"""Hold a basket of tokens at target weights, and put it back when it drifts.

On the first fire, with SEED_USD set, it buys the basket at its target
weights. On every fire after that it values the basket from the owner's own
holdings, and when any leg's weight is more than BAND_PCT points from target
it sells what has run ahead into USDC and buys what has lagged with the
proceeds.

The index is the owner's WHOLE holding of each leg's exact contract on its
chain. There is no separate ledger: a token the owner already held, or buys by
hand later, is part of the index and gets rebalanced with it.

Sells go first. The buys wait until those sells have settled, so a buy is
never funded by USDC that has not arrived yet: within the same fire if the
sells execute quickly, otherwise on the next fire. While any trade this duty
filed is still in flight (executing, or waiting on the owner's approval), the
duty files nothing new.

Settings: LEGS (SYMBOL, ADDRESS, CHAIN_ID, WEIGHT), SEED_USD, BAND_PCT,
MIN_TRADE_USD, MAX_REBALANCE_USD.
"""

import bevo
import json
import math
import os
import re
import subprocess
import time

PARAMS = json.loads(os.environ.get("PARAMS", "{}"))

LEGS_RAW = PARAMS.get("LEGS") or []
SEED_USD = float(PARAMS.get("SEED_USD") or 0)
BAND_PCT = float(PARAMS.get("BAND_PCT") or 5)
MIN_TRADE_USD = max(float(PARAMS.get("MIN_TRADE_USD") or 10), 2.0)
MAX_REBALANCE_USD = float(PARAMS.get("MAX_REBALANCE_USD") or 2000)

NAME = os.environ.get("BEVO_SERVICE_NAME") or "index"

#: The swap route's own minimum.
SPOT_MIN_USD = 2.0

#: Buys are sized to what the sells should return, less this, so slippage and
#: fees on the sell side never leave a buy short of cash.
PROCEEDS_HAIRCUT = 0.02

#: How long one fire waits for its sells to settle before it leaves the buys
#: for the next fire.
SETTLE_WAIT_SECONDS = 150
SETTLE_POLL_SECONDS = 10

#: A trade still in flight after this long stops blocking the duty: it is
#: logged and forgotten, and the next valuation reads whatever it did.
PENDING_TIMEOUT_SECONDS = 24 * 3600

#: exec_status states after which a key no longer blocks anything. `unknown`
#: means the ledger never saw the key, so nothing is in flight under it.
SETTLED_STATES = {
    "executed", "failed", "refused", "rejected", "expired", "cancelled",
    "canceled", "declined", "replay", "unknown",
}

EVM_ADDRESS = re.compile(r"^0x[0-9a-fA-F]{40}$")
SOLANA_ADDRESS = re.compile(r"^[1-9A-HJ-NP-Za-km-z]{32,44}$")
SOLANA_CHAIN_ID = 1151111081099710
NATIVE_CHAINS = {
    "ETH": (1, 8453, 42161, 4663),
    "BNB": (56,),
    "SOL": (SOLANA_CHAIN_ID,),
}


# --- small helpers -------------------------------------------------------------------------


def fmt(number):
    """Trim a float to something the CLI parses and a human can read."""
    return ("%.8f" % float(number)).rstrip("0").rstrip(".")


def usd(number):
    return "$%s" % format(round(float(number), 2), ",.2f")


def say(text):
    """`bevo.log()` on one line: an echoed error must not forge a log line."""
    bevo.log(" ".join(str(text).split()))


def now_ts():
    return time.time()


def slot_key(slot):
    """The slot in the grammar an idempotency key allows."""
    return str(slot).replace("@", "-").replace("/", "-")


def answer_of(text):
    """The JSON `acp` printed, or None. None is NOT a refusal."""
    text = (text or "").strip()
    if not text:
        return None
    try:
        value = json.loads(text)
    except ValueError:
        start = text.find("{")
        if start < 0:
            return None
        try:
            value, _ = json.JSONDecoder().raw_decode(text, start)
        except ValueError:
            return None
    return value if isinstance(value, dict) else None


# --- the basket ----------------------------------------------------------------------------


class Leg:
    """One token of the index: an exact contract on a chain, or a chain's own coin."""

    def __init__(self, index, symbol, address, chain_id, weight):
        self.index = index
        self.symbol = symbol
        self.address = address
        self.chain_id = chain_id
        self.weight = weight

    @property
    def ref(self):
        """What names the token on the wire: the contract, or the native ticker."""
        return self.address or self.symbol

    def label(self):
        return self.symbol

    def matches(self, row):
        """Whether one `spot.tokens` row is this leg."""
        try:
            chain = int(row.get("chainId"))
        except (TypeError, ValueError):
            return False
        if chain != self.chain_id:
            return False
        held = str(row.get("tokenAddress") or "").strip()
        if self.address:
            if EVM_ADDRESS.match(self.address):
                return held.lower() == self.address
            return held == self.address
        # A chain's own coin: matched by ticker on its chain, never by a
        # contract, since a contract row with the same ticker is a bridged token.
        symbol = str(row.get("symbol") or "").strip().upper()
        if symbol != self.symbol:
            return False
        return not EVM_ADDRESS.match(held) or held.lower().startswith("0xeeee")


def parse_legs(raw):
    """The settings as Leg objects, or (None, why not). Nothing loose is accepted."""
    if not isinstance(raw, list) or not 2 <= len(raw) <= 15:
        return None, "LEGS must hold 2 to 15 tokens"
    legs, seen, total = [], set(), 0.0
    for i, item in enumerate(raw):
        if not isinstance(item, dict):
            return None, "leg %d is not a token" % (i + 1)
        symbol = str(item.get("SYMBOL") or "").strip().lstrip("$").upper()
        address = str(item.get("ADDRESS") or "").strip()
        chain = item.get("CHAIN_ID")
        try:
            weight = float(item.get("WEIGHT"))
        except (TypeError, ValueError):
            return None, "leg %s has no WEIGHT" % (symbol or i + 1)
        if not symbol:
            return None, "leg %d has no SYMBOL" % (i + 1)
        if not isinstance(chain, int):
            return None, "%s has no CHAIN_ID" % symbol
        if address:
            if SOLANA_ADDRESS.match(address) and not EVM_ADDRESS.match(address):
                if chain != SOLANA_CHAIN_ID:
                    return None, "%s is a Solana mint, but CHAIN_ID is %s" % (symbol, chain)
            elif EVM_ADDRESS.match(address):
                if chain == SOLANA_CHAIN_ID:
                    return None, "%s has an EVM address but CHAIN_ID is Solana" % symbol
                address = address.lower()
            else:
                return None, "%s: ADDRESS is not a contract address" % symbol
        else:
            chains = NATIVE_CHAINS.get(symbol)
            if chains is None:
                return None, "%s is a ticker with no ADDRESS; pin its contract" % symbol
            if chain not in chains:
                return None, "%s is not the own coin of chain %s" % (symbol, chain)
        ident = (address or symbol, chain)
        if ident in seen:
            return None, "%s appears twice" % symbol
        seen.add(ident)
        total += weight
        legs.append(Leg(i, symbol, address or None, chain, weight))
    if abs(total - 100.0) > 0.5:
        return None, "the weights add up to %s%%, not 100%%" % fmt(total)
    # Normalise away rounding so targets sum to exactly 1.
    for leg in legs:
        leg.weight = leg.weight / total
    return legs, None


# --- reading the book ----------------------------------------------------------------------


def read_book(legs):
    """Each leg's (amount, price, usd) from the owner's holdings, or (None, why not).

    A failed read is never a zero balance: valuing the index off one would sell
    every other leg to buy the 'missing' one.
    """
    try:
        body = bevo.read("/user-assets", {"fresh": 1})
    except bevo.BevoError as exc:
        return None, "the portfolio could not be read (%s)" % exc
    spot = (body or {}).get("spot") or {}
    if spot.get("available") is not True:
        return None, "the portfolio is unavailable right now"
    rows = spot.get("tokens") or []
    book = {}
    for leg in legs:
        amount, value, price = 0.0, 0.0, None
        for row in rows:
            if not leg.matches(row):
                continue
            try:
                a = float(row.get("balance") or 0)
                v = float(row.get("usdValueUsd") or 0)
            except (TypeError, ValueError):
                continue
            amount += a
            value += v
            p = row.get("usdPrice")
            if p is not None:
                try:
                    price = float(p)
                except (TypeError, ValueError):
                    pass
        if amount > 0 and not price:
            return None, "%s has no price right now" % leg.label()
        book[leg.index] = {"amount": amount, "usd": value, "price": price}
    return book, None


def cash_usd():
    """Spendable USDC, or None when unreadable."""
    try:
        b = bevo.balance()
    except bevo.BevoError:
        return None
    if not b or b.cash_usd is None:
        return None
    return float(b.cash_usd)


# --- trading -------------------------------------------------------------------------------


def buy_args(leg, size):
    args = ["--token-in", "usdc", "--amount-in", fmt(size)]
    return args + ["--token-out", leg.ref, "--chain-out", str(leg.chain_id)]


def sell_args(leg, amount):
    args = ["--token-in", leg.ref, "--chain-in", str(leg.chain_id)]
    return args + ["--amount-in", fmt(amount), "--token-out", "usdc"]


def filed(args, key, sentence):
    """Run one `acp trade` and read what it answered. Returns (status, summary).

    status is "done", "pending" (accepted or waiting on approval), "refused",
    or "unknown". Unknown is never retried with a new key.
    """
    done = subprocess.run(
        ["acp", "trade", *args, "--idempotency-key", key],
        capture_output=True,
        text=True,
        timeout=180,
        check=False,
    )
    answer = answer_of(done.stdout)
    if answer is None:
        state = (bevo.exec_status(key) or {}).get("state")
        return "unknown", "%s: outcome UNKNOWN (exec_status: %s)" % (sentence, state)
    status = str(answer.get("status") or "").lower()
    if answer.get("executed") or status == "executed":
        return "done", "%s: executed" % sentence
    if answer.get("asked") or status in ("asked", "awaiting_approval", "pending_approval"):
        return "pending", "%s: waiting for your approval" % sentence
    if answer.get("ok") or status in ("accepted", "executing", "pending", "replay"):
        return "pending", "%s: accepted, executing" % sentence
    if answer.get("unrecognized"):
        return "unknown", "%s: unrecognised answer %r" % (sentence, answer.get("status"))
    return "refused", "%s: refused (%s)" % (sentence, answer.get("error") or answer.get("status"))


def track(key):
    pending = bevo.state.get("pending") or {}
    pending[key] = now_ts()
    bevo.state["pending"] = pending


def still_pending():
    """Keys this duty filed that have not settled yet. Settled and stale ones are dropped."""
    pending = dict(bevo.state.get("pending") or {})
    live = {}
    for key, filed_at in pending.items():
        state = str((bevo.exec_status(key) or {}).get("state") or "unknown").lower()
        if state in SETTLED_STATES:
            continue
        if now_ts() - float(filed_at or 0) > PENDING_TIMEOUT_SECONDS:
            say("stopped waiting on %s (state %s after 24h)" % (key, state))
            continue
        live[key] = filed_at
    bevo.state["pending"] = live
    return live


def wait_for(keys):
    """Wait a short while for these keys to settle. True when all have."""
    for attempt in range(SETTLE_WAIT_SECONDS // SETTLE_POLL_SECONDS + 1):
        if attempt:
            bevo.sleep(SETTLE_POLL_SECONDS)
        live = still_pending()
        if not any(k in live for k in keys):
            return True
    return False


def file_buys(legs, buys, slot, notes):
    """File the queued buys, scaled to the cash actually there."""
    by_index = {leg.index: leg for leg in legs}
    wanted = sum(size for _, size in buys)
    cash = cash_usd()
    scale = 1.0
    if cash is not None and wanted > 0 and cash < wanted:
        scale = max(cash, 0.0) / wanted
    for index, size in buys:
        leg = by_index.get(index)
        if leg is None:
            continue
        size = math.floor(size * scale * 100) / 100
        if size < SPOT_MIN_USD:
            notes.append("Buy %s skipped: %s is under the minimum" % (leg.label(), usd(size)))
            continue
        key = "index:%s:%s:buy:%d" % (bevo.SERVICE_ID, slot_key(slot), index)
        status, summary = filed(buy_args(leg, size), key, "Buy %s of %s" % (usd(size), leg.label()))
        if status in ("pending", "unknown"):
            track(key)
        notes.append(summary)


# --- one fire ------------------------------------------------------------------------------


def seed(legs):
    """Buy the starting basket at its target weights, once."""
    notes = []
    for leg in legs:
        size = math.floor(SEED_USD * leg.weight * 100) / 100
        if size < SPOT_MIN_USD:
            notes.append("%s skipped: %s is under the %s minimum" % (leg.label(), usd(size), usd(SPOT_MIN_USD)))
            continue
        key = "index:%s:seed:%d" % (bevo.SERVICE_ID, leg.index)
        status, summary = filed(buy_args(leg, size), key, "Buy %s of %s" % (usd(size), leg.label()))
        if status in ("pending", "unknown"):
            track(key)
        notes.append(summary)
    bevo.state["seeded"] = True
    bevo.status("seeded")
    bevo.notify(("%s: starting basket (%s): %s" % (NAME, usd(SEED_USD), "; ".join(notes)))[:500])


def plan(legs, book):
    """The sells and buys that bring the basket back to target, or None inside the band."""
    total = sum(book[leg.index]["usd"] for leg in legs)
    if total < MIN_TRADE_USD * 2:
        return None, total, 0.0
    drift = max(abs(book[leg.index]["usd"] / total - leg.weight) * 100 for leg in legs)
    if drift < BAND_PCT:
        return None, total, drift

    sells, buys = [], []
    for leg in legs:
        gap = leg.weight * total - book[leg.index]["usd"]
        if abs(gap) < MIN_TRADE_USD:
            continue
        (buys if gap > 0 else sells).append([leg, abs(gap)])

    sell_total = sum(size for _, size in sells)
    if sell_total > MAX_REBALANCE_USD:
        factor = MAX_REBALANCE_USD / sell_total
        sells = [[leg, size * factor] for leg, size in sells]
        sell_total = MAX_REBALANCE_USD
    # Buys are funded only by what the sells return.
    budget = sell_total * (1 - PROCEEDS_HAIRCUT)
    buy_total = sum(size for _, size in buys)
    if buy_total > budget and buy_total > 0:
        factor = budget / buy_total
        buys = [[leg, size * factor] for leg, size in buys]
    return {"sells": sells, "buys": buys}, total, drift


def rebalance(legs, book, slot):
    moves, total, drift = plan(legs, book)
    if moves is None:
        if total < MIN_TRADE_USD * 2:
            say("%s: the index holds %s, too little to rebalance" % (slot, usd(total)))
            bevo.status("small")
        else:
            say("%s: max drift %.1f pts, inside the %s-pt band" % (slot, drift, fmt(BAND_PCT)))
            bevo.status("balanced", drift=round(drift, 1))
        return
    if not moves["sells"]:
        say("%s: drift %.1f pts but no leg is far enough over to sell" % (slot, drift))
        bevo.status("balanced", drift=round(drift, 1))
        return

    notes = ["drift %.1f pts on %s" % (drift, usd(total))]
    sell_keys = []
    sold_usd = 0.0
    for leg, size in moves["sells"]:
        held = book[leg.index]
        # Capped at what is held and floored: rounding up sells what is not there.
        amount = math.floor(min(size / held["price"], held["amount"]) * 1e8) / 1e8
        if amount <= 0:
            continue
        key = "index:%s:%s:sell:%d" % (bevo.SERVICE_ID, slot_key(slot), leg.index)
        status, summary = filed(sell_args(leg, amount), key, "Sell %s of %s" % (usd(size), leg.label()))
        if status in ("pending", "unknown"):
            track(key)
            sell_keys.append(key)
        if status != "refused":
            sold_usd += amount * held["price"]
        notes.append(summary)

    # Buys are funded only by sells that went through: a refused sell must not
    # turn into a buy paid for with the owner's other cash.
    planned = sum(size for _, size in moves["buys"])
    budget = sold_usd * (1 - PROCEEDS_HAIRCUT)
    factor = min(1.0, budget / planned) if planned > 0 else 0.0
    buys = [(leg.index, size * factor) for leg, size in moves["buys"] if size * factor >= SPOT_MIN_USD]
    if moves["buys"] and not buys:
        notes.append("no buys: no sell went through")
    if buys and (not sell_keys or wait_for(sell_keys)):
        file_buys(legs, buys, slot, notes)
    elif buys:
        bevo.state["queued"] = {"slot": slot, "buys": buys}
        notes.append("buys queued until the sells settle")
    if bevo.state.get("queued"):
        bevo.status("queued")
    else:
        bevo.status("rebalanced")
    bevo.notify(("%s: rebalanced. %s" % (NAME, "; ".join(notes)))[:500])


def fire(legs, tick):
    slot = tick.slot
    if slot is None:
        say("skipped: the fire carried no time, so there is no slot to key on")
        bevo.status("skipped")
        return
    if still_pending():
        say("%s: waiting on %d trade(s) still in flight" % (slot, len(bevo.state.get("pending") or {})))
        bevo.status("settling")
        return

    queued = bevo.state.get("queued")
    if queued:
        notes = []
        file_buys(legs, [tuple(b) for b in queued.get("buys") or []], queued.get("slot") or slot, notes)
        bevo.state.pop("queued", None)
        bevo.status("rebalanced")
        bevo.notify(("%s: sells settled, buys filed: %s" % (NAME, "; ".join(notes)))[:500], quiet=True)
        return

    if SEED_USD > 0 and not bevo.state.get("seeded"):
        seed(legs)
        return

    book, why = read_book(legs)
    if book is None:
        say("%s: skipped, %s" % (slot, why))
        bevo.status("skipped")
        return
    rebalance(legs, book, slot)


LEGS, PROBLEM = parse_legs(LEGS_RAW)
if PROBLEM:
    bevo.notify("%s does nothing until its basket is fixed: %s." % (NAME, PROBLEM))
    bevo.status("paused")

# The owner's Duties row: recipe.json `status` words each state.
for tick in bevo.ticks():
    if PROBLEM:
        say("skipped: %s" % PROBLEM)
        bevo.status("paused")
        continue
    fire(LEGS, tick)
