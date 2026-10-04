import yfinance as yf
import asyncio
import websockets
import requests
import pandas as pd
import time, msvcrt, threading, json, os
from datetime import datetime, timedelta
from concurrent.futures import ThreadPoolExecutor
from http.server import HTTPServer, BaseHTTPRequestHandler
from rich.live import Live
from rich.layout import Layout
from rich.text import Text
from rich.table import Table
from rich import box
from rich.console import Console
from io import StringIO


# ─────────────────────────────────────────────────────────────
#  CRYPTO CONFIG
# ─────────────────────────────────────────────────────────────
COIN = {
    "BTC-USD" : "btcusdt",
    "ETH-USD" : "ethusdt",
    "SOL-USD" : "solusdt",
    "BNB-USD" : "bnbusdt",
    "ADA-USD" : "adausdt",
    "DOGE-USD": "dogeusdt",
}

STARTING_BALANCE  = 6500.0          # ← changed from 1000
RESERVE_PCT       = 0.10            # ← keep only 10% cash
DEPLOY_PCT        = 1.0 - RESERVE_PCT  # 90% always invested
RISK_PER_TRADE    = 0.1            # ← raised from 0.015 (4% risk per trade)
ATR_SL            = 1.5             # ← tighter stop (was 2.0)
ATR_TP1           = 2.0             # ← was 2.5
ATR_TP2           = 4.0             # ← was 5.0
ATR_TRAIL         = 1.2             # ← was 1.8
MAX_ALLOC         = 0.50            # ← was 0.35, allow 50% in one coin
MIN_SCORE_TREND   = 3               # ← was 4, easier trigger
MIN_SCORE_RANGE   = 3               # ← was 4
COOLDOWN_CYCLES   = 2               # ← was 4, faster re-entry
SIGNAL_EVERY      = 10              # ← was 15s, check more often
OHLCV_EVERY       = 60
SAVE_FILE         = "bot_state.json"
KEY_MAP           = {str(i + 1): c for i, c in enumerate(COIN)}

states = {
    coin: {
        "position"    : None,
        "prev_price"  : None,
        "status"      : "loading...",
        "score"       : 0,
        "cooldown"    : 0,
        "chart_prices": [],
    }
    for coin in COIN
}

coin_data       = {c: None for c in COIN}
coin_indicators = {c: None for c in COIN}
last_prices     = {c: None for c in COIN}
balance         = STARTING_BALANCE
trades          = []
manual_close    = {}
data_lock       = threading.Lock()

# ─────────────────────────────────────────────────────────────
#  US STOCK CONFIG
# ─────────────────────────────────────────────────────────────
STOCKS = {
    "NVDA" : "nvidia",
    "TSLA" : "tesla",
    "AAPL" : "apple",
    "MSFT" : "microsoft",
    "AMZN" : "amazon",
    "META" : "meta",
    "AMD"  : "amd",
    "PLTR" : "palantir",
    "NFLX" : "netflix",
    "COIN" : "coinbase",
}

STOCK_BALANCE      = 6500.0         # ← changed from 10000
STOCK_ATR_SL       = 1.5            # ← tighter
STOCK_ATR_TP1      = 2.0
STOCK_ATR_TP2      = 4.0
STOCK_ATR_TRAIL    = 1.2
STOCK_MAX_ALLOC    = 0.50           # ← was 0.30
STOCK_RISK         = 0.04           # ← was 0.015
STOCK_COOLDOWN     = 2              # ← was 4
STOCK_SIGNAL_EVERY = 10             # ← was 15
STOCK_OHLCV_EVERY  = 60
STOCK_SAVE_FILE    = "stock_state.json"

stock_states = {
    ticker: {
        "position"    : None,
        "prev_price"  : None,
        "status"      : "loading...",
        "score"       : 0,
        "cooldown"    : 0,
        "chart_prices": [],
    }
    for ticker in STOCKS
}

stock_data       = {t: None for t in STOCKS}
stock_indicators = {t: None for t in STOCKS}
stock_prices     = {t: None for t in STOCKS}
stock_balance    = STOCK_BALANCE
stock_trades     = []
stock_data_lock  = threading.Lock()


# ─────────────────────────────────────────────────────────────
#  SHARED: INDICATORS + SIGNAL  (ENHANCED v3)
# ─────────────────────────────────────────────────────────────
def compute_indicators(df):
    if df is None or df.empty:
        return None

    try:
        c = df["Close"].squeeze()
        h = df["High"].squeeze()
        l = df["Low"].squeeze()
        v = df["Volume"].squeeze()

        if len(c) < 50:
            return None

        # ── EMAs ──────────────────────────────────────────────
        e9  = c.ewm(span=9,  adjust=False).mean()
        e21 = c.ewm(span=21, adjust=False).mean()
        e50 = c.ewm(span=50, adjust=False).mean()
        e200 = c.ewm(span=200, adjust=False).mean()  # NEW: trend filter

        # ── RSI ───────────────────────────────────────────────
        d_   = c.diff()
        g_   = d_.where(d_ > 0, 0).ewm(alpha=1/14, adjust=False).mean()
        ls_  = (-d_.where(d_ < 0, 0)).ewm(alpha=1/14, adjust=False).mean()
        rsi_s = 100 - 100 / (1 + g_ / (ls_ + 1e-10))

        # ── Stochastic RSI ────────────────────────────────────
        rsi_min = rsi_s.rolling(14).min()
        rsi_max = rsi_s.rolling(14).max()
        stoch   = (rsi_s - rsi_min) / (rsi_max - rsi_min + 1e-10)
        stoch_k = stoch.rolling(3).mean()
        stoch_d = stoch_k.rolling(3).mean()

        # ── MACD ──────────────────────────────────────────────
        macd     = c.ewm(span=12, adjust=False).mean() - c.ewm(span=26, adjust=False).mean()
        macd_sig = macd.ewm(span=9, adjust=False).mean()
        macd_h   = macd - macd_sig

        # ── Bollinger Bands ───────────────────────────────────
        bb_mid = c.rolling(20).mean()
        bb_std = c.rolling(20).std()
        bb_pct = (c - (bb_mid - 2 * bb_std)) / (4 * bb_std + 1e-10)
        bb_width = (4 * bb_std) / (bb_mid + 1e-10)   # NEW: squeeze detector

        # ── ATR ───────────────────────────────────────────────
        tr  = pd.concat([(h - l), (h - c.shift()).abs(), (l - c.shift()).abs()], axis=1).max(axis=1)
        atr = tr.ewm(span=14, adjust=False).mean()

        # ── Trend / Volume / Momentum ─────────────────────────
        trend_str = (e9 - e50).abs() / (atr + 1e-10)
        vol_ratio = v / (v.rolling(20).mean() + 1e-10)
        roc5      = (c - c.shift(5))  / (c.shift(5)  + 1e-10) * 100
        roc10     = (c - c.shift(10)) / (c.shift(10) + 1e-10) * 100  # NEW: 10-bar momentum

        # ── NEW: Volume Weighted Price ─────────────────────────
        vwap = (c * v).rolling(20).sum() / (v.rolling(20).sum() + 1e-10)

        # ── NEW: Keltner Channel (breakout detection) ─────────
        kc_mid   = e21
        kc_upper = kc_mid + 2.0 * atr
        kc_lower = kc_mid - 2.0 * atr

        # ── NEW: Chaikin Money Flow ───────────────────────────
        mfm = ((c - l) - (h - c)) / (h - l + 1e-10)
        mfv = mfm * v
        cmf = mfv.rolling(20).sum() / (v.rolling(20).sum() + 1e-10)

        # ── NEW: ADX (trend strength) ─────────────────────────
        plus_dm  = (h.diff()).where(h.diff() > (-l).diff(), 0).clip(lower=0)
        minus_dm = (-l.diff()).where((-l.diff()) > h.diff(), 0).clip(lower=0)
        atr14    = atr
        plus_di  = 100 * plus_dm.ewm(span=14, adjust=False).mean()  / (atr14 + 1e-10)
        minus_di = 100 * minus_dm.ewm(span=14, adjust=False).mean() / (atr14 + 1e-10)
        dx       = (abs(plus_di - minus_di) / (plus_di + minus_di + 1e-10)) * 100
        adx      = dx.ewm(span=14, adjust=False).mean()

        # ── NEW: Supertrend (simplified) ─────────────────────
        basic_upper = (h + l) / 2 + 3 * atr
        basic_lower = (h + l) / 2 - 3 * atr
        # simplified: price vs midpoint ± ATR
        supertrend_bull = c.iloc[-2] > ((h + l) / 2).iloc[-2]

        vals = {
            "price"       : float(c.iloc[-2]),
            "e9"          : float(e9.iloc[-2]),
            "e21"         : float(e21.iloc[-2]),
            "e50"         : float(e50.iloc[-2]),
            "e200"        : float(e200.iloc[-2]),
            "rsi"         : float(rsi_s.iloc[-2]),
            "stoch_k"     : float(stoch_k.iloc[-2]),
            "stoch_d"     : float(stoch_d.iloc[-2]),
            "macd_h"      : float(macd_h.iloc[-2]),
            "macd_h_p"    : float(macd_h.iloc[-3]),
            "bb_pct"      : float(bb_pct.iloc[-2]),
            "bb_width"    : float(bb_width.iloc[-2]),
            "atr"         : float(atr.iloc[-2]),
            "trend_str"   : float(trend_str.iloc[-2]),
            "vol_ratio"   : float(vol_ratio.iloc[-2]),
            "roc5"        : float(roc5.iloc[-2]),
            "roc10"       : float(roc10.iloc[-2]),
            "vwap"        : float(vwap.iloc[-2]),
            "cmf"         : float(cmf.iloc[-2]),
            "adx"         : float(adx.iloc[-2]),
            "plus_di"     : float(plus_di.iloc[-2]),
            "minus_di"    : float(minus_di.iloc[-2]),
            "kc_upper"    : float(kc_upper.iloc[-2]),
            "kc_lower"    : float(kc_lower.iloc[-2]),
            "supertrend_bull": bool(supertrend_bull),
        }

        if any(pd.isna(v) for v in vals.values() if not isinstance(v, bool)):
            return None
        return vals
    except Exception:
        return None


def compute_signal(ind):
    """
    Enhanced signal engine with 6 strategy layers:
      1. EMA trend alignment (original)
      2. RSI + Stochastic RSI (original + improved)
      3. MACD momentum (original)
      4. Bollinger Band position (original)
      5. NEW: ADX + DI directional strength
      6. NEW: CMF volume-backed money flow
      7. NEW: VWAP relationship (institutional level)
      8. NEW: Supertrend + Keltner breakout
      9. NEW: Dual momentum (ROC5 + ROC10)
    Max possible score = 14 (was 8)
    """
    if ind is None:
        return None, 0

    price = ind["price"]
    e9, e21, e50, e200 = ind["e9"], ind["e21"], ind["e50"], ind["e200"]
    rsi          = ind["rsi"]
    sk, sd       = ind["stoch_k"], ind["stoch_d"]
    mh, mhp      = ind["macd_h"], ind["macd_h_p"]
    bbp          = ind["bb_pct"]
    vr           = ind["vol_ratio"]
    ts           = ind["trend_str"]
    roc5         = ind["roc5"]
    roc10        = ind["roc10"]
    vwap         = ind["vwap"]
    cmf          = ind["cmf"]
    adx          = ind["adx"]
    plus_di      = ind["plus_di"]
    minus_di     = ind["minus_di"]
    kc_upper     = ind["kc_upper"]
    kc_lower     = ind["kc_lower"]
    sup_bull     = ind["supertrend_bull"]

    long_pts = 0
    short_pts = 0

    # ── 1. EMA alignment (max 3) ─────────────────────────────
    if e9 > e21 > e50:    long_pts  += 3
    elif e9 > e21:         long_pts  += 1
    if e9 < e21 < e50:    short_pts += 3
    elif e9 < e21:         short_pts += 1

    # ── 2. RSI (max 2) ────────────────────────────────────────
    if rsi < 32:            long_pts  += 2
    elif rsi < 48:          long_pts  += 1
    if rsi > 68:            short_pts += 2
    elif rsi > 52:          short_pts += 1

    # ── 3. MACD histogram (max 2) ────────────────────────────
    if mh > 0 and mh > mhp:  long_pts  += 2
    elif mh > mhp:            long_pts  += 1
    if mh < 0 and mh < mhp:  short_pts += 2
    elif mh < mhp:            short_pts += 1

    # ── 4. Bollinger (max 1) ─────────────────────────────────
    if bbp < 0.20:    long_pts  += 1
    if bbp > 0.80:    short_pts += 1

    # ── 5. Stochastic RSI (max 1) ────────────────────────────
    if sk < 0.25 and sk > sd:  long_pts  += 1
    if sk > 0.75 and sk < sd:  short_pts += 1

    # ── 6. ADX directional (max 2) ───────────────────────────
    if adx > 25:
        if plus_di > minus_di:   long_pts  += 2
        elif minus_di > plus_di: short_pts += 2
    elif adx > 15:
        if plus_di > minus_di:   long_pts  += 1
        elif minus_di > plus_di: short_pts += 1

    # ── 7. Chaikin Money Flow (max 1) ────────────────────────
    if cmf > 0.10:    long_pts  += 1
    elif cmf < -0.10: short_pts += 1

    # ── 8. VWAP relationship (max 1) ─────────────────────────
    if price > vwap:  long_pts  += 1
    elif price < vwap: short_pts += 1

    # ── 9. Supertrend (max 1) ────────────────────────────────
    if sup_bull:      long_pts  += 1
    else:             short_pts += 1

    # ── 10. Dual momentum ROC (max 1) ────────────────────────
    if roc5 > 0 and roc10 > 0:    long_pts  += 1
    elif roc5 < 0 and roc10 < 0:  short_pts += 1

    # ── 11. E200 macro trend (max 1) ─────────────────────────
    if price > e200:   long_pts  += 1
    elif price < e200: short_pts += 1

    # ── Volume amplifier ──────────────────────────────────────
    if vr > 1.5:
        if long_pts >= short_pts:  long_pts  = min(long_pts  + 1, 14)
        else:                      short_pts = min(short_pts + 1, 14)

    # Dynamic min score: lower bar in strong trends
    if adx > 30:
        min_score = 4   # strong trend — fire earlier
    elif ts > 2.5:
        min_score = MIN_SCORE_TREND   # = 3
    else:
        min_score = MIN_SCORE_RANGE   # = 3

    if long_pts >= min_score and long_pts > short_pts:
        return "long", long_pts
    if short_pts >= min_score and short_pts > long_pts:
        return "short", short_pts
    return None, max(long_pts, short_pts)


# ─────────────────────────────────────────────────────────────
#  PERSISTENCE
# ─────────────────────────────────────────────────────────────
def save_state():
    with open(SAVE_FILE, "w") as f:
        json.dump({
            "balance"  : balance,
            "trades"   : trades,
            "positions": {c: states[c]["position"] for c in COIN if states[c]["position"]},
        }, f, indent=2)


def load_state():
    global balance, trades
    if not os.path.exists(SAVE_FILE):
        return
    with open(SAVE_FILE) as f:
        d = json.load(f)
    balance = d.get("balance", STARTING_BALANCE)
    trades  = d.get("trades", [])
    for c, pos in d.get("positions", {}).items():
        if c in states and pos:
            pos.setdefault("COIN_rem",    pos.get("COIN", 0))
            pos.setdefault("invested_rem", pos.get("invested", 0))
            pos.setdefault("trail_sl",     pos.get("sl", 0))
            pos.setdefault("tp1",          pos.get("entry", 0))
            pos.setdefault("tp2",          pos.get("entry", 0))
            pos.setdefault("atr",          0.001)
            pos.setdefault("partial_done", False)
            states[c]["position"] = pos
            col = "green" if pos["side"] == "long" else "red"
            states[c]["status"] = f"[{col}]resumed {pos['side']} @ ${pos['entry']:,.4f}[/{col}]"


def save_stock_state():
    with open(STOCK_SAVE_FILE, "w") as f:
        json.dump({
            "balance"  : stock_balance,
            "trades"   : stock_trades,
            "positions": {t: stock_states[t]["position"] for t in STOCKS if stock_states[t]["position"]},
        }, f, indent=2)


def load_stock_state():
    global stock_balance, stock_trades
    if not os.path.exists(STOCK_SAVE_FILE):
        return
    with open(STOCK_SAVE_FILE) as f:
        d = json.load(f)
    stock_balance = d.get("balance", STOCK_BALANCE)
    stock_trades  = d.get("trades", [])
    for t, pos in d.get("positions", {}).items():
        if t in stock_states and pos:
            pos.setdefault("COIN_rem",    pos.get("COIN", 0))
            pos.setdefault("invested_rem", pos.get("invested", 0))
            pos.setdefault("trail_sl",     pos.get("sl", 0))
            pos.setdefault("tp1",          pos.get("entry", 0))
            pos.setdefault("tp2",          pos.get("entry", 0))
            pos.setdefault("atr",          1.0)
            pos.setdefault("partial_done", False)
            stock_states[t]["position"] = pos
            col = "green" if pos["side"] == "long" else "red"
            stock_states[t]["status"] = f"[{col}]resumed {pos['side']} @ ${pos['entry']:,.2f}[/{col}]"


# ─────────────────────────────────────────────────────────────
#  KEYBOARD
# ─────────────────────────────────────────────────────────────
def keyboard_listener():
    while True:
        if msvcrt.kbhit():
            key = msvcrt.getch().decode("utf-8", errors="ignore")
            if key in KEY_MAP and states[KEY_MAP[key]]["position"]:
                manual_close[KEY_MAP[key]] = True
        time.sleep(0.05)


# ─────────────────────────────────────────────────────────────
#  CRYPTO FETCH
# ─────────────────────────────────────────────────────────────
def fetch_binance_ohlcv(coin):
    sym = COIN.get(coin, "").upper()
    if not sym:
        return coin, None, None
    try:
        r = requests.get(
            "https://api.binance.com/api/v3/klines",
            params={"symbol": sym, "interval": "1m", "limit": 300},
            timeout=10
        )
        raw = r.json()
        if not raw or isinstance(raw, dict):
            return coin, None, None
        df = pd.DataFrame(raw, columns=[
            'timestamp', 'Open', 'High', 'Low', 'Close', 'Volume',
            'close_time', 'quote_vol', 'trades', 'taker_base', 'taker_quote', 'ignore'
        ])
        for col in ['Open', 'High', 'Low', 'Close', 'Volume']:
            df[col] = df[col].astype(float)
        df.index = pd.to_datetime(df['timestamp'], unit='ms')
        return coin, df, float(df['Close'].iloc[-1])
    except Exception:
        return coin, None, None


def background_fetch():
    while True:
        with ThreadPoolExecutor(max_workers=6) as ex:
            results = list(ex.map(fetch_binance_ohlcv, COIN))
        with data_lock:
            for coin, df, price in results:
                if df is not None:
                    coin_data[coin]       = df
                    coin_indicators[coin] = compute_indicators(df)
        time.sleep(OHLCV_EVERY)


async def _binance_ws():
    streams = "/".join(f"{s}@miniTicker" for s in COIN.values())
    url     = f"wss://stream.binance.com:9443/stream?streams={streams}"
    while True:
        try:
            async with websockets.connect(url, ping_interval=20) as ws:
                async for raw in ws:
                    data  = json.loads(raw)
                    tick  = data.get("data", {})
                    sym   = tick.get("s", "").lower()
                    price = float(tick.get("c") or 0)
                    if price <= 0:
                        continue
                    for coin, bsym in COIN.items():
                        if bsym == sym:
                            last_prices[coin] = price
                            cp = states[coin]["chart_prices"]
                            cp.append(price)
                            if len(cp) > 120:
                                states[coin]["chart_prices"] = cp[-120:]
                            break
        except Exception:
            await asyncio.sleep(5)


def binance_ws_thread():
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    loop.run_until_complete(_binance_ws())
# ─────────────────────────────────────────────────────────────
#  STOCK FETCH
# ─────────────────────────────────────────────────────────────
def fetch_stock_ohlcv_single(ticker):
    try:
        time.sleep(0.15)
        df = yf.download(
            ticker,
            period="5d",
            interval="1m",
            progress=False,
            auto_adjust=True,
            threads=False,
            prepost=True,
        )
        if df is None or df.empty:
            return ticker, None, None
        return ticker, df, float(df["Close"].squeeze().iloc[-1])
    except Exception:
        return ticker, None, None


def stock_background_fetch():
    while True:
        with ThreadPoolExecutor(max_workers=10) as ex:
            results = list(ex.map(fetch_stock_ohlcv_single, STOCKS))
        with stock_data_lock:
            for ticker, df, price in results:
                if df is not None and price is not None:
                    stock_data[ticker]       = df
                    stock_prices[ticker]     = price
                    stock_indicators[ticker] = compute_indicators(df)
                    cp = stock_states[ticker]["chart_prices"]
                    cp.append(price)
                    if len(cp) > 120:
                        stock_states[ticker]["chart_prices"] = cp[-120:]
        time.sleep(STOCK_OHLCV_EVERY)


# ─────────────────────────────────────────────────────────────
#  CACHED PRICE REFRESHER
# ─────────────────────────────────────────────────────────────
def refresh_cached_prices():
    while True:
        with data_lock:
            for coin in COIN:
                df = coin_data.get(coin)
                if df is not None and not df.empty:
                    try:
                        last_prices[coin] = float(df["Close"].iloc[-1])
                    except Exception:
                        pass

        with stock_data_lock:
            for ticker in STOCKS:
                df = stock_data.get(ticker)
                if df is not None and not df.empty:
                    try:
                        stock_prices[ticker] = float(df["Close"].iloc[-1])
                    except Exception:
                        pass

        time.sleep(1)


# ─────────────────────────────────────────────────────────────
#  AUTOSAVE
# ─────────────────────────────────────────────────────────────
def autosave_loop():
    while True:
        try:
            save_state()
            save_stock_state()
        except Exception:
            pass
        time.sleep(300)


# ─────────────────────────────────────────────────────────────
#  CRYPTO POSITIONS
# ─────────────────────────────────────────────────────────────
def unrealised_pct(coin, price):
    pos = states[coin]["position"]
    if not pos or not price:
        return 0
    rem = pos["COIN_rem"]
    inv = pos["invested_rem"]
    if pos["side"] == "long":
        return (rem * price - inv) / (pos["invested"] + 1e-10) * 100
    return (inv - rem * price) / (pos["invested"] + 1e-10) * 100


def position_equity(coin, price):
    pos = states[coin]["position"]
    if not pos or not price:
        return 0
    if pos["side"] == "long":
        return pos["COIN_rem"] * price
    entry_value   = pos["COIN_rem"] * pos["entry"]
    current_value = pos["COIN_rem"] * price
    pnl           = entry_value - current_value
    return pos["invested_rem"] + pnl


def total_equity(prices=None):
    prices = prices or last_prices
    return balance + sum(position_equity(c, prices.get(c)) for c in COIN)


def _available_crypto():
    """Cash available to deploy — respects 10% reserve floor."""
    eq = total_equity()
    reserve = eq * RESERVE_PCT
    return max(0.0, balance - reserve)


def open_pos(coin, price, side, invest, atr):
    global balance
    if price <= 0:
        return
    invest = min(invest, _available_crypto())
    if invest < 1:
        return
    balance -= invest
    sl  = price - ATR_SL  * atr if side == "long" else price + ATR_SL  * atr
    tp1 = price + ATR_TP1 * atr if side == "long" else price - ATR_TP1 * atr
    tp2 = price + ATR_TP2 * atr if side == "long" else price - ATR_TP2 * atr
    states[coin]["position"] = {
        "side": side, "entry": price,
        "COIN": invest / price, "COIN_rem": invest / price,
        "invested": invest, "invested_rem": invest,
        "time": datetime.now().strftime("%H:%M:%S"),
        "sl": sl, "tp1": tp1, "tp2": tp2, "trail_sl": sl,
        "atr": atr, "partial_done": False,
    }
    col = "green" if side == "long" else "red"
    states[coin]["status"] = f"[{col}]{side} @ ${price:,.4f}[/{col}]"
    save_state()


def record_trade(coin, price, pnl, invested_portion, reason, partial=False):
    pct = (pnl / (invested_portion + 1e-10)) * 100
    pos = states[coin]["position"]
    trades.append({
        "timestamp": datetime.now().isoformat(),
        "time"     : datetime.now().strftime("%H:%M:%S"),
        "coin"     : COIN[coin],
        "side"     : pos["side"],
        "entry"    : pos["entry"],
        "exit"     : price,
        "pnl"      : pnl,
        "pct"      : pct,
        "reason"   : reason,
        "partial"  : partial,
    })


def close_pos(coin, price, reason):
    global balance
    pos = states[coin]["position"]
    rem = pos["COIN_rem"]
    inv = pos["invested_rem"]
    if pos["side"] == "long":
        pnl = rem * price - inv
        balance += rem * price
    else:
        pnl = inv - rem * price
        balance += inv + pnl
    record_trade(coin, price, pnl, inv, reason)
    pct  = (pnl / (pos["invested"] + 1e-10)) * 100
    sign = "+" if pnl >= 0 else ""
    col  = "green" if pnl >= 0 else "red"
    if reason == "stop loss":
        states[coin]["cooldown"] = COOLDOWN_CYCLES
    states[coin]["status"]   = f"[{col}]closed {sign}{pct:.3f}% [{reason}][/{col}]"
    states[coin]["position"] = None
    save_state()


def partial_close(coin, price):
    global balance
    pos     = states[coin]["position"]
    COIN_c = pos["COIN_rem"] * 0.5
    inv_c   = pos["invested_rem"] * 0.5
    if pos["side"] == "long":
        pnl = COIN_c * price - inv_c
        balance += COIN_c * price
    else:
        pnl = inv_c - COIN_c * price
        balance += inv_c + pnl
    record_trade(coin, price, pnl, inv_c, "partial tp", partial=True)
    pos["COIN_rem"]    -= COIN_c
    pos["invested_rem"] -= inv_c
    pos["partial_done"]  = True
    pos["trail_sl"]      = pos["entry"]
    save_state()


def update_trail(coin, price):
    pos = states[coin]["position"]
    if not pos:
        return
    atr = pos["atr"]
    if pos["side"] == "long":
        if price > pos["entry"] + atr:
            pos["trail_sl"] = max(pos["trail_sl"], price - ATR_TRAIL * atr)
    else:
        if price < pos["entry"] - atr:
            pos["trail_sl"] = min(pos["trail_sl"], price + ATR_TRAIL * atr)


def check_sl_tp():
    for coin in COIN:
        price = last_prices.get(coin)
        pos   = states[coin]["position"]
        if not price or not pos:
            continue
        update_trail(coin, price)
        if not pos["partial_done"]:
            if pos["side"] == "long"  and price >= pos["tp1"]: partial_close(coin, price)
            elif pos["side"] == "short" and price <= pos["tp1"]: partial_close(coin, price)
        sl = pos["trail_sl"]
        if pos["side"] == "long":
            if price <= sl:           close_pos(coin, price, "stop loss")
            elif price >= pos["tp2"]: close_pos(coin, price, "take profit")
        else:
            if price >= sl:           close_pos(coin, price, "stop loss")
            elif price <= pos["tp2"]: close_pos(coin, price, "take profit")


def check_signals():
    for coin in COIN:
        if states[coin]["cooldown"] > 0:
            states[coin]["cooldown"] -= 1

    signals, scores, atrs = {}, {}, {}
    with data_lock:
        for coin in COIN:
            ind = coin_indicators[coin]
            side, score = compute_signal(ind)
            signals[coin] = side
            scores[coin]  = score
            atrs[coin]    = ind["atr"] if ind else None

    total_score = sum(scores.values()) or 1
    weights     = {c: scores[c] / total_score for c in COIN}
    equity      = total_equity()

    for coin in COIN:
        price = last_prices.get(coin)
        pos   = states[coin]["position"]
        side  = signals[coin]
        score = scores[coin]
        atr   = atrs[coin]
        if not price or not atr:
            continue

        atr = max(atr, price * 0.002)

        states[coin]["score"] = score
        if states[coin]["cooldown"] > 0:
            cd = states[coin]["cooldown"]
            states[coin]["status"] = f"[dim]cooldown — {cd} cycles left[/dim]"
            continue
        with data_lock:
            n = len(coin_data[coin]) if coin_data[coin] is not None else 0
        if n < 50:
            states[coin]["status"] = f"[dim]loading ({n}/50 bars)[/dim]"
            continue

        # ── POSITION SIZING: risk-based, capped at 90% deployable ──
        risk_amount = equity * RISK_PER_TRADE * (score / 14)
        sl_dist     = ATR_SL * atr
        pos_usd     = risk_amount / (sl_dist / (price + 1e-10))

        # Ensure we deploy up to 90% of equity spread across active signals
        available   = _available_crypto()
        max_single  = equity * MAX_ALLOC * weights[coin]
        invest      = min(pos_usd, max_single, available)

        if pos is None:
            if side and invest > 1:
                open_pos(coin, price, side, invest, atr)
            else:
                states[coin]["status"] = f"[dim]waiting — score {score}/14[/dim]"
        elif side and side != pos["side"]:
            close_pos(coin, price, "signal flip")
            states[coin]["cooldown"] = 1
        else:
            pct  = unrealised_pct(coin, price)
            sign = "+" if pct >= 0 else ""
            col  = "green" if pct >= 0 else "red"
            states[coin]["status"] = f"[{col}]{pos['side']}  {sign}{pct:.3f}%  score {score}/14[/{col}]"


# ─────────────────────────────────────────────────────────────
#  STOCK POSITIONS
# ─────────────────────────────────────────────────────────────
def stock_unrealised_pct(ticker, price):
    pos = stock_states[ticker]["position"]
    if not pos or not price:
        return 0
    rem = pos["COIN_rem"]
    inv = pos["invested_rem"]
    if pos["side"] == "long":
        return (rem * price - inv) / (pos["invested"] + 1e-10) * 100
    return (inv - rem * price) / (pos["invested"] + 1e-10) * 100


def stock_position_equity(ticker, price):
    pos = stock_states[ticker]["position"]
    if not pos or not price:
        return 0
    if pos["side"] == "long":
        return pos["COIN_rem"] * price
    entry_value   = pos["COIN_rem"] * pos["entry"]
    current_value = pos["COIN_rem"] * price
    pnl           = entry_value - current_value
    return pos["invested_rem"] + pnl


def stock_total_equity():
    return stock_balance + sum(stock_position_equity(t, stock_prices.get(t)) for t in STOCKS)


def _available_stock():
    """Cash available to deploy — respects 10% reserve floor."""
    eq = stock_total_equity()
    reserve = eq * RESERVE_PCT
    return max(0.0, stock_balance - reserve)


def open_stock_pos(ticker, price, side, invest, atr):
    global stock_balance
    if price <= 0:
        return
    invest = min(invest, _available_stock())
    if invest < 1:
        return
    stock_balance -= invest
    sl  = price - STOCK_ATR_SL  * atr if side == "long" else price + STOCK_ATR_SL  * atr
    tp1 = price + STOCK_ATR_TP1 * atr if side == "long" else price - STOCK_ATR_TP1 * atr
    tp2 = price + STOCK_ATR_TP2 * atr if side == "long" else price - STOCK_ATR_TP2 * atr
    stock_states[ticker]["position"] = {
        "side": side, "entry": price,
        "COIN": invest / price, "COIN_rem": invest / price,
        "invested": invest, "invested_rem": invest,
        "time": datetime.now().strftime("%H:%M:%S"),
        "sl": sl, "tp1": tp1, "tp2": tp2, "trail_sl": sl,
        "atr": atr, "partial_done": False,
    }
    col = "green" if side == "long" else "red"
    stock_states[ticker]["status"] = f"[{col}]{side} @ ${price:,.2f}[/{col}]"
    save_stock_state()


def record_stock_trade(ticker, price, pnl, invested_portion, reason, partial=False):
    pct = (pnl / (invested_portion + 1e-10)) * 100
    pos = stock_states[ticker]["position"]
    stock_trades.append({
        "timestamp": datetime.now().isoformat(),
        "time"     : datetime.now().strftime("%H:%M:%S"),
        "ticker"   : STOCKS[ticker],
        "side"     : pos["side"],
        "entry"    : pos["entry"],
        "exit"     : price,
        "pnl"      : pnl,
        "pct"      : pct,
        "reason"   : reason,
        "partial"  : partial,
    })


def close_stock_pos(ticker, price, reason):
    global stock_balance
    pos = stock_states[ticker]["position"]
    rem = pos["COIN_rem"]
    inv = pos["invested_rem"]
    if pos["side"] == "long":
        pnl = rem * price - inv
        stock_balance += rem * price
    else:
        pnl = inv - rem * price
        stock_balance += inv + pnl
    record_stock_trade(ticker, price, pnl, inv, reason)
    pct  = (pnl / (pos["invested"] + 1e-10)) * 100
    sign = "+" if pnl >= 0 else ""
    col  = "green" if pnl >= 0 else "red"
    if reason == "stop loss":
        stock_states[ticker]["cooldown"] = STOCK_COOLDOWN
    stock_states[ticker]["status"]   = f"[{col}]closed {sign}{pct:.3f}% [{reason}][/{col}]"
    stock_states[ticker]["position"] = None
    save_stock_state()


def partial_close_stock(ticker, price):
    global stock_balance
    pos     = stock_states[ticker]["position"]
    COIN_c = pos["COIN_rem"] * 0.5
    inv_c   = pos["invested_rem"] * 0.5
    if pos["side"] == "long":
        pnl = COIN_c * price - inv_c
        stock_balance += COIN_c * price
    else:
        pnl = inv_c - COIN_c * price
        stock_balance += inv_c + pnl
    record_stock_trade(ticker, price, pnl, inv_c, "partial tp", partial=True)
    pos["COIN_rem"]    -= COIN_c
    pos["invested_rem"] -= inv_c
    pos["partial_done"]  = True
    pos["trail_sl"]      = pos["entry"]
    save_stock_state()


def update_stock_trail(ticker, price):
    pos = stock_states[ticker]["position"]
    if not pos:
        return
    atr = pos["atr"]
    if pos["side"] == "long":
        if price > pos["entry"] + atr:
            pos["trail_sl"] = max(pos["trail_sl"], price - STOCK_ATR_TRAIL * atr)
    else:
        if price < pos["entry"] - atr:
            pos["trail_sl"] = min(pos["trail_sl"], price + STOCK_ATR_TRAIL * atr)


def check_stock_sl_tp():
    for ticker in STOCKS:
        price = stock_prices.get(ticker)
        pos   = stock_states[ticker]["position"]
        if not price or not pos:
            continue
        update_stock_trail(ticker, price)
        if not pos["partial_done"]:
            if pos["side"] == "long"  and price >= pos["tp1"]: partial_close_stock(ticker, price)
            elif pos["side"] == "short" and price <= pos["tp1"]: partial_close_stock(ticker, price)
        sl = pos["trail_sl"]
        if pos["side"] == "long":
            if price <= sl:           close_stock_pos(ticker, price, "stop loss")
            elif price >= pos["tp2"]: close_stock_pos(ticker, price, "take profit")
        else:
            if price >= sl:           close_stock_pos(ticker, price, "stop loss")
            elif price <= pos["tp2"]: close_stock_pos(ticker, price, "take profit")


def check_stock_signals():
    session = market_session()
    if session == "closed":
        return

    for ticker in STOCKS:
        if stock_states[ticker]["cooldown"] > 0:
            stock_states[ticker]["cooldown"] -= 1

    signals, scores, atrs = {}, {}, {}
    with stock_data_lock:
        for ticker in STOCKS:
            ind = stock_indicators[ticker]
            side, score = compute_signal(ind)
            signals[ticker] = side
            scores[ticker]  = score
            atrs[ticker]    = ind["atr"] if ind else None

    total_score = sum(scores.values()) or 1
    weights     = {t: scores[t] / total_score for t in STOCKS}
    equity      = stock_total_equity()

    for ticker in STOCKS:
        price = stock_prices.get(ticker)
        pos   = stock_states[ticker]["position"]
        side  = signals[ticker]
        score = scores[ticker]
        atr   = atrs[ticker]
        if not price or not atr:
            continue

        atr = max(atr, price * 0.0015)

        stock_states[ticker]["score"] = score
        if stock_states[ticker]["cooldown"] > 0:
            cd = stock_states[ticker]["cooldown"]
            stock_states[ticker]["status"] = f"[dim]cooldown — {cd} cycles left[/dim]"
            continue
        with stock_data_lock:
            n = len(stock_data[ticker]) if stock_data[ticker] is not None else 0
        if n < 30:
            stock_states[ticker]["status"] = f"[dim]loading ({n}/30 bars)[/dim]"
            continue

        risk_amount = equity * STOCK_RISK * (score / 14)
        sl_dist     = STOCK_ATR_SL * atr
        pos_usd     = risk_amount / (sl_dist / (price + 1e-10))

        available   = _available_stock()
        max_single  = equity * STOCK_MAX_ALLOC * weights[ticker]
        invest      = min(pos_usd, max_single, available)

        if pos is None:
            if side and invest >= 1:
                open_stock_pos(ticker, price, side, invest, atr)
            else:
                stock_states[ticker]["status"] = f"[dim]waiting — score {score}/14[/dim]"
        elif side and side != pos["side"]:
            close_stock_pos(ticker, price, "signal flip")
            stock_states[ticker]["cooldown"] = 1
        else:
            pct  = stock_unrealised_pct(ticker, price)
            sign = "+" if pct >= 0 else ""
            col  = "green" if pct >= 0 else "red"
            stock_states[ticker]["status"] = f"[{col}]{pos['side']}  {sign}{pct:.3f}%  score {score}/14[/{col}]"


# ─────────────────────────────────────────────────────────────
#  HELPERS
# ─────────────────────────────────────────────────────────────
def pnl_12h():
    cutoff = (datetime.now() - timedelta(hours=12)).isoformat()
    return sum(t["pnl"] for t in trades if t.get("timestamp", "") >= cutoff)


def stock_pnl_12h():
    cutoff = (datetime.now() - timedelta(hours=12)).isoformat()
    return sum(t["pnl"] for t in stock_trades if t.get("timestamp", "") >= cutoff)


def market_session():
    from datetime import timezone
    est = timezone(timedelta(hours=-4))
    now = datetime.now(est)
    if now.weekday() >= 5:
        return "closed"
    pre_open   = now.replace(hour=4,  minute=0,  second=0, microsecond=0)
    core_open  = now.replace(hour=9,  minute=30, second=0, microsecond=0)
    core_close = now.replace(hour=16, minute=0,  second=0, microsecond=0)
    ext_close  = now.replace(hour=20, minute=0,  second=0, microsecond=0)
    if core_open <= now < core_close:
        return "core"
    if pre_open <= now < core_open or core_close <= now < ext_close:
        return "extended"
    return "closed"


def market_open():
    return market_session() in ("core", "extended")


def sparkline(values, width=36, height=4):
    if len(values) < 2:
        return ["─" * width] * height
    n   = len(values)
    pts = [values[int(i * (n - 1) / max(width - 1, 1))] for i in range(width)]
    lo, hi = min(pts), max(pts)
    if hi == lo:
        hi += 1e-10
    def to_row(v):
        return int((1 - (v - lo) / (hi - lo)) * (height - 1))
    rows = [to_row(p) for p in pts]
    grid = [[" "] * width for _ in range(height)]
    for x in range(width):
        r  = rows[x]
        rp = rows[x - 1] if x > 0 else r
        if x == 0:
            grid[r][x] = "─"
        elif r == rp:
            grid[r][x] = "─"
        elif r < rp:
            grid[r][x]  = "╱"
            for mid in range(r + 1, rp):
                grid[mid][x] = "│"
            grid[rp][x] = "╱"
        else:
            grid[r][x]  = "╲"
            for mid in range(rp + 1, r):
                grid[mid][x] = "│"
            grid[rp][x] = "╲"
    return ["".join(row) for row in grid]


# ─────────────────────────────────────────────────────────────
#  RICH TUI
# ─────────────────────────────────────────────────────────────
def coin_block(coin, key):
    name  = COIN[coin]
    price = last_prices.get(coin)
    pos   = states[coin]["position"]
    t     = Text()
    if price:
        prev = states[coin]["prev_price"]
        if prev is None or price == prev: arrow, col = "-", "white"
        elif price > prev:                arrow, col = "^", "green"
        else:                             arrow, col = "v", "red"
        states[coin]["prev_price"] = price
        t.append(f"{name}/usd  ", style="white")
        t.append(f"${price:,.4f} ", style=f"bold {col}")
        t.append(f"{arrow}\n", style=col)
    else:
        t.append(f"{name}/usd  no data\n", style="dim")
    if pos:
        pct  = unrealised_pct(coin, price)
        sign = "+" if pct >= 0 else ""
        pc   = "green" if pct >= 0 else "red"
        sc   = "green" if pos["side"] == "long" else "red"
        t.append(f"{pos['side']}  ", style=sc)
        t.append(f"entry ${pos['entry']:,.3f}  ", style="dim")
        t.append(f"{sign}{pct:.3f}%\n", style=pc)
        t.append(f"sl ${pos.get('trail_sl',0):,.3f}  ", style="dim red")
        t.append(f"tp ${pos.get('tp2',0):,.3f}", style="dim green")
        if pos.get("partial_done"):
            t.append("  50% locked\n", style="dim")
        else:
            t.append(f"  tp1 ${pos.get('tp1',0):,.3f}\n", style="dim")
        t.append(f"[{key}] close\n", style="dim")
    else:
        t.append(f"score {states[coin]['score']}/14\n", style="dim")
        t.append("\n")
    t.append(Text.from_markup(states[coin]["status"] + "\n"))
    chart_vals = states[coin]["chart_prices"]
    if len(chart_vals) >= 2:
        chart_col = "green" if chart_vals[-1] >= chart_vals[0] else "red"
        for line in sparkline(chart_vals, width=36, height=4):
            t.append(line + "\n", style=chart_col)
    return t


def stock_block(ticker):
    name  = STOCKS[ticker]
    price = stock_prices.get(ticker)
    pos   = stock_states[ticker]["position"]
    t     = Text()
    if price:
        prev = stock_states[ticker]["prev_price"]
        if prev is None or price == prev: arrow, col = "-", "white"
        elif price > prev:                arrow, col = "^", "green"
        else:                             arrow, col = "v", "red"
        stock_states[ticker]["prev_price"] = price
        t.append(f"{name}  ", style="white")
        t.append(f"${price:,.2f} ", style=f"bold {col}")
        t.append(f"{arrow}\n", style=col)
    else:
        t.append(f"{name}  no data\n", style="dim")
    if pos:
        pct  = stock_unrealised_pct(ticker, price)
        sign = "+" if pct >= 0 else ""
        pc   = "green" if pct >= 0 else "red"
        sc   = "green" if pos["side"] == "long" else "red"
        t.append(f"{pos['side']}  ", style=sc)
        t.append(f"entry ${pos['entry']:,.2f}  ", style="dim")
        t.append(f"{sign}{pct:.3f}%\n", style=pc)
        t.append(f"sl ${pos.get('trail_sl',0):,.2f}  ", style="dim red")
        t.append(f"tp ${pos.get('tp2',0):,.2f}", style="dim green")
        if pos.get("partial_done"):
            t.append("  50% locked\n", style="dim")
        else:
            t.append(f"  tp1 ${pos.get('tp1',0):,.2f}\n", style="dim")
    else:
        t.append(f"score {stock_states[ticker]['score']}/14\n", style="dim")
        t.append("\n")
    t.append(Text.from_markup(stock_states[ticker]["status"] + "\n"))
    chart_vals = stock_states[ticker]["chart_prices"]
    if len(chart_vals) >= 2:
        chart_col = "green" if chart_vals[-1] >= chart_vals[0] else "red"
        for line in sparkline(chart_vals, width=36, height=4):
            t.append(line + "\n", style=chart_col)
    return t


def make_layout():
    eq      = total_equity()
    pnl     = eq - STARTING_BALANCE
    pnl_12  = pnl_12h()
    seq     = stock_total_equity()
    spnl    = seq - STOCK_BALANCE
    spnl_12 = stock_pnl_12h()
    wins    = sum(1 for t in trades       if t["pnl"] > 0  and not t.get("partial"))
    losses  = sum(1 for t in trades       if t["pnl"] <= 0 and not t.get("partial"))
    swins   = sum(1 for t in stock_trades if t["pnl"] > 0  and not t.get("partial"))
    slosses = sum(1 for t in stock_trades if t["pnl"] <= 0 and not t.get("partial"))

    coin_list  = list(COIN.keys())
    stock_list = list(STOCKS.keys())

    layout = Layout()
    layout.split_column(
        Layout(name="crypto_hdr",    size=1),
        Layout(name="crow1",         size=11),
        Layout(name="crow2",         size=11),
        Layout(name="crypto_stats",  size=3),
        Layout(name="crypto_trades", size=9),
        Layout(name="stock_hdr",     size=1),
        Layout(name="srow1",         size=11),
        Layout(name="srow2",         size=11),
        Layout(name="stock_stats",   size=3),
        Layout(name="stock_trades"),
    )

    layout["crypto_hdr"].update(Text(
        "── CRYPTO (" + "  ".join(COIN.values()) + ") ── $6500 | DEPLOY 90% | 11-FACTOR SIGNAL ─────────────",
        style="dim"))
    layout["crow1"].split_row(*[Layout(name=COIN[c]) for c in coin_list[:3]])
    layout["crow2"].split_row(*[Layout(name=COIN[c]) for c in coin_list[3:]])
    for i, coin in enumerate(coin_list):
        row = "crow1" if i < 3 else "crow2"
        layout[row][COIN[coin]].update(coin_block(coin, str(i + 1)))

    cs = Text("\n")
    cs.append("balance  ", style="dim");       cs.append(f"${eq:,.2f}   ", style="white")
    cs.append("p&l  ", style="dim");           cs.append(f"{'+'if pnl>=0 else ''}${pnl:.2f}   ", style="green" if pnl >= 0 else "red")
    cs.append("12h  ", style="dim");           cs.append(f"{'+'if pnl_12>=0 else ''}${pnl_12:.2f}   ", style="green" if pnl_12 >= 0 else "red")
    cs.append("w/l  ", style="dim");           cs.append(f"{wins}", style="green"); cs.append(f"/{losses}\n", style="red")
    layout["crypto_stats"].update(cs)

    clog = Text()
    closed = [t for t in trades if not t.get("partial")]
    if closed:
        clog.append(f"recent crypto trades ({len(closed)} total)\n", style="dim")
        tbl = Table(box=None, show_header=True, header_style="dim", padding=(0, 2), show_edge=False)
        for col, w in [("time",8),("coin",5),("side",5),("in",11),("out",11),("pnl",9),("why",12)]:
            tbl.add_column(col, width=w, justify="right" if col in ("in","out","pnl") else "left")
        for tr in list(reversed(closed))[:5]:
            ps  = f"{'+'if tr['pnl']>=0 else ''}{tr['pct']:.3f}%"
            tbl.add_row(tr["time"], tr["coin"], Text(tr["side"], style="green" if tr["side"]=="long" else "red"),
                        f"${tr['entry']:,.4f}", f"${tr['exit']:,.4f}", Text(ps, style="green" if tr["pnl"]>=0 else "red"), tr["reason"])
        buf = StringIO()
        Console(file=buf, highlight=False, width=95).print(tbl)
        clog.append(buf.getvalue())
    else:
        clog.append("no crypto trades yet\n", style="dim")
    layout["crypto_trades"].update(clog)

    session = market_session()
    if session == "core":
        mkt = "[green]● core hours  9:30–16:00[/green]"
    elif session == "extended":
        mkt = "[yellow]● extended hours  4:00–20:00[/yellow]"
    else:
        mkt = "[dim]● closed (weekend)[/dim]"
    layout["stock_hdr"].update(Text.from_markup(
        f"── US STOCKS  {mkt}  $6500 | DEPLOY 90% | 11-FACTOR SIGNAL ──────────────────────────"))

    layout["srow1"].split_row(*[Layout(name=f"s{STOCKS[t]}") for t in stock_list[:5]])
    layout["srow2"].split_row(*[Layout(name=f"s{STOCKS[t]}") for t in stock_list[5:]])
    for i, ticker in enumerate(stock_list):
        row = "srow1" if i < 5 else "srow2"
        layout[row][f"s{STOCKS[ticker]}"].update(stock_block(ticker))

    ss = Text("\n")
    ss.append("balance  ", style="dim");      ss.append(f"${seq:,.2f}   ", style="white")
    ss.append("p&l  ", style="dim");          ss.append(f"{'+'if spnl>=0 else ''}${spnl:.2f}   ", style="green" if spnl >= 0 else "red")
    ss.append("12h  ", style="dim");          ss.append(f"{'+'if spnl_12>=0 else ''}${spnl_12:.2f}   ", style="green" if spnl_12 >= 0 else "red")
    ss.append("w/l  ", style="dim");          ss.append(f"{swins}", style="green"); ss.append(f"/{slosses}\n", style="red")
    layout["stock_stats"].update(ss)

    slog = Text()
    sclosed = [t for t in stock_trades if not t.get("partial")]
    if sclosed:
        slog.append(f"recent stock trades ({len(sclosed)} total)\n", style="dim")
        stbl = Table(box=None, show_header=True, header_style="dim", padding=(0, 2), show_edge=False)
        for col, w in [("time",8),("stock",9),("side",5),("in",11),("out",11),("pnl",9),("why",12)]:
            stbl.add_column(col, width=w, justify="right" if col in ("in","out","pnl") else "left")
        for tr in list(reversed(sclosed))[:8]:
            ps  = f"{'+'if tr['pnl']>=0 else ''}{tr['pct']:.3f}%"
            stbl.add_row(tr["time"], tr["ticker"], Text(tr["side"], style="green" if tr["side"]=="long" else "red"),
                         f"${tr['entry']:,.2f}", f"${tr['exit']:,.2f}", Text(ps, style="green" if tr["pnl"]>=0 else "red"), tr["reason"])
        buf2 = StringIO()
        Console(file=buf2, highlight=False, width=95).print(stbl)
        slog.append(buf2.getvalue())
    else:
        slog.append("no stock trades yet\n", style="dim")
    slog.append("ctrl+c to quit  |  keys 1-6 manually close crypto position\n", style="dim")
    layout["stock_trades"].update(slog)

    return layout


# ─────────────────────────────────────────────────────────────
#  WEB SERVER  (unchanged from v2.1 — keep full HTML + routes)
# ─────────────────────────────────────────────────────────────
NEWS_API_KEY = "d86043bb8c9043158c7dbd18292c2f0e"
live_news = []

def fetch_live_news():
    global live_news
    while True:
        try:
            url = (
                f"https://newsapi.org/v2/top-headlines?"
                f"category=business&language=en&pageSize=15&apiKey={NEWS_API_KEY}"
            )
            r = requests.get(url, timeout=10)
            data = r.json()
            if "articles" in data:
                news = []
                for article in data["articles"]:
                    news.append({
                        "title": article.get("title", "No title"),
                        "source": article.get("source", {}).get("name", "Unknown"),
                        "url": article.get("url", ""),
                        "time": article.get("publishedAt", "")
                    })
                live_news = news
        except Exception as e:
            print("News Error:", e)
        time.sleep(60)


def get_country_market_data(country):
    country = country.lower()
    if country not in COUNTRY_MARKETS:
        return {"error": "country not supported"}
    cfg = COUNTRY_MARKETS[country]
    try:
        idx = yf.Ticker(cfg["ticker"])
        hist = idx.history(period="1d", interval="1m")
        index_price = round(float(hist["Close"].iloc[-1]), 2)
    except:
        index_price = None
    commodities = {}
    for name, ticker in COMMODITIES.items():
        try:
            c = yf.Ticker(ticker)
            hist = c.history(period="1d", interval="1m")
            commodities[name] = round(float(hist["Close"].iloc[-1]), 2)
        except:
            commodities[name] = None
    news = []
    try:
        url = (
            f"https://newsapi.org/v2/everything?"
            f"q={cfg['query']}"
            f"&language=en&sortBy=publishedAt&pageSize=10&apiKey={NEWS_API_KEY}"
        )
        r = requests.get(url, timeout=10)
        data = r.json()
        if "articles" in data:
            for article in data["articles"]:
                news.append({
                    "title": article.get("title"),
                    "source": article.get("source", {}).get("name"),
                    "url": article.get("url"),
                    "time": article.get("publishedAt")
                })
    except Exception as e:
        print("Country news error:", e)
    return {
        "country": country,
        "index": {"name": cfg["index_name"], "price": index_price},
        "gold": commodities["gold"],
        "silver": commodities["silver"],
        "crude": commodities["crude"],
        "news": news
    }


COUNTRY_MARKETS = {
    "india":       {"index_name": "NIFTY 50",           "ticker": "^NSEI",      "query": "India stock market"},
    "usa":         {"index_name": "S&P 500",             "ticker": "^GSPC",      "query": "US stock market"},
    "uk":          {"index_name": "FTSE 100",            "ticker": "^FTSE",      "query": "UK economy"},
    "japan":       {"index_name": "Nikkei 225",          "ticker": "^N225",      "query": "Japan economy"},
    "china":       {"index_name": "Shanghai Composite",  "ticker": "000001.SS",  "query": "China economy"},
    "germany":     {"index_name": "DAX",                 "ticker": "^GDAXI",     "query": "Germany economy"},
    "france":      {"index_name": "CAC 40",              "ticker": "^FCHI",      "query": "France economy"},
    "australia":   {"index_name": "ASX 200",             "ticker": "^AXJO",      "query": "Australia economy"},
    "canada":      {"index_name": "TSX Composite",       "ticker": "^GSPTSE",    "query": "Canada economy"},
    "brazil":      {"index_name": "Bovespa",             "ticker": "^BVSP",      "query": "Brazil economy"},
    "south korea": {"index_name": "KOSPI",               "ticker": "^KS11",      "query": "South Korea economy"},
    "hong kong":   {"index_name": "Hang Seng",           "ticker": "^HSI",       "query": "Hong Kong economy"},
    "singapore":   {"index_name": "STI",                 "ticker": "^STI",       "query": "Singapore economy"},
    "switzerland": {"index_name": "SMI",                 "ticker": "^SSMI",      "query": "Switzerland economy"},
    "netherlands": {"index_name": "AEX",                 "ticker": "^AEX",       "query": "Netherlands economy"},
    "spain":       {"index_name": "IBEX 35",             "ticker": "^IBEX",      "query": "Spain economy"},
    "italy":       {"index_name": "FTSE MIB",            "ticker": "FTSEMIB.MI", "query": "Italy economy"},
    "sweden":      {"index_name": "OMX Stockholm 30",    "ticker": "^OMX",       "query": "Sweden economy"},
    "norway":      {"index_name": "OBX",                 "ticker": "^OBX",       "query": "Norway economy"},
    "denmark":     {"index_name": "OMX Copenhagen 20",   "ticker": "^OMXC20",    "query": "Denmark economy"},
    "mexico":      {"index_name": "IPC Mexico",          "ticker": "^MXX",       "query": "Mexico economy"},
    "argentina":   {"index_name": "MERVAL",              "ticker": "^MERV",      "query": "Argentina economy"},
    "russia":      {"index_name": "MOEX Russia",         "ticker": "IMOEX.ME",   "query": "Russia economy"},
    "turkey":      {"index_name": "BIST 100",            "ticker": "XU100.IS",   "query": "Turkey economy"},
    "saudi arabia":{"index_name": "Tadawul",             "ticker": "^TASI.SR",   "query": "Saudi Arabia economy"},
    "south africa":{"index_name": "JSE Top 40",          "ticker": "^JN0U.JO",   "query": "South Africa economy"},
    "indonesia":   {"index_name": "IDX Composite",       "ticker": "^JKSE",      "query": "Indonesia economy"},
    "malaysia":    {"index_name": "KLCI",                "ticker": "^KLSE",      "query": "Malaysia economy"},
    "thailand":    {"index_name": "SET Index",           "ticker": "^SET.BK",    "query": "Thailand economy"},
    "pakistan":    {"index_name": "KSE 100",             "ticker": "^KSE",       "query": "Pakistan economy"},
    "new zealand": {"index_name": "NZX 50",              "ticker": "^NZ50",      "query": "New Zealand economy"},
    "taiwan":      {"index_name": "TAIEX",               "ticker": "^TWII",      "query": "Taiwan economy"},
    "israel":      {"index_name": "TA-125",              "ticker": "^TA125.TA",  "query": "Israel economy"},
    "portugal":    {"index_name": "PSI 20",              "ticker": "^PSI20",     "query": "Portugal economy"},
    "poland":      {"index_name": "WIG20",               "ticker": "^WIG20",     "query": "Poland economy"},
    "austria":     {"index_name": "ATX",                 "ticker": "^ATX",       "query": "Austria economy"},
    "belgium":     {"index_name": "BEL 20",              "ticker": "^BFX",       "query": "Belgium economy"},
    "finland":     {"index_name": "OMX Helsinki 25",     "ticker": "^OMXH25",    "query": "Finland economy"},
    "ireland":     {"index_name": "ISEQ Overall",        "ticker": "^ISEQ",      "query": "Ireland economy"},
    "egypt":       {"index_name": "EGX 30",              "ticker": "^CASE30",    "query": "Egypt economy"},
    "nigeria":     {"index_name": "NGX All-Share",       "ticker": "^NGSEINDX",  "query": "Nigeria economy"},
    "kenya":       {"index_name": "NSE 20",              "ticker": "^NSE20",     "query": "Kenya economy"},
    "chile":       {"index_name": "IPSA",                "ticker": "^IPSA",      "query": "Chile economy"},
    "colombia":    {"index_name": "COLCAP",              "ticker": "^COLCAP",    "query": "Colombia economy"},
    "peru":        {"index_name": "S&P Lima General",    "ticker": "^SPBLPGPT",  "query": "Peru economy"},
    "bangladesh":  {"index_name": "DSEX",                "ticker": "^DSEX",      "query": "Bangladesh economy"},
    "sri lanka":   {"index_name": "CSE All-Share",       "ticker": "^CSEALL.CM", "query": "Sri Lanka economy"},
    "vietnam":     {"index_name": "VN Index",            "ticker": "^VNINDEX",   "query": "Vietnam economy"},
    "philippines": {"index_name": "PSEi",                "ticker": "PSEI.PS",    "query": "Philippines economy"},
    "greece":      {"index_name": "Athens General",      "ticker": "^ATG",       "query": "Greece economy"},
    "czech republic": {"index_name": "PX Index",         "ticker": "^PX",        "query": "Czech Republic economy"},
    "hungary":     {"index_name": "BUX",                 "ticker": "^BUX",       "query": "Hungary economy"},
    "romania":     {"index_name": "BET",                 "ticker": "^BET",       "query": "Romania economy"},
    "ukraine":     {"index_name": "PFTS",                "ticker": "^PFTS",      "query": "Ukraine economy"},
    "qatar":       {"index_name": "QE Index",            "ticker": "^QSI",       "query": "Qatar economy"},
    "uae":         {"index_name": "ADX General",         "ticker": "^FTFADGI",   "query": "UAE economy"},
    "kuwait":      {"index_name": "Kuwait Main Market",  "ticker": "^KWSE",      "query": "Kuwait economy"},
    "bahrain":     {"index_name": "Bahrain All Share",   "ticker": "^BHSEASI",   "query": "Bahrain economy"},
    "iceland":     {"index_name": "OMXI10",              "ticker": "^OMXI10",    "query": "Iceland economy"},
    "luxembourg":  {"index_name": "LuxX Index",          "ticker": "^LUX",       "query": "Luxembourg economy"},
    "slovakia":    {"index_name": "SAX Index",           "ticker": "^SAX",       "query": "Slovakia economy"},
    "croatia":     {"index_name": "CROBEX",              "ticker": "^CROBEX",    "query": "Croatia economy"},
    "serbia":      {"index_name": "BELEX15",             "ticker": "^BELEX15",   "query": "Serbia economy"},
    "bulgaria":    {"index_name": "SOFIX",               "ticker": "^SOFIX",     "query": "Bulgaria economy"},
    "estonia":     {"index_name": "OMX Tallinn",         "ticker": "^OMXTGI",    "query": "Estonia economy"},
    "latvia":      {"index_name": "OMX Riga",            "ticker": "^OMXRGI",    "query": "Latvia economy"},
    "lithuania":   {"index_name": "OMX Vilnius",         "ticker": "^OMXVGI",    "query": "Lithuania economy"},
    "slovenia":    {"index_name": "SBI TOP",             "ticker": "^SBITOP",    "query": "Slovenia economy"},
    "cyprus":      {"index_name": "CSE General",         "ticker": "^CSE",       "query": "Cyprus economy"},
    "malta":       {"index_name": "MSE Index",           "ticker": "^MSE",       "query": "Malta economy"},
    "oman":        {"index_name": "MSM 30",              "ticker": "^MSM30",     "query": "Oman economy"},
    "jordan":      {"index_name": "ASE General",         "ticker": "^AMMANME",   "query": "Jordan economy"},
    "lebanon":     {"index_name": "BLOM Stock Index",    "ticker": "^BLOM",      "query": "Lebanon economy"},
    "morocco":     {"index_name": "MASI",                "ticker": "^MASI",      "query": "Morocco economy"},
    "tunisia":     {"index_name": "TUNINDEX",            "ticker": "^TUNINDEX",  "query": "Tunisia economy"},
    "ghana":       {"index_name": "GSE Composite",       "ticker": "^GGSECI",    "query": "Ghana economy"},
    "zimbabwe":    {"index_name": "ZSE Industrial",      "ticker": "^INDUS.ZW",  "query": "Zimbabwe economy"},
    "botswana":    {"index_name": "DCI",                 "ticker": "^DCI",       "query": "Botswana economy"},
    "namibia":     {"index_name": "NSX Overall",         "ticker": "^FTN098",    "query": "Namibia economy"},
    "tanzania":    {"index_name": "DSE All Share",       "ticker": "^DSE",       "query": "Tanzania economy"},
    "zambia":      {"index_name": "LuSE All Share",      "ticker": "^LUSE",      "query": "Zambia economy"},
    "myanmar":     {"index_name": "Myanmar Index",       "ticker": "^MYANPIX",   "query": "Myanmar economy"},
    "cambodia":    {"index_name": "CSX Index",           "ticker": "^CSXSI",     "query": "Cambodia economy"},
    "mongolia":    {"index_name": "MSE Top 20",          "ticker": "^MSE20",     "query": "Mongolia economy"},
    "nepal":       {"index_name": "NEPSE",               "ticker": "^NEPSE",     "query": "Nepal economy"},
    "laos":        {"index_name": "LSX Composite",       "ticker": "^LSXC",      "query": "Laos economy"},
    "maldives":    {"index_name": "MMA Index",           "ticker": "^MMA",       "query": "Maldives economy"},
    "iran":        {"index_name": "Tehran Exchange",     "ticker": "^TEDPIX",    "query": "Iran economy"},
    "iraq":        {"index_name": "ISX Index",           "ticker": "^ISX60",     "query": "Iraq economy"},
    "uzbekistan":  {"index_name": "UZSE Index",          "ticker": "^UZSE",      "query": "Uzbekistan economy"},
    "kazakhstan":  {"index_name": "KASE Index",          "ticker": "^KASE",      "query": "Kazakhstan economy"},
    "azerbaijan":  {"index_name": "BSE Index",           "ticker": "^BJSE",      "query": "Azerbaijan economy"},
    "georgia":     {"index_name": "GSE Index",           "ticker": "^GSE",       "query": "Georgia economy"},
    "armenia":     {"index_name": "AMX Index",           "ticker": "^AMX",       "query": "Armenia economy"},
    "venezuela":   {"index_name": "IBC Index",           "ticker": "^IBC",       "query": "Venezuela economy"},
    "ecuador":     {"index_name": "BVQ Index",           "ticker": "^ECU",       "query": "Ecuador economy"},
    "bolivia":     {"index_name": "BBV Index",           "ticker": "^BBV",       "query": "Bolivia economy"},
    "paraguay":    {"index_name": "BVPASA",              "ticker": "^BVPASA",    "query": "Paraguay economy"},
    "uruguay":     {"index_name": "BEVSA Index",         "ticker": "^BEVSA",     "query": "Uruguay economy"},
    "panama":      {"index_name": "BVPSI",               "ticker": "^BVPSI",     "query": "Panama economy"},
    "costa rica":  {"index_name": "CRSMBCT",             "ticker": "^CRSMBCT",   "query": "Costa Rica economy"},
    "jamaica":     {"index_name": "JSE Market",          "ticker": "^JMSMX",     "query": "Jamaica economy"},
    "trinidad":    {"index_name": "TTD Composite",       "ticker": "^TTD",       "query": "Trinidad economy"},
    "barbados":    {"index_name": "BSE Index",           "ticker": "^BSE",       "query": "Barbados economy"},
    "papua new guinea": {"index_name": "PNGX Index",    "ticker": "^PNGX",      "query": "Papua New Guinea economy"},
    "fiji":        {"index_name": "SPX Fiji",            "ticker": "^SPXF",      "query": "Fiji economy"},
}

COMMODITIES = {
    "gold": "GC=F",
    "silver": "SI=F",
    "crude": "CL=F",
}

WEB_PORT = 5050

# ── Paste the full HTML string from v2.1 here unchanged ──────
# (kept identical to original — no UI changes needed)
HTML = '''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>TRADING TERMINAL v3.0</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
*{margin:0;padding:0;box-sizing:border-box;}
:root{
  --bg0:#0b0e11;--bg1:#111418;--bg2:#161c22;--bg3:#1c2530;--bg4:#222d3a;
  --border:#253040;--border-hi:#2e3d50;--border-dim:#1a2230;
  --orange:#e8920a;--orange-dim:#7a4d08;--orange-pale:#c47a0a;
  --amber:#f5c842;--amber-dim:#8a7020;--blue:#3a7bd5;--blue-hi:#4ea1ff;--blue-dim:#1a3a6b;
  --cyan:#5bc0de;--cyan-dim:#1e5060;--green:#5cb85c;--green-dim:#2d5c2d;
  --red:#d9534f;--red-dim:#5c2222;--white:#d6dde6;--gray:#95a3b3;--gray-dim:#6b7785;--gray-dark:#3d4d5c;
  --font:'Courier New',Courier,'Lucida Console',monospace;
}
html,body{height:100%;overflow:auto;background:var(--bg0);}
body{display:flex;flex-direction:column;color:var(--white);font-family:var(--font);font-size:10px;line-height:1.3;}
#cmdbar{background:#000;border-bottom:1px solid var(--border);height:20px;display:flex;align-items:stretch;flex-shrink:0;}
.cmd-brand{background:var(--orange);color:#000;font-weight:bold;font-size:11px;letter-spacing:2px;padding:0 10px;display:flex;align-items:center;border-right:2px solid var(--orange-dim);flex-shrink:0;}
.cmd-input-area{display:flex;align-items:center;padding:0 8px;gap:4px;border-right:1px solid var(--border);flex-shrink:0;}
.cmd-prompt{color:var(--orange);font-size:9px;font-weight:bold;}
.cmd-text{color:var(--amber);font-size:9px;min-width:120px;}
.cmd-pills{display:flex;align-items:center;padding:0 6px;}
.cmd-pill{display:inline-flex;align-items:center;background:var(--bg3);border:1px solid var(--border-hi);color:var(--blue-hi);font-size:8px;padding:1px 5px;margin:0 1px;cursor:default;}
.sysbar-right{margin-left:auto;display:flex;align-items:stretch;}
.sys-cell{display:flex;align-items:center;gap:3px;padding:0 8px;font-size:8px;border-left:1px solid var(--border);color:var(--gray-dim);}
.sys-cell .sv{color:var(--gray);}.sys-cell .ok{color:var(--green);}
#sys-clock{color:var(--amber);font-weight:bold;font-size:9px;letter-spacing:1px;}
.blink{animation:bk 1.4s step-end infinite;}
@keyframes bk{0%,100%{opacity:1;}50%{opacity:0;}}
#acctbar{background:var(--bg1);border-bottom:2px solid var(--border);height:28px;display:flex;align-items:stretch;flex-shrink:0;}
.acct-seg{display:flex;align-items:center;border-right:1px solid var(--border);padding:0 8px;gap:5px;}
.acct-lbl{font-size:7px;color:var(--gray-dim);text-transform:uppercase;letter-spacing:0.5px;white-space:nowrap;}
.acct-val{font-size:11px;font-weight:bold;color:var(--amber);white-space:nowrap;font-variant-numeric:tabular-nums;}
.acct-val.pos{color:var(--green);}.acct-val.neg{color:var(--red);}.acct-val.blue{color:var(--blue-hi);}
.acct-divider{width:1px;height:14px;background:var(--border);}
.acct-seg.mkt{margin-left:auto;border-right:none;border-left:1px solid var(--border);}
#mkt-status{font-size:9px;font-weight:bold;}.mkt-core{color:var(--green);}.mkt-ext{color:var(--amber);}.mkt-closed{color:var(--gray-dim);}
#ticker-strip{background:var(--bg1);border-bottom:1px solid var(--border);height:17px;display:flex;align-items:center;overflow:hidden;flex-shrink:0;}
#ticker-tag{background:var(--blue-dim);border-right:1px solid var(--blue);color:var(--blue-hi);font-size:8px;font-weight:bold;padding:0 7px;height:100%;display:flex;align-items:center;letter-spacing:1.5px;flex-shrink:0;}
#tick-inner{display:inline-block;white-space:nowrap;animation:scroll-t 70s linear infinite;}
@keyframes scroll-t{0%{transform:translateX(0);}100%{transform:translateX(-50%);}}
.ti{display:inline-block;padding:0 10px;font-size:8px;border-right:1px solid var(--border-dim);}
.ti-s{color:var(--gray-dim);margin-right:3px;}.ti-p{color:var(--amber);font-weight:bold;}
.ti-c.up{color:var(--green);}.ti-c.dn{color:var(--red);}
#fkbar{background:var(--bg2);border-bottom:1px solid var(--border-dim);height:16px;display:flex;align-items:stretch;flex-shrink:0;}
.fk{display:flex;align-items:center;gap:2px;padding:0 7px;border-right:1px solid var(--border-dim);cursor:pointer;font-size:8px;background:var(--bg2);border:none;color:var(--white);font-family:var(--font);height:100%;}
.fk:hover{background:var(--bg3);}.fk .fn{color:var(--orange);font-weight:bold;}.fk .fl{color:var(--gray-dim);}
.fk.active{background:var(--bg3);border-bottom:1px solid var(--orange);}.fk.active .fl{color:var(--white);}
#body{display:grid;grid-template-columns:1fr 1fr 180px;grid-template-rows:1fr;gap:1px;background:var(--border-dim);flex:1;min-height:0;overflow:hidden;}
.panel{background:var(--bg0);display:flex;flex-direction:column;min-height:0;overflow:hidden;}
.ph{background:var(--bg2);border-bottom:1px solid var(--border);height:18px;display:flex;align-items:center;justify-content:space-between;padding:0 6px;flex-shrink:0;}
.ph-title{font-size:8px;font-weight:bold;color:var(--gray);text-transform:uppercase;letter-spacing:1.5px;border-left:2px solid var(--orange);padding-left:4px;}
.ph-meta{font-size:7px;color:var(--gray-dim);display:flex;align-items:center;gap:6px;}.ph-meta .live{color:var(--green);}
.ph-sub{background:var(--bg1);border-bottom:1px solid var(--border-dim);height:14px;display:flex;align-items:center;padding:0 5px;flex-shrink:0;font-size:7px;color:var(--gray-dim);gap:8px;}
.ph-sub .tag{color:var(--blue-hi);font-weight:bold;}
#lcol{display:flex;flex-direction:column;gap:1px;background:var(--border-dim);min-height:0;overflow:hidden;}
#ccol{display:flex;flex-direction:column;gap:1px;background:var(--border-dim);min-height:0;overflow:hidden;}
#rcol{display:flex;flex-direction:column;gap:1px;background:var(--border-dim);min-height:0;overflow:hidden;}
.mw-tbl-wrap{overflow-y:auto;flex:1;min-height:0;}
.mw-tbl{width:100%;border-collapse:collapse;table-layout:fixed;}
.mw-tbl thead th{background:var(--bg2);color:var(--gray-dim);font-size:7px;font-weight:normal;text-transform:uppercase;letter-spacing:0.5px;padding:2px 4px;border-bottom:1px solid var(--border);white-space:nowrap;position:sticky;top:0;z-index:2;font-variant-numeric:tabular-nums;}
.mw-tbl thead th.or{color:var(--orange);}
.mw-tbl tbody tr{cursor:default;border-bottom:1px solid var(--bg2);}
.mw-tbl tbody tr:hover{background:var(--bg3)!important;}
.mw-tbl tbody tr:nth-child(even){background:var(--bg1);}
.mw-tbl td{padding:1px 4px;font-size:9px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-variant-numeric:tabular-nums;vertical-align:middle;}
.mw-tbl td.sym{color:var(--amber);font-weight:bold;font-size:9px;}
.mw-tbl td.px{color:var(--amber);font-weight:bold;text-align:right;}
.mw-tbl td.up{color:var(--green);}.mw-tbl td.dn{color:var(--red);}
.mw-tbl td.dim{color:var(--gray-dim);}.mw-tbl td.sc{color:var(--blue-hi);text-align:right;}
.mw-tbl td.long{color:var(--green);font-weight:bold;}.mw-tbl td.short{color:var(--red);font-weight:bold;}
.mw-tbl td.num{text-align:right;}.mw-tbl td.reason{color:var(--gray-dim);font-size:8px;}
.spark-cell{width:52px;}.spark-cell canvas{display:block;}
@keyframes fup{0%{background:#0d2e1a;}100%{background:transparent;}}
@keyframes fdn{0%{background:#2e0d0d;}100%{background:transparent;}}
.fl-up{animation:fup 0.5s ease-out;}.fl-dn{animation:fdn 0.5s ease-out;}
.pos-tbl{width:100%;border-collapse:collapse;table-layout:fixed;}
.pos-tbl th{background:var(--bg2);color:var(--gray-dim);font-size:7px;font-weight:normal;text-transform:uppercase;padding:2px 4px;border-bottom:1px solid var(--border);white-space:nowrap;position:sticky;top:0;letter-spacing:0.5px;}
.pos-tbl td{padding:1px 4px;font-size:9px;border-bottom:1px solid var(--bg2);white-space:nowrap;font-variant-numeric:tabular-nums;}
.pos-tbl tr:hover td{background:var(--bg3);}.pos-tbl tr:nth-child(even) td{background:var(--bg1);}
.pos-tbl td.sym{color:var(--amber);font-weight:bold;}.pos-tbl td.up{color:var(--green);}.pos-tbl td.dn{color:var(--red);}
.pos-tbl td.long{color:var(--green);}.pos-tbl td.short{color:var(--red);}.pos-tbl td.num{text-align:right;}
.scan-row{display:flex;align-items:center;gap:4px;padding:1px 6px;border-bottom:1px solid var(--bg2);font-size:8px;cursor:default;}
.scan-row:hover{background:var(--bg2);}.scan-row:nth-child(even){background:var(--bg1);}
.sc-sym{width:42px;color:var(--amber);font-weight:bold;font-size:8px;flex-shrink:0;}
.sc-bar{flex:1;height:4px;background:var(--bg3);position:relative;overflow:hidden;}
.sc-fill{height:100%;position:absolute;left:0;top:0;transition:width 0.5s;}
.sc-fill.bull{background:var(--green-dim);}.sc-fill.bear{background:var(--red-dim);}
.sc-score{width:28px;text-align:right;color:var(--blue-hi);font-size:7px;flex-shrink:0;}
.sc-side{width:32px;font-size:7px;font-weight:bold;flex-shrink:0;}
.sc-side.long{color:var(--green);}.sc-side.short{color:var(--red);}.sc-side.none{color:var(--gray-dark);}
.al-row{display:flex;align-items:flex-start;gap:4px;padding:1px 5px;border-bottom:1px solid var(--bg2);font-size:8px;}
.al-row:nth-child(even){background:var(--bg1);}.al-row:hover{background:var(--bg2);}
.al-t{color:var(--gray-dim);width:38px;flex-shrink:0;font-size:7px;}.al-s{color:var(--amber);width:44px;flex-shrink:0;font-weight:bold;}.al-m{flex:1;color:var(--gray);}
.al-row.buy .al-m{color:var(--green);}.al-row.sell .al-m{color:var(--red);}.al-row.warn .al-m{color:var(--amber);}.al-row.info .al-m{color:var(--blue-hi);}
.feed-row{display:flex;align-items:center;gap:5px;padding:1px 6px;border-bottom:1px solid var(--bg2);font-size:8px;}
.feed-dot{width:5px;height:5px;border-radius:50%;flex-shrink:0;}.feed-dot.ok{background:var(--green);}
.feed-dot.warn{background:var(--amber);animation:bk 1s step-end infinite;}.feed-dot.err{background:var(--red);}
.feed-name{color:var(--gray);flex:1;font-size:8px;}.feed-st{font-size:7px;color:var(--gray-dim);}.feed-st.ok{color:var(--green);}
.stat-grid{display:grid;grid-template-columns:1fr 1fr;gap:0;background:var(--border-dim);}
.stat-cell{background:var(--bg1);padding:3px 6px;border-bottom:1px solid var(--bg2);}
.stat-cell .sl{font-size:7px;color:var(--gray-dim);text-transform:uppercase;letter-spacing:0.5px;}
.stat-cell .sv{font-size:11px;font-weight:bold;color:var(--amber);font-variant-numeric:tabular-nums;}
.stat-cell .sv.pos{color:var(--green);}.stat-cell .sv.neg{color:var(--red);}.stat-cell .sv.blue{color:var(--blue-hi);}
.sdiv{background:var(--bg2);border-top:1px solid var(--blue-dim);border-bottom:1px solid var(--border-dim);padding:1px 6px;font-size:7px;color:var(--blue-hi);text-transform:uppercase;letter-spacing:2px;display:flex;justify-content:space-between;align-items:center;flex-shrink:0;height:14px;}
.sdiv span{color:var(--gray-dim);}
#statusbar{background:#000;border-top:1px solid var(--border);height:14px;display:flex;align-items:center;padding:0 6px;gap:12px;font-size:7px;color:var(--gray-dim);flex-shrink:0;}
#statusbar .sb-lbl{color:var(--gray-dark);}#statusbar .sb-ok{color:var(--green);}#statusbar .sb-val{color:var(--gray);}#statusbar .sb-right{margin-left:auto;color:var(--gray-dark);}
::-webkit-scrollbar{width:3px;height:3px;}::-webkit-scrollbar-track{background:var(--bg1);}::-webkit-scrollbar-thumb{background:var(--bg4);}
.news-row{display:flex;gap:4px;align-items:flex-start;padding:2px 5px;border-bottom:1px solid var(--bg2);font-size:8px;}
.news-row:nth-child(even){background:var(--bg1);}
.news-t{color:var(--gray-dim);width:38px;flex-shrink:0;font-size:7px;}.news-s{width:42px;color:var(--cyan);font-weight:bold;flex-shrink:0;}.news-h{flex:1;color:var(--gray);line-height:1.2;}
.news-row.brk .news-h{color:var(--amber);}.news-row.neg .news-h{color:var(--red);}.news-row.pos .news-h{color:var(--green);}
@keyframes pfl-up{0%{color:var(--green);}100%{color:var(--amber);}}
@keyframes pfl-dn{0%{color:var(--red);}100%{color:var(--amber);}}
.pf-up{animation:pfl-up 0.8s ease-out;}.pf-dn{animation:pfl-dn 0.8s ease-out;}
.w-sym{width:52px;}.w-px{width:72px;}.w-pct{width:54px;}.w-sc{width:28px;}.w-side{width:36px;}.w-entry{width:66px;}.w-sl{width:62px;}.w-tp{width:62px;}.w-stat{width:46px;}.w-spark{width:54px;}.w-time{width:40px;}.w-why{width:62px;}.w-pnl{width:52px;}
#fk-right{margin-left:auto;display:flex;align-items:center;gap:12px;padding:0 8px;font-size:7px;color:var(--gray-dim);}
.fkr-ref{color:var(--amber);}
</style>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/jsvectormap/dist/css/jsvectormap.min.css">
<script src="https://cdn.jsdelivr.net/npm/jsvectormap"></script>
<script src="https://cdn.jsdelivr.net/npm/jsvectormap/dist/maps/world.js"></script>
</head>
<body>
<div id="cmdbar">
  <div class="cmd-brand">TRMNL v3</div>
  <div class="cmd-input-area"><span class="cmd-prompt">CMD&gt;</span><span class="cmd-text" id="cmd-display"</span></div>
  <div class="cmd-pills"><span class="cmd-pill">MKTW</span><span class="cmd-pill">POS</span><span class="cmd-pill">SCAN</span><span class="cmd-pill">RISK</span><span class="cmd-pill">NEWS</span></div>
  <div class="sysbar-right">
    <div class="sys-cell"><span class="sb-lbl">LAT</span><span class="sv" id="sb-lat">--ms</span></div>
    <div class="sys-cell"><span class="sb-lbl">POS</span><span class="sv" id="sb-pos">0</span></div>
    <div class="sys-cell"><span class="sb-lbl">ENG</span><span class="ok">RUN</span></div>
    <div class="sys-cell"><span class="sb-lbl">FEED</span><span class="ok">LIVE</span></div>
    <div class="sys-cell"><span class="sb-lbl">SIGS</span><span class="sv" id="sb-sigs">0</span></div>
    <div class="sys-cell" style="border-right:none"><span id="sys-clock">--:--:--</span></div>
  </div>
</div>
<div id="acctbar">
  <div class="acct-seg">
    <span class="acct-lbl">CRYPTO EQ</span><span class="acct-val" id="ac-ceq">--</span>
    <div class="acct-divider"></div><span class="acct-lbl">P&amp;L</span><span class="acct-val" id="ac-cpnl">--</span>
    <div class="acct-divider"></div><span class="acct-lbl">W/L</span><span class="acct-val blue" id="ac-cwl">--</span>
  </div>
  <div class="acct-seg" style="border-left:2px solid var(--border);">
    <span class="acct-lbl">STOCKS EQ</span><span class="acct-val" id="ac-seq">--</span>
    <div class="acct-divider"></div><span class="acct-lbl">P&amp;L</span><span class="acct-val" id="ac-spnl">--</span>
    <div class="acct-divider"></div><span class="acct-lbl">W/L</span><span class="acct-val blue" id="ac-swl">--</span>
  </div>
  <div class="acct-seg" style="border-left:2px solid var(--border);">
    <span class="acct-lbl">TOTAL EQ</span><span class="acct-val" id="ac-teq">--</span>
    <div class="acct-divider"></div><span class="acct-lbl">WIN RATE</span><span class="acct-val blue" id="ac-wr">--%</span>
    <div class="acct-divider"></div><span class="acct-lbl">OPEN POS</span><span class="acct-val" id="ac-op">0</span>
  </div>
  <div class="acct-seg mkt"><span class="acct-lbl">SESSION</span><span id="mkt-status" class="mkt-closed">● LOADING</span></div>
</div>
<div id="ticker-strip">
  <div id="ticker-tag">QUOTES</div>
  <div style="overflow:hidden;flex:1;"><div id="tick-inner">initializing feed...</div></div>
</div>
<div id="fkbar">
  <button class="fk active" id="tab-f1"><span class="fn">F1</span><span class="fl">MKTWATCH</span></button>
  <button class="fk" id="tab-f2"><span class="fn">F2</span><span class="fl">POSITIONS</span></button>
  <button class="fk" id="tab-f3"><span class="fn">F3</span><span class="fl">ORDERS</span></button>
  <button class="fk" id="tab-f4"><span class="fn">F4</span><span class="fl">HISTORY</span></button>
  <button class="fk" id="tab-f5"><span class="fn">F5</span><span class="fl">SCANNER</span></button>
  <button class="fk" id="tab-f6"><span class="fn">F6</span><span class="fl">WORLD MAP</span></button>
  <button class="fk" id="tab-f7"><span class="fn">F7</span><span class="fl">FEEDS</span></button>
  <button class="fk" id="tab-f8"><span class="fn">F8</span><span class="fl">RISK</span></button>
  <button class="fk" id="tab-f9"><span class="fn">F9</span><span class="fl">CHARTS</span></button>
  <button class="fk" id="tab-f10"><span class="fn">F10</span><span class="fl">NEWS</span></button>
  <div id="fk-right">
    <span>UPTIME <span class="fkr-ref" id="fk-uptime">00:00:00</span></span>
    <span>REFRESHES <span class="fkr-ref" id="fk-ref">0</span></span>
    <span>ALGO <span style="color:var(--cyan)">EMA·RSI·MACD·BB·STOCH·ATR·ADX·CMF·VWAP·SUPER·ROC</span></span>
    <span>RISK/TRADE <span class="fkr-ref">4%</span></span>
    <span>DEPLOY <span class="fkr-ref">90%</span></span>
  </div>
</div>
<div id="dashboard-page">
<div id="body">
  <div id="lcol">
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">CRYPTO MKT WATCH</span><span class="ph-meta"><span>11-FACTOR ALGO | SCORE /14</span><span class="live">● 1m LIVE</span></span></div>
      <div class="ph-sub"><span class="tag">CRYPTO</span><span>BTC · ETH · SOL · BNB · ADA · DOGE</span><span style="margin-left:auto">$6,500 | 90% DEPLOY</span></div>
      <div class="mw-tbl-wrap" style="max-height:148px;">
        <table class="mw-tbl"><thead><tr>
          <th class="w-sym or">SYM</th><th class="w-px">LAST</th><th class="w-pct">CHG%</th><th class="w-sc">SCR</th>
          <th class="w-side">SIG</th><th class="w-entry">ENTRY</th><th class="w-sl">SL</th><th class="w-tp">TP</th><th class="w-pct">UNRL%</th><th class="w-spark">CHART</th>
        </tr></thead><tbody id="crypto-mw-tbody"></tbody></table>
      </div>
    </div>
    <div class="sdiv">■ US EQUITIES — NYSE · NASDAQ <span id="sess-tag">--</span></div>
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">US STOCKS MKT WATCH</span><span class="ph-meta"><span>11-FACTOR | PREPOST · 1m</span><span id="stocks-live" class="live">● LIVE</span></span></div>
      <div class="ph-sub"><span class="tag">EQUITIES</span><span>NVDA · TSLA · AAPL · MSFT · AMZN · META · AMD · PLTR · NFLX · COIN</span><span style="margin-left:auto">$6,500 | 90% DEPLOY</span></div>
      <div class="mw-tbl-wrap" style="max-height:192px;">
        <table class="mw-tbl"><thead><tr>
          <th class="w-sym or">SYM</th><th class="w-px">LAST</th><th class="w-pct">CHG%</th><th class="w-sc">SCR</th>
          <th class="w-side">SIG</th><th class="w-entry">ENTRY</th><th class="w-sl">SL</th><th class="w-tp">TP</th><th class="w-pct">UNRL%</th><th class="w-spark">CHART</th>
        </tr></thead><tbody id="stock-mw-tbody"></tbody></table>
      </div>
    </div>
    <div class="panel" style="flex:1;min-height:0;">
      <div class="ph"><span class="ph-title">EXECUTION LOG</span><span class="ph-meta"><span id="trade-cnt">0 fills</span></span></div>
      <div style="display:grid;grid-template-columns:1fr 1fr;gap:1px;background:var(--border-dim);flex:1;min-height:0;">
        <div style="display:flex;flex-direction:column;background:var(--bg0);min-height:0;">
          <div class="ph-sub"><span class="tag">CRYPTO FILLS</span></div>
          <div class="mw-tbl-wrap"><table class="mw-tbl"><thead><tr>
            <th class="w-time">TIME</th><th class="w-sym">SYM</th><th class="w-side">SIDE</th><th class="w-entry">IN</th><th class="w-entry">OUT</th><th class="w-pnl">P&amp;L%</th><th class="w-why">REASON</th>
          </tr></thead><tbody id="crypto-fills"></tbody></table></div>
        </div>
        <div style="display:flex;flex-direction:column;background:var(--bg0);min-height:0;">
          <div class="ph-sub"><span class="tag">EQUITY FILLS</span></div>
          <div class="mw-tbl-wrap"><table class="mw-tbl"><thead><tr>
            <th class="w-time">TIME</th><th class="w-sym">SYM</th><th class="w-side">SIDE</th><th class="w-entry">IN</th><th class="w-entry">OUT</th><th class="w-pnl">P&amp;L%</th><th class="w-why">REASON</th>
          </tr></thead><tbody id="stock-fills"></tbody></table></div>
        </div>
      </div>
    </div>
  </div>
  <div id="ccol">
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">OPEN POSITIONS</span><span class="ph-meta"><span id="pos-cnt">0 open</span> | <span class="live">● LIVE P&amp;L</span></span></div>
      <div class="mw-tbl-wrap" style="max-height:110px;">
        <table class="pos-tbl"><thead><tr>
          <th class="w-sym">SYM</th><th class="w-side">SIDE</th><th class="w-entry">ENTRY</th><th class="w-px">LAST</th><th class="w-pnl">UNRL%</th><th class="w-sl">SL</th><th class="w-tp">TP</th><th class="w-stat">PARTL</th>
        </tr></thead><tbody id="pos-tbody"></tbody></table>
      </div>
    </div>
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">PORTFOLIO SUMMARY</span><span class="ph-meta" id="pf-time">--</span></div>
      <div class="stat-grid">
        <div class="stat-cell"><div class="sl">TOTAL EQUITY</div><div class="sv" id="st-teq">--</div></div>
        <div class="stat-cell"><div class="sl">TOTAL P&L</div><div class="sv" id="st-tpnl">--</div></div>
        <div class="stat-cell"><div class="sl">CRYPTO BAL</div><div class="sv" id="st-cbal">--</div></div>
        <div class="stat-cell"><div class="sl">STOCKS BAL</div><div class="sv" id="st-sbal">--</div></div>
        <div class="stat-cell"><div class="sl">WIN RATE</div><div class="sv blue" id="st-wr">--%</div></div>
        <div class="stat-cell"><div class="sl">TOTAL FILLS</div><div class="sv blue" id="st-fills">0</div></div>
      </div>
    </div>
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">SIGNAL SCANNER — 11 FACTORS /14 MAX</span><span class="ph-meta"><span class="live blink">● SCANNING</span></span></div>
      <div style="display:grid;grid-template-columns:1fr 1fr;gap:1px;background:var(--border-dim);">
        <div style="background:var(--bg0);"><div class="ph-sub"><span class="tag">CRYPTO</span></div><div id="scan-crypto"></div></div>
        <div style="background:var(--bg0);"><div class="ph-sub"><span class="tag">EQUITIES</span></div><div id="scan-stock"></div></div>
      </div>
    </div>
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">MARKET DEPTH | ORDER FLOW</span><span class="ph-meta">SIMULATED</span></div>
      <div style="display:grid;grid-template-columns:1fr 1fr;gap:1px;background:var(--border-dim);">
        <div style="background:var(--bg0);"><div class="ph-sub"><span style="color:var(--green)">ASK LADDER</span></div><div id="ask-ladder"></div></div>
        <div style="background:var(--bg0);"><div class="ph-sub"><span style="color:var(--red)">BID LADDER</span></div><div id="bid-ladder"></div></div>
      </div>
    </div>
    <div class="panel" style="flex:1;min-height:0;">
      <div class="ph"><span class="ph-title">NEWS &amp; ALERTS FEED</span><span class="ph-meta"><span id="news-cnt">0</span> items</span></div>
      <div style="padding:8px;border-bottom:1px solid var(--border);background:var(--bg1);">
        <select id="country-select" style="background:var(--bg2);color:var(--amber);border:1px solid var(--border);padding:4px;font-family:var(--font);font-size:10px;width:100%;margin-bottom:6px;">
          <option value="india">INDIA</option><option value="usa">USA</option><option value="uk">UK</option><option value="japan">JAPAN</option><option value="china">CHINA</option>
        </select>
        <div id="country-market-box" style="background:var(--bg0);border:1px solid var(--border);padding:6px;font-size:9px;line-height:1.6;color:var(--white);">Loading...</div>
      </div>
      <div class="mw-tbl-wrap" id="news-feed"></div>
    </div>
  </div>
  <div id="rcol">
    <div class="panel" style="flex:none;"><div class="ph"><span class="ph-title">DATA FEEDS</span></div><div id="feed-list"></div></div>
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">RISK METRICS v3</span></div>
      <div class="stat-grid">
        <div class="stat-cell"><div class="sl">MAX ALLOC</div><div class="sv">50%</div></div>
        <div class="stat-cell"><div class="sl">RISK/TRD</div><div class="sv">4%</div></div>
        <div class="stat-cell"><div class="sl">ATR SL</div><div class="sv">1.5×</div></div>
        <div class="stat-cell"><div class="sl">ATR TP1</div><div class="sv">2.0×</div></div>
        <div class="stat-cell"><div class="sl">ATR TP2</div><div class="sv">4.0×</div></div>
        <div class="stat-cell"><div class="sl">TRAIL</div><div class="sv">1.2×</div></div>
        <div class="stat-cell"><div class="sl">RESERVE</div><div class="sv">10%</div></div>
        <div class="stat-cell"><div class="sl">DEPLOY</div><div class="sv pos">90%</div></div>
        <div class="stat-cell"><div class="sl">COOLDOWN</div><div class="sv">2 cyc</div></div>
        <div class="stat-cell"><div class="sl">SIG EVERY</div><div class="sv">10s</div></div>
      </div>
    </div>
    <div class="panel" style="flex:1;min-height:0;">
      <div class="ph"><span class="ph-title">ALERT LOG</span><span class="ph-meta" id="al-cnt">0</span></div>
      <div class="mw-tbl-wrap" id="alert-log"></div>
    </div>
    <div class="panel" style="flex:none;">
      <div class="ph"><span class="ph-title">SYSTEM v3.0</span></div>
      <div style="padding:3px 6px;display:flex;flex-direction:column;gap:1px;">
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">VERSION</span><span style="color:var(--amber)">v3.0</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">CRYPTO BAL</span><span style="color:var(--green)">$6,500</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">STOCKS BAL</span><span style="color:var(--green)">$6,500</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">FACTORS</span><span style="color:var(--cyan)">11 | SCORE /14</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">DEPLOY</span><span style="color:var(--orange)">90%</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">RESERVE</span><span style="color:var(--white)">10%</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">SIGNAL</span><span style="color:var(--white)">10s</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">OHLCV</span><span style="color:var(--white)">60s</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;border-bottom:1px solid var(--bg2);"><span style="color:var(--gray-dim)">WEB PORT</span><span style="color:var(--blue-hi)">:5050</span></div>
        <div style="display:flex;justify-content:space-between;font-size:8px;padding:1px 0;"><span style="color:var(--gray-dim)">REF RATE</span><span style="color:var(--white)">2s</span></div>
      </div>
    </div>
  </div>
</div>
</div>
<div id="positions-page" style="display:none;height:100vh;background:var(--bg0);color:var(--white);overflow:auto;">
  <div style="padding:14px;border-bottom:1px solid var(--border);display:flex;align-items:center;justify-content:space-between;background:var(--bg1);position:sticky;top:0;z-index:100;">
    <div style="font-size:20px;color:var(--orange);font-weight:bold;letter-spacing:2px;">OPEN POSITIONS</div>
    <button id="back-dashboard" style="background:var(--bg3);border:1px solid var(--border);color:var(--white);padding:8px 14px;cursor:pointer;font-family:var(--font);">← BACK</button>
  </div>
  <div style="padding:16px;">
    <table class="pos-tbl" style="width:100%;">
      <thead><tr><th>SYMBOL</th><th>SIDE</th><th>ENTRY</th><th>CURRENT</th><th>P&L</th><th>STOP LOSS</th><th>TARGET</th><th>SIZE</th><th>RISK</th><th>STATUS</th></tr></thead>
      <tbody id="fullscreen-positions-table"></tbody>
    </table>
  </div>
</div>
<div id="world-page" style="display:none;height:100vh;max-height:100vh;background:var(--bg0);color:var(--white);overflow:hidden;flex-direction:column;">
  <div style="padding:10px 14px;border-bottom:1px solid var(--border);display:flex;align-items:center;justify-content:space-between;background:var(--bg1);flex-shrink:0;">
    <div style="font-size:16px;color:var(--cyan);font-weight:bold;letter-spacing:2px;">GLOBAL MARKET MAP</div>
    <div style="display:flex;align-items:center;gap:10px;">
      <span style="font-size:8px;color:var(--gray-dim);">CLICK A COUNTRY TO LOAD MARKET DATA</span>
      <button id="back-world" style="background:var(--bg3);border:1px solid var(--border);color:var(--white);padding:6px 12px;cursor:pointer;font-family:var(--font);font-size:9px;">← BACK</button>
    </div>
  </div>
  <div style="display:flex;flex:1;min-height:0;">
    <div id="world-map" style="flex:1;min-width:0;"></div>
    <div id="country-panel" style="width:220px;flex-shrink:0;background:var(--bg1);border-left:1px solid var(--border);display:flex;flex-direction:column;overflow:hidden;">
      <div style="background:var(--bg2);border-bottom:1px solid var(--border);padding:6px 10px;display:flex;align-items:center;justify-content:space-between;">
        <span style="font-size:8px;font-weight:bold;color:var(--gray);text-transform:uppercase;letter-spacing:1.5px;border-left:2px solid var(--orange);padding-left:4px;">MARKET DATA</span>
        <span id="panel-live-dot" style="font-size:7px;color:var(--gray-dark);">● SELECT</span>
      </div>
      <div id="country-panel-body" style="flex:1;overflow-y:scroll;min-height:0;">
        <div id="panel-default" style="padding:20px 12px;text-align:center;">
          <div style="font-size:24px;margin-bottom:8px;opacity:0.3;">🌍</div>
          <div style="font-size:8px;color:var(--gray-dark);line-height:1.6;">Click any country on the map to load live market data</div>
        </div>
        <div id="panel-loading" style="display:none;padding:20px 12px;text-align:center;">
          <div style="font-size:8px;color:var(--amber);" id="panel-loading-txt">LOADING...</div>
        </div>
        <div id="panel-data" style="display:none;flex-direction:column;">
          <div style="background:var(--bg2);border-bottom:1px solid var(--border);padding:8px 10px;">
            <div style="font-size:14px;font-weight:bold;color:var(--orange);letter-spacing:1px;" id="pd-country">--</div>
            <div style="font-size:8px;color:var(--gray-dim);margin-top:2px;" id="pd-index-name">--</div>
          </div>
          <div style="display:grid;grid-template-columns:1fr 1fr;gap:0;border-bottom:1px solid var(--border-dim);">
            <div style="padding:6px 8px;border-right:1px solid var(--border-dim);">
              <div style="font-size:7px;color:var(--gray-dark);text-transform:uppercase;margin-bottom:3px;">INDEX</div>
              <div style="font-size:15px;font-weight:bold;color:var(--green);font-variant-numeric:tabular-nums;" id="pd-index-val">--</div>
            </div>
            <div style="padding:6px 8px;display:flex;flex-direction:column;gap:3px;">
              <div style="display:flex;justify-content:space-between;align-items:center;"><span style="font-size:7px;color:var(--gray-dark);">GOLD</span><span style="font-size:8px;font-weight:bold;color:#ffd700;" id="pd-gold">--</span></div>
              <div style="display:flex;justify-content:space-between;align-items:center;"><span style="font-size:7px;color:var(--gray-dark);">SILVER</span><span style="font-size:8px;font-weight:bold;color:#c0c0c0;" id="pd-silver">--</span></div>
              <div style="display:flex;justify-content:space-between;align-items:center;"><span style="font-size:7px;color:var(--gray-dark);">CRUDE</span><span style="font-size:8px;font-weight:bold;color:var(--red);" id="pd-crude">--</span></div>
            </div>
          </div>
          <div style="padding:6px 8px 4px 8px;border-bottom:1px solid var(--border-dim);flex-shrink:0;"><div style="font-size:7px;color:var(--gray-dark);text-transform:uppercase;">LATEST NEWS</div></div>
          <div id="pd-news" style="overflow-y:scroll;flex:1;min-height:120px;max-height:340px;display:flex;flex-direction:column;"></div>
          <div style="padding:4px 8px;border-top:1px solid var(--border-dim);flex-shrink:0;"><div style="font-size:7px;color:var(--gray-dark);">FETCHED <span id="pd-time">--</span></div></div>
        </div>
        <div id="panel-error" style="display:none;padding:20px 12px;text-align:center;">
          <div style="font-size:10px;color:var(--red);margin-bottom:6px;">DATA UNAVAILABLE</div>
          <div style="font-size:8px;color:var(--gray-dark);" id="panel-error-txt">Could not load market data.</div>
        </div>
      </div>
    </div>
  </div>
</div>
<div id="statusbar">
  <span class="sb-lbl">UPTIME</span><span class="sb-val" id="sb-uptime">--</span>
  <span class="sb-lbl">│</span><span class="sb-lbl">REFRESHES</span><span class="sb-val" id="sb-ref">0</span>
  <span class="sb-lbl">│</span><span class="sb-lbl">LAST</span><span class="sb-val" id="sb-last">--</span>
  <span class="sb-lbl">│</span><span class="sb-ok">● ALGO ACTIVE</span>
  <span class="sb-lbl">│</span><span class="sb-lbl">v3.0 — 11 FACTORS | 90% DEPLOYED | $6.5K+$6.5K</span>
  <span class="sb-right">CTRL+C TO QUIT | 1-6 MANUAL CRYPTO CLOSE | WEB UI :5050</span>
</div>
<script>
const charts={},prevPx={},alerts=[],newsItems=[];
let refreshN=0,lastData=null,prevTrades={c:0,s:0};
const startTs=Date.now();
const f2=n=>Number(n).toFixed(2);
const f4=n=>Number(n).toFixed(4);
const fUSD=(n,d=2)=>'$'+Number(n).toLocaleString('en-US',{minimumFractionDigits:d,maximumFractionDigits:d});
const fPct=n=>(n>=0?'+':'')+Number(n).toFixed(3)+'%';
const fPct2=n=>(n>=0?'+':'')+Number(n).toFixed(2)+'%';
const elapsed=ms=>{const s=Math.floor(ms/1000),m=Math.floor(s/60),h=Math.floor(m/60);return`${String(h).padStart(2,'0')}:${String(m%60).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`;};
const t2=()=>new Date().toLocaleTimeString('en-US',{hour12:false,hour:'2-digit',minute:'2-digit'});
function buildMini(id,prices,up){const ctx=document.getElementById(id);if(!ctx||!prices||prices.length<2)return;if(charts[id]){charts[id].destroy();}const col=up?'#5cb85c':'#d9534f';charts[id]=new Chart(ctx.getContext('2d'),{type:'line',data:{labels:prices.map((_,i)=>i),datasets:[{data:prices,borderColor:col,borderWidth:1,pointRadius:0,tension:0.1,fill:{target:'origin',above:up?'rgba(92,184,92,0.06)':'rgba(0,0,0,0)',below:up?'rgba(0,0,0,0)':'rgba(217,83,79,0.06)'}}]},options:{animation:false,responsive:true,maintainAspectRatio:false,plugins:{legend:{display:false},tooltip:{enabled:false}},scales:{x:{display:false},y:{display:false}}}});}
function renderTicker(d){let html='';Object.entries(d.crypto.COIN).forEach(([n,c])=>{if(!c||!c.price)return;const pct=c.prices&&c.prices.length>1?(c.prices[c.prices.length-1]-c.prices[0])/c.prices[0]*100:0;const up=pct>=0;html+=`<span class="ti"><span class="ti-s">${n.toUpperCase()}</span><span class="ti-p">${fUSD(c.price,4)}</span><span class="ti-c ${up?'up':'dn'}"> ${up?'▲':'▼'}${fPct2(pct)}</span></span>`;});html+=`<span class="ti" style="color:var(--border-hi)">◆</span>`;Object.entries(d.stocks.COIN).forEach(([n,s])=>{if(!s||!s.price)return;const pct=s.prices&&s.prices.length>1?(s.prices[s.prices.length-1]-s.prices[0])/s.prices[0]*100:0;const up=pct>=0;html+=`<span class="ti"><span class="ti-s">${n.toUpperCase()}</span><span class="ti-p">${fUSD(s.price,2)}</span><span class="ti-c ${up?'up':'dn'}"> ${up?'▲':'▼'}${fPct2(pct)}</span></span>`;});document.getElementById('tick-inner').innerHTML=html+html;}
function mwRow(id,sym,score,price,prices,pos,isCrypto){const prev=prevPx[id];const dec=isCrypto?4:2;const pct=prices&&prices.length>1?(prices[prices.length-1]-prices[0])/prices[0]*100:0;const up=pct>=0;let tr=document.getElementById('tr-'+id);const isNew=!tr;if(isNew){tr=document.createElement('tr');tr.id='tr-'+id;}const dir=prev==null?'flat':price>prev?'up':price<prev?'dn':'flat';if(dir!=='flat'){tr.classList.remove('fl-up','fl-dn');void tr.offsetWidth;tr.classList.add(dir==='up'?'fl-up':'fl-dn');}prevPx[id]=price;const posStr=pos?`<td class="${pos.side}">${pos.side.toUpperCase()}</td><td class="num dim">${fUSD(pos.entry,dec)}</td><td class="num dim">${fUSD(pos.sl||0,dec)}</td><td class="num dim">${fUSD(pos.tp||0,dec)}</td><td class="num ${pos.pnl_pct>=0?'up':'dn'}">${fPct2(pos.pnl_pct)}</td>`:`<td class="dim">--</td><td class="dim">--</td><td class="dim">--</td><td class="dim">--</td><td class="dim">--</td>`;const sig=pos?(pos.side==='long'?`<td class="long">▲LONG</td>`:`<td class="short">▼SHORT</td>`):`<td class="dim">WAIT</td>`;tr.innerHTML=`<td class="sym">${sym.toUpperCase()}</td><td class="px" id="px-${id}">${price?fUSD(price,dec):'--'}</td><td class="${up?'up':'dn'} num">${fPct2(pct)}</td><td class="sc">${score||0}/14</td>${sig}${posStr}<td class="spark-cell"><canvas id="cv-${id}" width="52" height="18"></canvas></td>`;if(isNew)return tr;return null;}
function renderMW(d){const ctbody=document.getElementById('crypto-mw-tbody');const stbody=document.getElementById('stock-mw-tbody');Object.entries(d.crypto.COIN).forEach(([n,c])=>{const id='c-'+n;const tr=mwRow(id,n,c.score,c.price,c.prices,c.position,true);if(tr)ctbody.appendChild(tr);setTimeout(()=>buildMini('cv-'+id,c.prices,c.prices&&c.prices.length>1&&c.prices[c.prices.length-1]>=c.prices[0]),50);});Object.entries(d.stocks.COIN).forEach(([n,s])=>{const id='s-'+n;const tr=mwRow(id,n,s.score,s.price,s.prices,s.position,false);if(tr)stbody.appendChild(tr);setTimeout(()=>buildMini('cv-'+id,s.prices,s.prices&&s.prices.length>1&&s.prices[s.prices.length-1]>=s.prices[0]),50);});}
function renderPositions(d){const rows=[];Object.entries(d.crypto.COIN).forEach(([n,c])=>{if(c.position)rows.push({sym:n.toUpperCase()+'/USD',...c.position,isCrypto:true});});Object.entries(d.stocks.COIN).forEach(([n,s])=>{if(s.position)rows.push({sym:n.toUpperCase(),...s.position,isCrypto:false});});const dec=r=>r.isCrypto?4:2;document.getElementById('pos-tbody').innerHTML=rows.length?rows.map(r=>`<tr><td class="sym">${r.sym}</td><td class="${r.side}">${r.side.toUpperCase()}</td><td class="num">${fUSD(r.entry,dec(r))}</td><td class="num">${r.price?fUSD(r.price,dec(r)):'--'}</td><td class="num ${r.pnl_pct>=0?'up':'dn'}">${fPct2(r.pnl_pct)}</td><td class="num dim">${fUSD(r.sl||0,dec(r))}</td><td class="num dim">${fUSD(r.tp||0,dec(r))}</td><td class="${r.partial_done?'up':'dim'}">${r.partial_done?'50% LK':'--'}</td></tr>`).join(''):`<tr><td colspan="8" style="text-align:center;color:var(--gray-dark);padding:6px">NO OPEN POSITIONS</td></tr>`;const cnt=rows.length;document.getElementById('pos-cnt').textContent=cnt+' open';document.getElementById('sb-pos').textContent=cnt;document.getElementById('ac-op').textContent=cnt;document.getElementById('fullscreen-positions-table').innerHTML=rows.length?rows.map(r=>`<tr><td class="sym">${r.sym}</td><td class="${r.side}">${r.side.toUpperCase()}</td><td>${fUSD(r.entry,r.isCrypto?4:2)}</td><td>${r.price?fUSD(r.price,r.isCrypto?4:2):'--'}</td><td class="${r.pnl_pct>=0?'up':'dn'}">${fPct2(r.pnl_pct)}</td><td>${fUSD(r.sl||0,r.isCrypto?4:2)}</td><td>${fUSD(r.tp||0,r.isCrypto?4:2)}</td><td>--</td><td>4%</td><td style="color:var(--green)">ACTIVE</td></tr>`).join(''):`<tr><td colspan="10" style="text-align:center;padding:30px;color:var(--gray-dark);">NO OPEN POSITIONS</td></tr>`;}
function renderScanner(d){const cc=[],sc=[];Object.entries(d.crypto.COIN).forEach(([n,c])=>cc.push({sym:n.toUpperCase(),score:c.score||0,side:c.signal||null}));Object.entries(d.stocks.COIN).forEach(([n,s])=>sc.push({sym:n.toUpperCase(),score:s.score||0,side:s.signal||null}));cc.sort((a,b)=>b.score-a.score);sc.sort((a,b)=>b.score-a.score);const row=a=>`<div class="scan-row"><span class="sc-sym">${a.sym}</span><div class="sc-bar"><div class="sc-fill ${a.side==='long'?'bull':a.side==='short'?'bear':'bull'}" style="width:${Math.round(a.score/14*100)}%"></div></div><span class="sc-score">${a.score}/14</span><span class="sc-side ${a.side||'none'}">${a.side?a.side.toUpperCase():'WAIT'}</span></div>`;document.getElementById('scan-crypto').innerHTML=cc.map(row).join('');document.getElementById('scan-stock').innerHTML=sc.map(row).join('');const active=cc.filter(a=>a.side).length+sc.filter(a=>a.side).length;document.getElementById('sb-sigs').textContent=active;}
function renderOrderBook(d){const prices=Object.values(d.crypto.COIN).filter(c=>c.price).map(c=>c.price);if(!prices.length)return;const mid=prices[0];const ask=[],bid=[];for(let i=0;i<5;i++){const spread=(0.001+i*0.0008+Math.random()*0.0003)*mid;const size=(Math.random()*2+0.2).toFixed(3);const barW=Math.min(100,Math.round(parseFloat(size)/3*100));ask.push(`<div style="display:flex;gap:3px;align-items:center;padding:1px 5px;border-bottom:1px solid var(--bg2);font-size:8px;"><span style="color:var(--red);width:60px;text-align:right;font-variant-numeric:tabular-nums">${fUSD(mid+spread,2)}</span><div style="flex:1;height:3px;background:var(--bg3);position:relative;overflow:hidden"><div style="position:absolute;right:0;top:0;height:100%;width:${barW}%;background:var(--red-dim)"></div></div><span style="color:var(--gray-dim);width:36px;text-align:right">${size}</span></div>`);bid.push(`<div style="display:flex;gap:3px;align-items:center;padding:1px 5px;border-bottom:1px solid var(--bg2);font-size:8px;"><span style="color:var(--green);width:60px;font-variant-numeric:tabular-nums">${fUSD(mid-spread,2)}</span><div style="flex:1;height:3px;background:var(--bg3);position:relative;overflow:hidden"><div style="position:absolute;left:0;top:0;height:100%;width:${barW}%;background:var(--green-dim)"></div></div><span style="color:var(--gray-dim);width:36px;text-align:right">${size}</span></div>`);}document.getElementById('ask-ladder').innerHTML=ask.reverse().join('');document.getElementById('bid-ladder').innerHTML=bid.join('');}
function renderFeeds(d){const feeds=[{n:'CRYPTO OHLCV',s:'YFINANCE 1m',ok:true},{n:'US STOCKS',s:'YFINANCE 1m',ok:d.stocks.session!=='closed'},{n:'SIGNAL ENG',s:'11-FACTOR',ok:true},{n:'RISK MGR',s:'90% DEPLOY',ok:true},{n:'STATE SAVE',s:'AUTO 5m',ok:true},{n:'WEB SERVER',s:':5050 HTTP',ok:true},{n:'ALGO THREAD',s:'10s CYCLE',ok:true},{n:'OHLCV CACHE',s:'1s REFRESH',ok:true}];document.getElementById('feed-list').innerHTML=feeds.map(f=>`<div class="feed-row"><div class="feed-dot ${f.ok?'ok':'warn'}"></div><span class="feed-name">${f.n}</span><span class="feed-st ${f.ok?'ok':''}">${f.s}</span></div>`).join('');}
function renderTrades(d){const ct=(d.crypto.trades||[]).filter(t=>!t.partial).slice(-30).reverse();const st=(d.stocks.trades||[]).filter(t=>!t.partial).slice(-30).reverse();const trow=(t,d)=>`<tr><td class="dim">${t.time}</td><td class="sym">${(t.coin||t.ticker||'').toUpperCase()}</td><td class="${t.side}">${t.side.toUpperCase()}</td><td class="num dim">${fUSD(t.entry,d)}</td><td class="num dim">${fUSD(t.exit,d)}</td><td class="num ${t.pnl>=0?'up':'dn'}">${fPct(t.pct)}</td><td class="reason">${t.reason}</td></tr>`;const none=`<tr><td colspan="7" style="text-align:center;color:var(--gray-dark);padding:6px">NO FILLS</td></tr>`;document.getElementById('crypto-fills').innerHTML=ct.length?ct.map(t=>trow(t,4)).join(''):none;document.getElementById('stock-fills').innerHTML=st.length?st.map(t=>trow(t,2)).join(''):none;document.getElementById('trade-cnt').textContent=(ct.length+st.length)+' fills';document.getElementById('st-fills').textContent=ct.length+st.length;}
function pushAlert(sym,msg,type='info'){alerts.unshift({t:t2(),sym,msg,type});if(alerts.length>100)alerts.pop();renderAlerts();}
function renderAlerts(){document.getElementById('alert-log').innerHTML=alerts.slice(0,50).map(a=>`<div class="al-row ${a.type}"><span class="al-t">${a.t}</span><span class="al-s">${a.sym}</span><span class="al-m">${a.msg}</span></div>`).join('');document.getElementById('al-cnt').textContent=alerts.length;}
const staticNews=[{t:'--:--',sym:'FED',h:'Fed officials signal data-dependent approach to rate decisions through 2025',type:'brk'},{t:'--:--',sym:'NVDA',h:'Nvidia data center revenue surpasses expectations on AI demand surge',type:'pos'},{t:'--:--',sym:'BTC',h:'Institutional crypto inflows reach multi-month high via ETF products',type:'pos'},{t:'--:--',sym:'TSLA',h:'Tesla delivery figures miss analyst estimates for second consecutive quarter',type:'neg'},{t:'--:--',sym:'MACRO',h:'US CPI data shows inflation cooling toward Fed 2% target range',type:''},{t:'--:--',sym:'SOL',h:'Solana network activity records highest daily transactions since 2022',type:'pos'}];
function initNews(){const now=new Date();staticNews.forEach((n,i)=>{const d=new Date(now-i*600000);n.t=d.toLocaleTimeString('en-US',{hour12:false,hour:'2-digit',minute:'2-digit'});});document.getElementById('news-feed').innerHTML=staticNews.map(n=>`<div class="news-row ${n.type}"><span class="news-t">${n.t}</span><span class="news-s">${n.sym}</span><span class="news-h">${n.h}</span></div>`).join('');document.getElementById('news-cnt').textContent=staticNews.length;}
function detectNewTrades(d){const ct=(d.crypto.trades||[]).filter(t=>!t.partial);const st=(d.stocks.trades||[]).filter(t=>!t.partial);if(ct.length>prevTrades.c){const t=ct[ct.length-1];pushAlert(t.coin.toUpperCase(),`${t.side.toUpperCase()} CLOSED ${fPct(t.pct)} [${t.reason}]`,t.pnl>=0?'buy':'sell');prevTrades.c=ct.length;}if(st.length>prevTrades.s){const t=st[st.length-1];pushAlert(t.ticker.toUpperCase(),`${t.side.toUpperCase()} CLOSED ${fPct(t.pct)} [${t.reason}]`,t.pnl>=0?'buy':'sell');prevTrades.s=st.length;}}
async function refresh(){const t0=Date.now();try{const d=await fetch('/data').then(r=>r.json());const lat=Date.now()-t0;lastData=d;refreshN++;const now=new Date();document.getElementById('sys-clock').textContent=now.toLocaleTimeString('en-US',{hour12:false});document.getElementById('sb-lat').textContent=lat+'ms';document.getElementById('sb-ref').textContent=refreshN;document.getElementById('fk-ref').textContent=refreshN;document.getElementById('sb-last').textContent=now.toLocaleTimeString('en-US',{hour12:false});document.getElementById('sb-uptime').textContent=elapsed(Date.now()-startTs);document.getElementById('fk-uptime').textContent=elapsed(Date.now()-startTs);document.getElementById('pf-time').textContent=now.toLocaleTimeString('en-US',{hour12:false});const ceq=d.crypto.equity,cpnl=d.crypto.pnl;const seq=d.stocks.equity,spnl=d.stocks.pnl;const cw=d.crypto.wins,cl=d.crypto.losses;const sw=d.stocks.wins,sl2=d.stocks.losses;const allW=cw+sw,allL=cl+sl2;const wr=allW+allL>0?Math.round(allW/(allW+allL)*100):0;const teq=ceq+seq,tpnl=cpnl+spnl;const setVal=(id,v,pnl)=>{const el=document.getElementById(id);el.textContent=v;if(pnl!==undefined){el.className='acct-val '+(pnl>=0?'pos':'neg');}};setVal('ac-ceq',fUSD(ceq));setVal('ac-cpnl',(cpnl>=0?'+':'')+fUSD(Math.abs(cpnl)),cpnl);document.getElementById('ac-cwl').textContent=cw+'W/'+cl+'L';setVal('ac-seq',fUSD(seq));setVal('ac-spnl',(spnl>=0?'+':'')+fUSD(Math.abs(spnl)),spnl);document.getElementById('ac-swl').textContent=sw+'W/'+sl2+'L';setVal('ac-teq',fUSD(teq));document.getElementById('ac-wr').textContent=wr+'%';document.getElementById('st-teq').textContent=fUSD(teq);const tpEl=document.getElementById('st-tpnl');tpEl.textContent=(tpnl>=0?'+':'')+fUSD(Math.abs(tpnl));tpEl.className='sv '+(tpnl>=0?'pos':'neg');document.getElementById('st-wr').textContent=wr+'%';document.getElementById('st-cbal').textContent=fUSD(d.crypto.balance);document.getElementById('st-sbal').textContent=fUSD(d.stocks.balance);const sess=d.stocks.session;const mb=document.getElementById('mkt-status');const sl=document.getElementById('sess-tag');if(sess==='core'){mb.innerHTML='● CORE 09:30–16:00';mb.className='mkt-core';sl.textContent='CORE HOURS';sl.style.color='var(--green)';}else if(sess==='extended'){mb.innerHTML='◉ EXTENDED 04:00–20:00';mb.className='mkt-ext';sl.textContent='EXTENDED';sl.style.color='var(--amber)';}else{mb.innerHTML='○ CLOSED';mb.className='mkt-closed';sl.textContent='CLOSED';sl.style.color='var(--gray-dim)';}renderMW(d);renderTicker(d);renderPositions(d);renderScanner(d);renderFeeds(d);renderTrades(d);renderOrderBook(d);detectNewTrades(d);}catch(e){pushAlert('SYS','Fetch error: '+e.message,'warn');}setTimeout(refresh,2000);}
setInterval(()=>{const t=new Date().toLocaleTimeString('en-US',{hour12:false});document.getElementById('sys-clock').textContent=t;document.getElementById('pf-time').textContent=t;document.getElementById('fk-uptime').textContent=elapsed(Date.now()-startTs);document.getElementById('sb-uptime').textContent=elapsed(Date.now()-startTs);},1000);
let worldMap=null,panelCountry=null;
const CODE_MAP={'IN':'india','US':'usa','GB':'uk','JP':'japan','CN':'china','DE':'germany','FR':'france','AU':'australia','CA':'canada','BR':'brazil','KR':'south korea','HK':'hong kong','SG':'singapore','CH':'switzerland','NL':'netherlands','ES':'spain','IT':'italy','SE':'sweden','NO':'norway','DK':'denmark','MX':'mexico','AR':'argentina','RU':'russia','TR':'turkey','SA':'saudi arabia','ZA':'south africa','ID':'indonesia','MY':'malaysia','TH':'thailand','PK':'pakistan','NZ':'new zealand','TW':'taiwan','IL':'israel','PT':'portugal','PL':'poland','AT':'austria','BE':'belgium','FI':'finland','IE':'ireland','EG':'egypt','NG':'nigeria','KE':'kenya','CL':'chile','CO':'colombia','PE':'peru','BD':'bangladesh','LK':'sri lanka','VN':'vietnam','PH':'philippines','GR':'greece','CZ':'czech republic','HU':'hungary','RO':'romania','UA':'ukraine','QA':'qatar','AE':'uae','KW':'kuwait','BH':'bahrain'};
function panelShow(state){['default','loading','data','error'].forEach(s=>{document.getElementById('panel-'+s).style.display=s===state?'block':'none';});}
async function loadCountryPanel(code){const country=CODE_MAP[code];if(!country){panelShow('error');document.getElementById('panel-error-txt').textContent='No data for this region.';return;}panelCountry=country;panelShow('loading');document.getElementById('panel-loading-txt').textContent='LOADING '+country.toUpperCase()+'...';try{const r=await fetch('/country-data?country='+country);if(!r.ok)throw new Error('HTTP '+r.status);const data=await r.json();if(data.error)throw new Error(data.error);document.getElementById('pd-country').textContent=country.toUpperCase();document.getElementById('pd-index-name').textContent=(data.index&&data.index.name)?data.index.name:'--';document.getElementById('pd-index-val').textContent=(data.index&&data.index.price!=null)?Number(data.index.price).toLocaleString('en-US',{maximumFractionDigits:2}):'N/A';const fmt=v=>v!=null?'$'+Number(v).toFixed(2):'--';document.getElementById('pd-gold').textContent=fmt(data.gold);document.getElementById('pd-silver').textContent=fmt(data.silver);document.getElementById('pd-crude').textContent=fmt(data.crude);const newsEl=document.getElementById('pd-news');if(data.news&&data.news.length){newsEl.innerHTML=data.news.slice(0,10).map(n=>{const title=(n.title||'').replace(/\s-\s[^-]*$/,'');const src=n.source||'';const url=n.url||'#';const time=n.time?new Date(n.time).toLocaleTimeString('en-US',{hour12:false,hour:'2-digit',minute:'2-digit'}):'';return`<a href="${url}" target="_blank" rel="noopener" style="display:block;padding:5px 8px;border-bottom:1px solid var(--bg2);text-decoration:none;" onmouseover="this.style.background='var(--bg3)'" onmouseout="this.style.background='transparent'"><div style="display:flex;justify-content:space-between;margin-bottom:2px;"><span style="font-size:7px;color:var(--cyan);font-weight:bold;">${src}</span><span style="font-size:7px;color:var(--gray-dark);">${time}</span></div><div style="font-size:8px;color:var(--gray);line-height:1.4;">${title}</div><div style="font-size:7px;color:var(--blue-hi);margin-top:2px;">READ MORE →</div></a>`;}).join('');}else{newsEl.innerHTML='<div style="padding:10px 8px;font-size:7px;color:var(--gray-dark);">No news available</div>';}document.getElementById('pd-time').textContent=new Date().toLocaleTimeString('en-US',{hour12:false});panelShow('data');document.getElementById('panel-live-dot').textContent='● LIVE';document.getElementById('panel-live-dot').style.color='var(--green)';}catch(e){panelShow('error');document.getElementById('panel-error-txt').textContent='Failed: '+e.message;}}
function initWorldMap(){if(worldMap)return;worldMap=new jsVectorMap({selector:'#world-map',map:'world',zoomButtons:true,backgroundColor:'#05070b',regionStyle:{initial:{fill:'#1a2330',stroke:'#2b3a4d',strokeWidth:1},hover:{fill:'#2e4a6b',cursor:'pointer'},selected:{fill:'#1a3a6b'}},onRegionClick(event,code){loadCountryPanel(code);}});}
initNews();
pushAlert('SYS','Terminal v3.0 initialized — 11-factor algo | $6.5K + $6.5K | 90% deployed','info');
pushAlert('RISK','SL=1.5×ATR | TP1=2.0× | TP2=4.0× | TRAIL=1.2× | RISK/TRADE=4%','info');
pushAlert('ALGO','Factors: EMA·RSI·MACD·BB·STOCH·ADX·CMF·VWAP·SUPERTREND·ROC·E200','info');
document.getElementById('tab-f1').onclick=function(){document.getElementById('positions-page').style.display='none';document.getElementById('world-page').style.display='none';document.getElementById('dashboard-page').style.display='block';document.querySelectorAll('.fk').forEach(b=>b.classList.remove('active'));this.classList.add('active');window.scrollTo({top:0,behavior:'smooth'});};
document.getElementById('tab-f2').onclick=function(){document.getElementById('dashboard-page').style.display='none';document.getElementById('world-page').style.display='none';document.getElementById('positions-page').style.display='block';};
document.getElementById('back-dashboard').onclick=function(){document.getElementById('positions-page').style.display='none';document.getElementById('dashboard-page').style.display='block';};
document.getElementById('back-world').onclick=function(){document.getElementById('world-page').style.display='none';document.getElementById('dashboard-page').style.display='block';};
document.getElementById('tab-f5').onclick=function(){document.querySelectorAll('.fk').forEach(b=>b.classList.remove('active'));this.classList.add('active');};
document.getElementById('tab-f6').onclick=function(){document.getElementById('dashboard-page').style.display='none';document.getElementById('positions-page').style.display='none';document.getElementById('world-page').style.display='block';initWorldMap();};
async function loadCountryMarket(country="india"){try{const r=await fetch(`/country-data?country=${country}`);const data=await r.json();document.getElementById("country-market-box").innerHTML=`<div style="color:var(--amber);font-weight:bold;margin-bottom:6px;">${data.country?data.country.toUpperCase():country.toUpperCase()} MARKET</div><div>INDEX: <span style="color:var(--green)">${data.index&&data.index.price!=null?data.index.name+' '+Number(data.index.price).toLocaleString('en-US',{maximumFractionDigits:2}):'N/A'}</span></div><div>GOLD: <span style="color:var(--amber)">${data.gold!=null?'$'+Number(data.gold).toFixed(2):'--'}</span></div><div>SILVER: <span style="color:#c0c0c0">${data.silver!=null?'$'+Number(data.silver).toFixed(2):'--'}</span></div><div>CRUDE: <span style="color:var(--red)">${data.crude!=null?'$'+Number(data.crude).toFixed(2):'--'}</span></div>`;}catch(err){document.getElementById("country-market-box").innerHTML="FAILED TO LOAD MARKET DATA";}}
document.getElementById("country-select").addEventListener("change",e=>{loadCountryMarket(e.target.value);});
loadCountryMarket();
refresh();
</script>
</body>
</html>
'''


class _SafeEncoder(json.JSONEncoder):
    def encode(self, obj):
        import math
        def fix(o):
            if isinstance(o, float):
                return None if (math.isnan(o) or math.isinf(o)) else o
            if isinstance(o, dict): return {k: fix(v) for k, v in o.items()}
            if isinstance(o, list): return [fix(v) for v in o]
            return o
        return super().encode(fix(obj))


class _Handler(BaseHTTPRequestHandler):
    def log_message(self, *args): pass

    def do_GET(self):
        if self.path == "/":
            body = HTML.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif self.path.startswith("/country-data"):
            try:
                from urllib.parse import urlparse, parse_qs
                query = parse_qs(urlparse(self.path).query)
                country = query.get("country", ["india"])[0]
                body = json.dumps(get_country_market_data(country), cls=_SafeEncoder).encode()
            except Exception as e:
                body = json.dumps({"error": str(e)}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif self.path == "/data":
            try:
                ceq   = total_equity()
                seq   = stock_total_equity()
                cwins = sum(1 for t in trades       if t["pnl"] > 0  and not t.get("partial"))
                closs = sum(1 for t in trades       if t["pnl"] <= 0 and not t.get("partial"))
                swins = sum(1 for t in stock_trades if t["pnl"] > 0  and not t.get("partial"))
                sloss = sum(1 for t in stock_trades if t["pnl"] <= 0 and not t.get("partial"))
                payload = {
                    "crypto": {
                        "balance": balance, "equity": ceq,
                        "pnl": ceq - STARTING_BALANCE,
                        "wins": cwins, "losses": closs,
                        "trades": trades[-30:], "COIN": {},
                    },
                    "stocks": {
                        "balance": stock_balance, "equity": seq,
                        "pnl": seq - STOCK_BALANCE,
                        "wins": swins, "losses": sloss,
                        "market_open": market_open(),
                        "session": market_session(),
                        "trades": stock_trades[-30:], "COIN": {},
                    },
                    "news": live_news,
                }
                for coin, name in COIN.items():
                    pos = states[coin]["position"]
                    payload["crypto"]["COIN"][name] = {
                        "prices": states[coin]["chart_prices"],
                        "price": last_prices.get(coin),
                        "score": states[coin]["score"],
                        "position": {
                            "side": pos["side"], "entry": pos["entry"],
                            "sl": pos.get("trail_sl"), "tp": pos.get("tp2"),
                            "pnl_pct": unrealised_pct(coin, last_prices.get(coin))
                        } if pos else None,
                    }
                for ticker, name in STOCKS.items():
                    pos = stock_states[ticker]["position"]
                    payload["stocks"]["COIN"][name] = {
                        "prices": stock_states[ticker]["chart_prices"],
                        "price": stock_prices.get(ticker),
                        "score": stock_states[ticker]["score"],
                        "position": {
                            "side": pos["side"], "entry": pos["entry"],
                            "sl": pos.get("trail_sl"), "tp": pos.get("tp2"),
                            "pnl_pct": stock_unrealised_pct(ticker, stock_prices.get(ticker))
                        } if pos else None,
                    }
                body = json.dumps(payload, cls=_SafeEncoder).encode()
            except Exception as e:
                body = json.dumps({"error": str(e)}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)


def run_web():
    HTTPServer(("", WEB_PORT), _Handler).serve_forever()


def main():
    load_state()
    load_stock_state()
    threading.Thread(target=keyboard_listener,      daemon=True).start()
    threading.Thread(target=background_fetch,       daemon=True).start()
    threading.Thread(target=stock_background_fetch, daemon=True).start()
    threading.Thread(target=binance_ws_thread,   daemon=True).start()
    threading.Thread(target=autosave_loop,          daemon=True).start()
    threading.Thread(target=run_web,                daemon=True).start()
    threading.Thread(target=fetch_live_news,        daemon=True).start()

    time.sleep(4)
    crypto_tick = 0
    stock_tick  = 0
    with Live(make_layout(), refresh_per_second=1, screen=True) as live:
        while True:
            for coin in list(manual_close):
                if manual_close.pop(coin, False) and states[coin]["position"]:
                    close_pos(coin, last_prices[coin], "manual")
            check_sl_tp()
            check_stock_sl_tp()
            crypto_tick += 1
            if crypto_tick >= SIGNAL_EVERY:
                check_signals()
                crypto_tick = 0
            stock_tick += 1
            if stock_tick >= STOCK_SIGNAL_EVERY:
                check_stock_signals()
                stock_tick = 0
            live.update(make_layout())
            time.sleep(1)


if __name__ == "__main__":
    main()
