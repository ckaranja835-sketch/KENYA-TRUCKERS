#!/usr/bin/env python3
"""
KENYA TRUCKERS SIMULATOR  -  server
ACE SYNAPSE TECHNOLOGIES

Run:   python app.py
Open:  http://127.0.0.1:5000

Requires: Flask   (pip install flask)   -- everything else is the standard library.
"""

# =============================================================================
# CONFIGURATION
# =============================================================================
import os, re, json, time, math, random, sqlite3, hashlib, secrets
from flask import Flask, request, jsonify, g, send_file, abort

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "kenya_truckers.db")
INDEX_PATH = os.path.join(BASE_DIR, "index.html")

WORLD_SCALE = 0.1            # game road length / real road length (sent to client)
PAY_PER_KM = 160             # KSh per real km before cargo/difficulty multipliers
START_MONEY = 25000
SELL_RATIO = 0.60
JOB_WINDOW_S = 900           # job board re-rolls every 15 minutes
MAX_FLEET = 40

app = Flask(__name__)
app.config["JSON_SORT_KEYS"] = False

# =============================================================================
# CATALOG (single source of truth for prices, stats, cargo, routes)
# =============================================================================
# node id -> (display name, city, fuel, garage, dealer, depot)
NODES = {
    "nairobi":      ("Nairobi CBD",                "nairobi", 1, 0, 0, 1),
    "nairobi_ind":  ("Nairobi Industrial Area",    "nairobi", 1, 1, 1, 1),
    "kikuyu":       ("Kikuyu",                     None,      1, 0, 0, 0),
    "limuru":       ("Limuru",                     None,      1, 1, 0, 0),
    "kijabe":       ("Kijabe",                     None,      0, 0, 0, 0),
    "naivasha":     ("Naivasha",                   None,      1, 1, 0, 0),
    "gilgil":       ("Gilgil",                     None,      1, 0, 0, 0),
    "lanet":        ("Lanet (Nakuru East)",        "nakuru",  0, 0, 0, 1),
    "nakuru":       ("Nakuru",                     "nakuru",  1, 1, 1, 1),
    "salgaa":       ("Salgaa",                     None,      1, 0, 0, 0),
    "maus":         ("Mau Summit",                 None,      0, 0, 0, 0),
    "timboroa":     ("Timboroa",                   None,      1, 0, 0, 0),
    "burnt":        ("Burnt Forest",               None,      0, 0, 0, 0),
    "eld_ind":      ("Eldoret Industrial (Kipkenyo)", "eldoret", 0, 0, 0, 1),
    "eldoret":      ("Eldoret",                    "eldoret", 1, 1, 1, 1),
    "athiriver":    ("Athi River",                 None,      1, 1, 0, 0),
    "sultanhamud":  ("Sultan Hamud",               None,      0, 0, 0, 0),
    "emali":        ("Emali",                      None,      1, 0, 0, 0),
    "kibwezi":      ("Kibwezi",                    None,      1, 0, 0, 0),
    "mtitoandei":   ("Mtito Andei",                None,      1, 0, 0, 0),
    "voi":          ("Voi",                        None,      1, 1, 0, 0),
    "mackinnon":    ("Mackinnon Road",             None,      1, 0, 0, 0),
    "mariakani":    ("Mariakani",                  None,      1, 0, 0, 0),
    "changamwe":    ("Changamwe",                  "mombasa", 0, 0, 0, 1),
    "mombasa":      ("Mombasa",                    "mombasa", 1, 1, 1, 1),
}
FUEL_PRICE = {"mombasa": 176, "changamwe": 176, "nairobi": 178, "nairobi_ind": 178,
              "nakuru": 181, "eldoret": 184, "voi": 182}

# city id -> (name, depot node, tutorial destination node, region blurb)
CITIES = {
    "nairobi": ("Nairobi", "nairobi_ind", "nairobi",  "Capital hub: heavy urban traffic, Uhuru Highway roundabout, Industrial Area yards."),
    "nakuru":  ("Nakuru",  "nakuru",      "lanet",    "Rift Valley town: dry plains, flamingo lake country, A104 gateway west."),
    "eldoret": ("Eldoret", "eldoret",     "eld_ind",  "Highland farm capital: maize, wheat, cool air and rolling farmland."),
    "mombasa": ("Mombasa", "mombasa",     "changamwe","Coastal port city: palms, heat, container traffic and the Makupa causeway."),
}

# approximate real road distances (km) between the four depot cities
_REAL = {("nairobi", "nakuru"): 156, ("nakuru", "eldoret"): 157, ("nairobi", "eldoret"): 313,
         ("nairobi", "mombasa"): 485, ("nakuru", "mombasa"): 641, ("eldoret", "mombasa"): 798}
def real_km(a, b):
    return _REAL.get((a, b)) or _REAL.get((b, a)) or 0
ROUTE_DIFFICULTY = {frozenset(("nairobi", "nakuru")): 2, frozenset(("nakuru", "eldoret")): 3,
                    frozenset(("nairobi", "eldoret")): 3, frozenset(("nairobi", "mombasa")): 3,
                    frozenset(("nakuru", "mombasa")): 4, frozenset(("eldoret", "mombasa")): 5}

# id, make, model, hp, torque Nm, empty kg, tank L, price KSh, L/100km, brake, handling, turn radius m, cab, min level
_T = [
    ("volvo_fm370", "Volvo", "FM 370", 370, 1850, 7300, 450, 210000, 29, 0.95, 1.00, 9.6, "day", 1),
    ("volvo_fh420", "Volvo", "FH 420", 420, 2100, 7900, 600, 430000, 30, 1.00, 1.02, 9.8, "sleeper", 2),
    ("volvo_fh500", "Volvo", "FH 500", 500, 2500, 8200, 800, 780000, 32, 1.05, 1.03, 10.0, "highroof", 3),
    ("volvo_fh16", "Volvo", "FH16 750", 750, 3550, 8800, 900, 1650000, 36, 1.12, 1.00, 10.4, "highroof", 5),
    ("mb_axor1840", "Mercedes-Benz", "Axor 1840", 400, 1900, 7200, 450, 225000, 29, 0.95, 0.98, 9.7, "day", 1),
    ("mb_actros1845", "Mercedes-Benz", "Actros 1845", 450, 2200, 7800, 700, 460000, 30, 1.02, 1.00, 10.0, "sleeper", 2),
    ("mb_actros1851", "Mercedes-Benz", "Actros 1851", 510, 2500, 8100, 800, 820000, 32, 1.06, 1.00, 10.2, "highroof", 3),
    ("mb_arocs3363", "Mercedes-Benz", "Arocs 3363", 630, 3000, 9600, 600, 1180000, 38, 1.10, 0.90, 11.0, "day", 4),
    ("rn_kerax380", "Renault", "Kerax 380", 380, 1800, 7400, 450, 200000, 30, 0.93, 1.00, 9.5, "day", 1),
    ("rn_t480", "Renault", "T 480", 480, 2400, 7700, 600, 640000, 31, 1.02, 1.04, 9.9, "sleeper", 3),
    ("rn_thigh520", "Renault", "T High 520", 520, 2550, 8000, 800, 880000, 32, 1.04, 1.03, 10.1, "highroof", 4),
    ("sc_p360", "Scania", "P 360", 360, 1700, 7000, 450, 230000, 28, 0.97, 1.02, 9.4, "day", 1),
    ("sc_r450", "Scania", "R 450", 450, 2350, 7800, 700, 520000, 30, 1.03, 1.02, 10.0, "sleeper", 2),
    ("sc_r500", "Scania", "R 500", 500, 2600, 8100, 800, 850000, 31, 1.06, 1.04, 10.1, "highroof", 3),
    ("sc_s580", "Scania", "S 580 V8", 580, 3000, 8500, 900, 1450000, 35, 1.10, 1.02, 10.3, "highroof", 5),
    ("man_tgs18360", "MAN", "TGS 18.360", 360, 1700, 7100, 400, 180000, 28, 0.94, 1.01, 9.4, "day", 1),
    ("man_tgx18440", "MAN", "TGX 18.440", 440, 2100, 7700, 650, 470000, 30, 1.01, 1.00, 10.0, "sleeper", 2),
    ("man_tgx26510", "MAN", "TGX 26.510", 510, 2500, 9300, 700, 890000, 33, 1.05, 0.95, 10.8, "highroof", 4),
]
TRUCKS = {}
for r in _T:
    TRUCKS[r[0]] = dict(id=r[0], make=r[1], model=r[2], hp=r[3], torque=r[4], weight=r[5], fuel=r[6],
                        price=r[7], cons=r[8], brake=r[9], handling=r[10], turn=r[11], cab=r[12], level=r[13])
STARTERS = [t for t, v in TRUCKS.items() if v["level"] == 1]

UPGRADES = {
    "engine":       dict(name="Engine",       base=45000, fx="+4% power & torque per level"),
    "transmission": dict(name="Transmission", base=35000, fx="+2% drivetrain efficiency per level"),
    "brakes":       dict(name="Brakes",       base=30000, fx="+6% braking force per level"),
    "tires":        dict(name="Tires",        base=28000, fx="+5% grip per level"),
    "suspension":   dict(name="Suspension",   base=32000, fx="-8% crash damage & less body roll per level"),
    "fuel_tank":    dict(name="Fuel Tank",    base=25000, fx="+8% tank capacity per level"),
    "cabin":        dict(name="Cabin",        base=38000, fx="+3% XP from deliveries per level"),
    "lighting":     dict(name="Lighting",     base=18000, fx="+15% headlight range per level"),
}
UPGRADE_MAX = 5
def upgrade_price(key, lvl):           # price of buying level `lvl` (1..5)
    return int(UPGRADES[key]["base"] * (lvl ** 1.6))

TRAILERS = {
    "box":       dict(id="box",       name="Box Trailer",          price=0,      level=1, tare=6200),
    "curtain":   dict(id="curtain",   name="Curtainside Trailer",  price=140000, level=1, tare=6500),
    "flat":      dict(id="flat",      name="Flatbed Trailer",      price=110000, level=1, tare=5600),
    "container": dict(id="container", name="Container Chassis",    price=120000, level=2, tare=4800),
    "reefer":    dict(id="reefer",    name="Refrigerated Trailer", price=290000, level=3, tare=8300),
}

# id, name, category, trailer, kg, pay multiplier, fragility 0..1, min level
_C = [
    ("maize",     "Maize sacks",           "Agricultural", "curtain",   22000, 0.85, 0.10, 1),
    ("tea",       "Bagged tea",            "Agricultural", "curtain",   18000, 1.10, 0.20, 1),
    ("potatoes",  "Irish potatoes",        "Agricultural", "curtain",   24000, 0.80, 0.10, 1),
    ("unga",      "Wheat flour (unga)",    "Food",         "box",       20000, 1.00, 0.15, 1),
    ("oil",       "Cooking oil",           "Food",         "box",       22000, 1.05, 0.30, 2),
    ("milk",      "Fresh dairy",           "Refrigerated", "reefer",    20000, 1.30, 0.50, 3),
    ("flowers",   "Cut flowers",           "Refrigerated", "reefer",     8000, 1.60, 0.70, 3),
    ("cement",    "Cement bags",           "Construction", "flat",      26000, 0.90, 0.05, 1),
    ("steel",     "Steel bars",            "Construction", "flat",      28000, 1.00, 0.05, 2),
    ("timber",    "Sawn timber",           "Construction", "flat",      20000, 0.95, 0.10, 2),
    ("machinery", "Farm machinery",        "Machinery",    "flat",      24000, 1.35, 0.40, 4),
    ("furniture", "Furniture",             "Furniture",    "box",       12000, 1.15, 0.50, 2),
    ("electronics","Electronics",          "Electronics",  "box",        9000, 1.70, 0.90, 4),
    ("general",   "General cargo",         "General",      "box",       16000, 1.00, 0.30, 1),
    ("cont20",    "20ft container",        "Logistics",    "container", 24000, 1.20, 0.20, 2),
    ("cont40",    "40ft container",        "Logistics",    "container", 30000, 1.40, 0.20, 3),
]
CARGO = {}
for r in _C:
    CARGO[r[0]] = dict(id=r[0], name=r[1], cat=r[2], trailer=r[3], mass=r[4], mult=r[5], fragile=r[6], level=r[7])

LEVELS = [(1, 0, "New Driver"), (2, 400, "Local Driver"), (3, 1500, "Professional Driver"),
          (4, 4000, "Transport Operator"), (5, 9000, "Fleet Owner"),
          (6, 20000, "Regional Haulier"), (7, 45000, "Kenya Logistics Baron")]
def level_for(xp):
    lv = 1
    for n, need, _ in LEVELS:
        if xp >= need:
            lv = n
    return lv

def catalog():
    nodes = {k: dict(name=v[0], city=v[1], fuel=FUEL_PRICE.get(k, 180) if v[2] else 0,
                     garage=bool(v[3]), dealer=bool(v[4]), depot=bool(v[5])) for k, v in NODES.items()}
    cities = {k: dict(name=v[0], depot=v[1], tutorial_to=v[2], blurb=v[3]) for k, v in CITIES.items()}
    return dict(scale=WORLD_SCALE, nodes=nodes, cities=cities, trucks=list(TRUCKS.values()), starters=STARTERS,
                upgrades={k: dict(v, prices=[upgrade_price(k, i) for i in range(1, UPGRADE_MAX + 1)]) for k, v in UPGRADES.items()},
                upgrade_max=UPGRADE_MAX, trailers=list(TRAILERS.values()), cargo=list(CARGO.values()),
                levels=[dict(level=a, xp=b, title=c) for a, b, c in LEVELS], sell_ratio=SELL_RATIO,
                attribution="Route corridors are hand-authored from public town coordinates; not Google/proprietary data.")

# =============================================================================
# DATABASE
# =============================================================================
def db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH)
        g.db.row_factory = sqlite3.Row
    return g.db

@app.teardown_appcontext
def close_db(_e):
    d = g.pop("db", None)
    if d is not None:
        d.close()

# =============================================================================
# TABLES
# =============================================================================
def init_db():
    con = sqlite3.connect(DB_PATH)
    con.executescript("""
    CREATE TABLE IF NOT EXISTS accounts(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        username TEXT UNIQUE NOT NULL,
        pw_hash TEXT NOT NULL, salt TEXT NOT NULL,
        token TEXT, created REAL NOT NULL);
    CREATE TABLE IF NOT EXISTS saves(
        account_id INTEGER PRIMARY KEY REFERENCES accounts(id),
        data TEXT NOT NULL, updated REAL NOT NULL);
    CREATE TABLE IF NOT EXISTS jobs(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        account_id INTEGER NOT NULL, job_id TEXT NOT NULL,
        state TEXT NOT NULL, accepted REAL, completed REAL, pay INTEGER DEFAULT 0, xp INTEGER DEFAULT 0,
        UNIQUE(account_id, job_id));
    """)
    con.commit()
    con.close()

# =============================================================================
# VALIDATION
# =============================================================================
def clean_name(s, lo=2, hi=28):
    s = re.sub(r"[^\w \-.'&]", "", str(s or "")).strip()
    return s if lo <= len(s) <= hi else None

def hash_pw(pw, salt):
    return hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt), 120000).hex()

def truck_value(fleet_row):
    t = TRUCKS[fleet_row["model"]]
    v = t["price"]
    for k, lvl in fleet_row["upgrades"].items():
        for i in range(1, int(lvl) + 1):
            v += upgrade_price(k, i)
    return v

def networth(st):
    v = st["money"] + sum(truck_value(f) for f in st["fleet"])
    v += sum(TRAILERS[t]["price"] for t in st["trailers"])
    return v

def num(v, lo, hi, default=None):
    try:
        v = float(v)
    except (TypeError, ValueError):
        return default
    if math.isnan(v) or math.isinf(v):
        return default
    return max(lo, min(hi, v))

def new_state(company, driver, start, starter):
    return {
        "company": {"name": company, "driver": driver, "reputation": 50, "founded": int(time.time()),
                    "stats": {"deliveries": 0, "km": 0, "earned": 0, "spent": 0, "crashes": 0, "fines": 0}},
        "money": START_MONEY, "xp": 0, "level": 1,
        "fleet": [{"uid": 1, "model": starter, "upgrades": {k: 0 for k in UPGRADES}, "fuel": 1.0, "cond": 100.0,
                   "odo": 0.0, "paint": "#e8e4dc"}],
        "next_uid": 2, "active": 1, "trailers": ["box"], "trailer": "box",
        "location": start, "pos": None, "job": None, "completed": 0,
        "tutorial": {"done": False},
        "settings": {"quality": "auto", "volume": 0.8, "manual": False, "weather": "auto", "touch": "auto", "steer": 1.0},
    }

def sanitize_state(prev, new):
    """Validate a client save against the last stored state. Returns (state, error)."""
    if not isinstance(new, dict):
        return None, "bad payload"
    out = json.loads(json.dumps(prev))   # deep copy; server-owned fields stay
    money = num(new.get("money"), 0, 1e10)
    if money is None:
        return None, "invalid money"
    fleet_in = new.get("fleet")
    if not isinstance(fleet_in, list) or not (1 <= len(fleet_in) <= MAX_FLEET):
        return None, "invalid fleet"
    fleet, seen = [], set()
    for f in fleet_in:
        if not isinstance(f, dict) or f.get("model") not in TRUCKS:
            return None, "unknown truck"
        uid = int(num(f.get("uid"), 1, 1e9, 0))
        if uid in seen or uid == 0:
            return None, "duplicate truck id"
        seen.add(uid)
        ups = {}
        for k in UPGRADES:
            ups[k] = int(num((f.get("upgrades") or {}).get(k), 0, UPGRADE_MAX, 0))
        paint = f.get("paint") if isinstance(f.get("paint"), str) and re.fullmatch(r"#[0-9a-fA-F]{6}", f["paint"]) else "#e8e4dc"
        fleet.append({"uid": uid, "model": f["model"], "upgrades": ups,
                      "fuel": num(f.get("fuel"), 0, 1, 1.0), "cond": num(f.get("cond"), 0, 100, 100.0),
                      "odo": num(f.get("odo"), 0, 1e7, 0.0), "paint": paint})
    trailers = [t for t in dict.fromkeys(new.get("trailers") or []) if t in TRAILERS]
    if "box" not in trailers:
        trailers.insert(0, "box")
    cand = dict(out, money=int(money), fleet=fleet, trailers=trailers)
    # money can only be created by the server (job completion); saves may never increase net worth.
    if networth(cand) > networth(prev) + 1:
        return None, "net worth increased without a verified delivery"
    xp = int(num(new.get("xp"), 0, 1e9, 0))
    if xp > prev["xp"]:
        return None, "xp increased without a verified delivery"
    out.update(money=int(money), fleet=fleet, trailers=trailers, xp=xp, level=level_for(xp))
    ua = int(num(new.get("active"), 1, 1e9, 0))
    out["active"] = ua if ua in seen else fleet[0]["uid"]
    out["next_uid"] = int(max(num(new.get("next_uid"), 1, 1e9, 1), max(seen) + 1))
    out["trailer"] = new.get("trailer") if new.get("trailer") in trailers else "box"
    loc = new.get("location")
    out["location"] = loc if loc in CITIES else prev.get("location", "nairobi")
    pos = new.get("pos")
    if isinstance(pos, dict):
        out["pos"] = {k: num(pos.get(k), -1e6, 1e6, 0.0) for k in ("x", "z", "yaw")}
    job = new.get("job")
    if job is None:
        out["job"] = None
    elif isinstance(job, dict) and isinstance(job.get("id"), str):
        j = job_from_id(job["id"])
        if j:
            out["job"] = dict(j, phase="transit" if job.get("phase") == "transit" else "pickup",
                              t=num(job.get("t"), 0, 1e6, 0.0), integrity=num(job.get("integrity"), 0, 1, 1.0))
    c_in = new.get("company") or {}
    comp = out["company"]
    nm = clean_name(c_in.get("name")); dr = clean_name(c_in.get("driver"))
    if nm: comp["name"] = nm
    if dr: comp["driver"] = dr
    comp["reputation"] = int(num(c_in.get("reputation"), 0, 100, comp["reputation"]))
    s_in = c_in.get("stats") or {}
    for k in ("km", "crashes", "fines", "spent"):      # non-earning stats: monotonic and bounded per save
        v = num(s_in.get(k), comp["stats"][k], comp["stats"][k] + 5e6, comp["stats"][k])
        comp["stats"][k] = int(v)
    t_in = new.get("tutorial") or {}
    out["tutorial"] = {"done": bool(t_in.get("done") or prev["tutorial"].get("done"))}
    st_in = new.get("settings") or {}
    sset = out["settings"]
    if st_in.get("quality") in ("auto", "low", "med", "high"): sset["quality"] = st_in["quality"]
    sset["volume"] = num(st_in.get("volume"), 0, 1, sset["volume"])
    sset["manual"] = bool(st_in.get("manual"))
    if st_in.get("weather") in ("auto", "clear", "cloudy", "rain", "fog"): sset["weather"] = st_in["weather"]
    if st_in.get("touch") in ("auto", "on", "off"): sset["touch"] = st_in["touch"]
    sset["steer"] = num(st_in.get("steer"), 0.4, 2.0, sset["steer"])
    return out, None

# =============================================================================
# COMPANY
# =============================================================================
def auth():
    tok = request.headers.get("X-Token", "")
    if not tok:
        return None
    row = db().execute("SELECT * FROM accounts WHERE token=?", (tok,)).fetchone()
    return row

def need_auth():
    a = auth()
    if not a:
        abort(401, description="Please sign in.")
    return a

def load_state(acc):
    row = db().execute("SELECT data FROM saves WHERE account_id=?", (acc["id"],)).fetchone()
    return json.loads(row["data"]) if row else None

def store_state(acc, st):
    st["level"] = level_for(st["xp"])
    db().execute("INSERT INTO saves(account_id,data,updated) VALUES(?,?,?) "
                 "ON CONFLICT(account_id) DO UPDATE SET data=excluded.data, updated=excluded.updated",
                 (acc["id"], json.dumps(st), time.time()))
    db().commit()

@app.errorhandler(400)
@app.errorhandler(401)
@app.errorhandler(403)
@app.errorhandler(404)
@app.errorhandler(409)
def handle_err(e):
    return jsonify(error=getattr(e, "description", "error")), e.code

def level_info(xp):
    lv = level_for(xp)
    cur = next(x for x in LEVELS if x[0] == lv)
    nxt = next((x for x in LEVELS if x[0] == lv + 1), None)
    return dict(level=lv, title=cur[2], xp=xp, xp_this=cur[1], xp_next=nxt[1] if nxt else None,
                next_title=nxt[2] if nxt else None)

# =============================================================================
# JOBS
# =============================================================================
def _rng(*parts):
    return random.Random(hashlib.sha256("|".join(map(str, parts)).encode()).hexdigest())

def job_from_id(job_id):
    """Deterministically rebuild a job from its id.  Ids: 'o:d:cargo:seed:k' or 'tut:o:d'."""
    p = job_id.split(":")
    try:
        if p[0] == "tut" and len(p) == 3:
            o, dnode = p[1], p[2]
            if o not in CITIES or dnode != CITIES[o][2]:
                return None
            return dict(id=job_id, tutorial=True, frm=o, to=dnode, from_node=CITIES[o][1], to_node=dnode,
                        cargo="general", trailer="box", mass=9000, fragile=0.2, real_km=4, dist_game_km=0.4,
                        pay=5000, xp=120, deadline=600, difficulty=1, level=1, value=45000)
        if len(p) != 5:
            return None
        o, d, c, seed, k = p[0], p[1], p[2], int(p[3]), int(p[4])
        if o not in CITIES or d not in CITIES or o == d or c not in CARGO:
            return None
        if abs(int(time.time() // JOB_WINDOW_S) - seed) > 24:      # accept jobs up to ~6 hours old
            return None
        km = real_km(o, d)
        cg = CARGO[c]
        diff = ROUTE_DIFFICULTY[frozenset((o, d))] + (1 if cg["fragile"] > 0.6 else 0)
        rnd = _rng(job_id)
        pay = int(km * PAY_PER_KM * cg["mult"] * (1 + 0.08 * (diff - 1)) * rnd.uniform(0.92, 1.12))
        pay = int(round(pay, -1))
        deadline = int((km * WORLD_SCALE / 62.0 * 3600) * 1.55 + 240)      # seconds of real play time
        return dict(id=job_id, tutorial=False, frm=o, to=d, from_node=CITIES[o][1], to_node=CITIES[d][1],
                    cargo=c, trailer=cg["trailer"], mass=cg["mass"], fragile=cg["fragile"], real_km=km,
                    dist_game_km=round(km * WORLD_SCALE, 1), pay=pay, xp=int(km * 1.4 + 30 + diff * 8),
                    deadline=deadline, difficulty=min(5, diff), level=cg["level"],
                    value=int(pay * 2.5))
    except (ValueError, IndexError, KeyError):
        return None

def board(origin, level):
    seed = int(time.time() // JOB_WINDOW_S)
    out = []
    for d in CITIES:
        if d == origin:
            continue
        pool = [c for c in CARGO.values() if c["level"] <= max(level, 1)] or [CARGO["general"]]
        rnd = _rng("board", origin, d, seed)
        for k, c in enumerate(rnd.sample(pool, min(3, len(pool)))):
            out.append(job_from_id(f"{origin}:{d}:{c['id']}:{seed}:{k}"))
    return [j for j in out if j]

# =============================================================================
# API ROUTES
# =============================================================================
@app.route("/")
def index():
    if not os.path.exists(INDEX_PATH):
        return "index.html not found next to app.py", 404
    return send_file(INDEX_PATH)

@app.route("/api/catalog")
def api_catalog():
    return jsonify(catalog())

@app.route("/api/register", methods=["POST"])
def api_register():
    d = request.get_json(silent=True) or {}
    user = re.sub(r"[^a-zA-Z0-9_]", "", str(d.get("username", "")))[:20]
    pw = str(d.get("password", ""))
    company, driver = clean_name(d.get("company")), clean_name(d.get("driver"))
    start, starter = d.get("start"), d.get("starter")
    if len(user) < 3: abort(400, description="Username needs 3+ letters or numbers.")
    if len(pw) < 4: abort(400, description="Password needs at least 4 characters.")
    if not company: abort(400, description="Enter a company name (2-28 characters).")
    if not driver: abort(400, description="Enter a driver name (2-28 characters).")
    if start not in CITIES: abort(400, description="Choose a starting city.")
    if starter not in STARTERS: abort(400, description="Choose a starter truck.")
    salt = secrets.token_hex(16)
    tok = secrets.token_hex(24)
    try:
        cur = db().execute("INSERT INTO accounts(username,pw_hash,salt,token,created) VALUES(?,?,?,?,?)",
                           (user.lower(), hash_pw(pw, salt), salt, tok, time.time()))
    except sqlite3.IntegrityError:
        abort(409, description="That username is taken.")
    acc = db().execute("SELECT * FROM accounts WHERE id=?", (cur.lastrowid,)).fetchone()
    st = new_state(company, driver, start, starter)
    store_state(acc, st)
    return jsonify(token=tok, state=st, profile=level_info(0))

@app.route("/api/login", methods=["POST"])
def api_login():
    d = request.get_json(silent=True) or {}
    row = db().execute("SELECT * FROM accounts WHERE username=?", (str(d.get("username", "")).lower(),)).fetchone()
    if not row or hash_pw(str(d.get("password", "")), row["salt"]) != row["pw_hash"]:
        abort(401, description="Wrong username or password.")
    tok = secrets.token_hex(24)
    db().execute("UPDATE accounts SET token=? WHERE id=?", (tok, row["id"]))
    db().commit()
    st = load_state(row)
    return jsonify(token=tok, state=st, profile=level_info(st["xp"]))

@app.route("/api/load")
def api_load():
    acc = need_auth()
    st = load_state(acc)
    if not st: abort(404, description="No save found.")
    return jsonify(state=st, profile=level_info(st["xp"]))

@app.route("/api/save", methods=["POST"])
def api_save():
    acc = need_auth()
    prev = load_state(acc)
    d = request.get_json(silent=True) or {}
    st, err = sanitize_state(prev, d.get("state"))
    if err:
        return jsonify(error="Save rejected: " + err, state=prev), 400
    store_state(acc, st)
    return jsonify(ok=True, saved=time.time(), profile=level_info(st["xp"]))

@app.route("/api/company", methods=["GET", "POST"])
def api_company():
    acc = need_auth()
    st = load_state(acc)
    if request.method == "POST":
        d = request.get_json(silent=True) or {}
        nm, dr = clean_name(d.get("name")), clean_name(d.get("driver"))
        if not nm or not dr: abort(400, description="Names must be 2-28 characters.")
        st["company"]["name"], st["company"]["driver"] = nm, dr
        store_state(acc, st)
    c = st["company"]
    return jsonify(company=c, money=st["money"], fleet_size=len(st["fleet"]),
                   fleet_value=sum(truck_value(f) for f in st["fleet"]), profile=level_info(st["xp"]))

@app.route("/api/profile")
def api_profile():
    acc = need_auth()
    st = load_state(acc)
    n = db().execute("SELECT COUNT(*) c FROM jobs WHERE account_id=? AND state='done'", (acc["id"],)).fetchone()["c"]
    return jsonify(username=acc["username"], profile=level_info(st["xp"]), deliveries=n,
                   member_since=acc["created"], company=st["company"]["name"])

@app.route("/api/jobs")
def api_jobs():
    acc = need_auth()
    st = load_state(acc)
    origin = request.args.get("origin", st.get("location", "nairobi"))
    if origin not in CITIES: abort(400, description="Unknown city.")
    return jsonify(origin=origin, jobs=board(origin, level_for(st["xp"])))

@app.route("/api/job/accept", methods=["POST"])
def api_job_accept():
    acc = need_auth()
    st = load_state(acc)
    jid = str((request.get_json(silent=True) or {}).get("id", ""))
    j = job_from_id(jid)
    if not j: abort(400, description="That job is no longer available.")
    if j["level"] > level_for(st["xp"]): abort(403, description=f"Requires level {j['level']}.")
    if j["trailer"] not in st["trailers"]:
        abort(403, description=f"You need a {TRAILERS[j['trailer']]['name']} (buy it in the dealership).")
    row = db().execute("SELECT state FROM jobs WHERE account_id=? AND job_id=?", (acc["id"], jid)).fetchone()
    if row and row["state"] == "done": abort(409, description="Job already completed.")
    db().execute("UPDATE jobs SET state='abandoned' WHERE account_id=? AND state='active'", (acc["id"],))
    db().execute("INSERT INTO jobs(account_id,job_id,state,accepted) VALUES(?,?,?,?) "
                 "ON CONFLICT(account_id,job_id) DO UPDATE SET state='active', accepted=excluded.accepted",
                 (acc["id"], jid, "active", time.time()))
    st["job"] = dict(j, phase="pickup", t=0.0, integrity=1.0)
    store_state(acc, st)
    return jsonify(job=st["job"])

@app.route("/api/job/abandon", methods=["POST"])
def api_job_abandon():
    acc = need_auth()
    st = load_state(acc)
    db().execute("UPDATE jobs SET state='abandoned' WHERE account_id=? AND state='active'", (acc["id"],))
    if st.get("job") and not st["job"].get("tutorial"):
        st["company"]["reputation"] = max(0, st["company"]["reputation"] - 2)
    st["job"] = None
    store_state(acc, st)
    return jsonify(ok=True, reputation=st["company"]["reputation"])

@app.route("/api/job/complete", methods=["POST"])
def api_job_complete():
    """Server computes the payout. Client only reports how the job went."""
    acc = need_auth()
    st = load_state(acc)
    d = request.get_json(silent=True) or {}
    jid = str(d.get("id", ""))
    row = db().execute("SELECT * FROM jobs WHERE account_id=? AND job_id=?", (acc["id"], jid)).fetchone()
    if not row or row["state"] != "active": abort(409, description="Job was not active.")
    j = job_from_id(jid) if not jid.startswith("tut:") else job_from_id(jid)
    if not j:
        # expired board window but already accepted -> rebuild ignoring the window
        parts = jid.split(":")
        try:
            j = job_from_id(f"{parts[0]}:{parts[1]}:{parts[2]}:{int(time.time() // JOB_WINDOW_S)}:{parts[4]}")
        except IndexError:
            abort(400, description="Bad job.")
    elapsed = time.time() - (row["accepted"] or time.time())
    game_m = j["dist_game_km"] * 1000
    if elapsed < max(15.0, game_m / 45.0):          # faster than 162 km/h average is impossible
        abort(400, description="Delivery rejected: implausibly fast.")
    integrity = num(d.get("integrity"), 0, 1, 1.0)
    on_time = bool(d.get("on_time"))
    base = j["pay"]
    pay = base * (0.45 + 0.55 * integrity) * (1.10 if on_time else 0.85)
    pay = int(min(pay, base * 1.25))
    cabin = 1.0
    act = next((f for f in st["fleet"] if f["uid"] == st["active"]), st["fleet"][0])
    cabin += 0.03 * act["upgrades"].get("cabin", 0)
    xp = int(j["xp"] * cabin * (1.0 if on_time else 0.8))
    st["money"] += pay
    st["xp"] += xp
    st["completed"] += 1
    s = st["company"]["stats"]
    s["deliveries"] += 1; s["earned"] += pay; s["km"] += int(j["real_km"])
    st["company"]["reputation"] = int(max(0, min(100, st["company"]["reputation"] + (2 if on_time and integrity > .8 else -1))))
    st["job"] = None
    st["location"] = j["to"] if j["to"] in CITIES else st["location"]
    old_level = st["level"]
    store_state(acc, st)
    db().execute("UPDATE jobs SET state='done', completed=?, pay=?, xp=? WHERE id=?", (time.time(), pay, xp, row["id"]))
    db().commit()
    return jsonify(pay=pay, xp=xp, money=st["money"], total_xp=st["xp"], level=st["level"],
                   leveled_up=st["level"] > old_level, profile=level_info(st["xp"]),
                   reputation=st["company"]["reputation"], stats=s)

# =============================================================================
# SERVER
# =============================================================================
if __name__ == "__main__":
    init_db()
    print("\n  KENYA TRUCKERS SIMULATOR  -  ACE SYNAPSE TECHNOLOGIES")
    print("  Open http://127.0.0.1:5000  (phones on the same Wi-Fi: http://<this-PC-IP>:5000)\n")
    app.run(host="0.0.0.0", port=5000, debug=False, threaded=True)
