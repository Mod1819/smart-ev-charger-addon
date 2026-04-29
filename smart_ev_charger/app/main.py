#!/usr/bin/env python3
"""Smart EV Charger - PV-basierte Ladesteuerung mit Lernfunktion"""

import json
import logging
import math
import os
import sqlite3
import threading
import time
from collections import deque
from datetime import datetime, date, timedelta
from pathlib import Path

import requests
from flask import Flask, jsonify, render_template_string, request, Response

try:
    from pymodbus.client import ModbusTcpClient as _ModbusTcpClient
    _PYMODBUS_OK = True
except ImportError:
    _PYMODBUS_OK = False

# ---------------------------------------------------------------------------
# Globale Konstanten
# ---------------------------------------------------------------------------

LATITUDE_DEG          = 51.0    # Näherungsbreitengrad für Sonnenzeiten (Deutschland)
PV_GLITCH_MIN_W       = 150     # Unter diesem Wert gilt PV als inaktiv (Glitch-Schutz)
PV_ESTIMATE_FACTOR    = 0.65    # Schätzfaktor: verbleibende PV aus aktueller Leistung
PV_ESTIMATE_HOURS     = 0.25    # Stunden-Horizont für PV-Kurzschätzung
DEFAULT_BATT_CHARGE_KW = 0.4   # Fallback-Laderate Speicher wenn kein Sensor/Lernwert
LEARNING_HOUR         = 22      # Ab dieser Stunde startet der Tages-Lernlauf
DEBUG_BUFFER_MAX      = 300     # Max. Einträge im Debug-Ringpuffer

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# HA Supervisor / Dev-Fallback
# ---------------------------------------------------------------------------
# Als HA Add-on: SUPERVISOR_TOKEN wird automatisch injiziert → kein manueller Token nötig.
# Für lokale Entwicklung: Fallback auf options.json oder Hardcoded-Werte.

SUPERVISOR_TOKEN = os.environ.get("SUPERVISOR_TOKEN")


def _dev_config():
    """Nur für lokale Entwicklung ohne HA Supervisor."""
    path = "/data/options.json"
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return {
        "ha_url":                  "http://192.168.0.178:8123",
        "ha_token":                "",
        "evcc_url":                "http://192.168.0.224:7070",
        "batterie_kapazitaet_kwh": 9.0,
        "batterie_min_soc":        15,
        "haus_ema_kwh":            11.0,
        "update_interval_min":     5,
        "loadpoint_id":            1,
        "sensor_batterie_soc":     "sensor.growatt_battery_soc",
        "sensor_pv_leistung":      "sensor.growatt_pv_power_total",
        "sensor_haus_last":        "sensor.growatt_today_s_yield",
    }


_DEV_CFG = _dev_config()


def _use_supervisor() -> bool:
    """Supervisor-API nur nutzen wenn kein direkter HA-Token in options.json vorhanden ist.
    SUPERVISOR_TOKEN ist in jedem HA Add-on Container gesetzt, aber für API-Zugriff
    muss config.yaml homeassistant_api: true haben — sonst liefert der Supervisor kein JSON."""
    return bool(SUPERVISOR_TOKEN) and not _DEV_CFG.get("ha_token", "")


def get_ha_headers():
    if _use_supervisor():
        return {"Authorization": f"Bearer {SUPERVISOR_TOKEN}"}
    return {"Authorization": f"Bearer {_DEV_CFG.get('ha_token', '')}"}


def get_ha_api_url(entity_id=None):
    if _use_supervisor():
        base = "http://supervisor/core/api"
    else:
        base = _DEV_CFG.get("ha_url", "http://localhost:8123") + "/api"
    return f"{base}/states/{entity_id}" if entity_id else base


# ---------------------------------------------------------------------------
# Sensor-Definitionen  (key, label, beschreibung, default_entity_id)
# ---------------------------------------------------------------------------

SENSOREN_DEF = [
    ("pv_remaining",   "PV verbleibend heute",    "Forecast.Solar — heute noch erwartete PV-Energie (kWh)",       "sensor.energy_production_today_remaining"),
    ("pv_heute_total", "PV Prognose heute gesamt", "Forecast.Solar — Tages-Gesamtprognose (kWh)",                  "sensor.energy_production_today"),
    ("pv_morgen",      "PV Prognose morgen",       "Forecast.Solar — morgige Gesamtprognose (kWh)",                "sensor.energy_production_tomorrow"),
    ("pv_real",        "PV produziert heute real", "Wechselrichter — tatsächlich erzeugte Energie heute (kWh)",    "sensor.growatt_today_s_solar_energy"),
    ("batterie_soc",   "Batterie SOC",             "Aktueller Ladestand des Speichers (%)",                        "sensor.growatt_battery_soc"),
    ("pv_leistung",    "PV Leistung aktuell",      "Aktuelle PV-Erzeugungsleistung (W)",                           "sensor.growatt_pv_power_total"),
    ("haus_last",      "Haus Gesamtlast heute",    "Gesamter Hausverbrauch heute inkl. Auto-Laden (kWh)",          "sensor.growatt_today_s_yield"),
    ("grid_power",     "Netzleistung",             "Aktuelle Netzleistung (W) — negativ = Einspeisung ins Netz",   "sensor.grid_power_evcc"),
]
SENSOREN_DEFAULTS = {k: d for k, _, _, d in SENSOREN_DEF}

# Solcast sensor-IDs (HACS Integration "solcast_solar" v4.5.2 — deutsche Entity-IDs)
SOLCAST_SENSOR_DEFAULTS = {
    "pv_remaining":   "sensor.solcast_pv_forecast_prognose_verbleibende_leistung_heute",
    "pv_heute_total": "sensor.solcast_pv_forecast_prognose_heute",
    "pv_morgen":      "sensor.solcast_pv_forecast_prognose_morgen",
}

# ---------------------------------------------------------------------------
# Pfade & Konstanten
# ---------------------------------------------------------------------------

DATA_DIR      = Path("/data")
DB_PATH       = DATA_DIR / "smart_ev.db"
SETTINGS_PATH = DATA_DIR / "user_settings.json"
WOCHENTAGE    = ["Montag", "Dienstag", "Mittwoch", "Donnerstag", "Freitag", "Samstag", "Sonntag"]

# ---------------------------------------------------------------------------
# User Settings (persistent, über UI änderbar)
# ---------------------------------------------------------------------------

def load_settings():
    data = {}
    if SETTINGS_PATH.exists():
        with open(SETTINGS_PATH) as f:
            data = json.load(f)

    # Lernwerte
    data.setdefault("addon_aktiv", True)
    data.setdefault("min_strom_a", 6)
    data.setdefault("haus_verbrauch_kwh", 10.0)  # Startwert für EMA (vom Nutzer einzustellen)
    data.setdefault("sensor_auto_soc",   "")     # optional: Fahrzeug-SOC Sensor
    data.setdefault("auto_batterie_kwh", 0.0)    # optional: Fahrzeug-Batteriegröße (kWh)
    data.setdefault("auto_ziel_soc",     80)     # Ziel-SOC Fahrzeug (%)
    if "haus_ema_wochentag" not in data:
        base = float(data.get("haus_verbrauch_kwh", 10.0))
        data["haus_ema_wochentag"] = {str(i): base for i in range(7)}
    # Gelernte Batterie-Laderate (kW) pro Wochentag
    if "batt_fill_rate_wochentag" not in data:
        data["batt_fill_rate_wochentag"] = {}
    data.setdefault("pv_faktor", 1.0)
    data.pop("pv_faktor_wochentag",  None)  # altes Feld entfernen
    data.pop("pv_korrekturfaktor",   None)  # altes Feld entfernen

    # Verbindung
    data.setdefault("evcc_url",     _DEV_CFG.get("evcc_url", "http://localhost:7070"))
    data.setdefault("loadpoint_id", int(_DEV_CFG.get("loadpoint_id", 1)))

    # Batterie
    data.setdefault("wallbox_type",      "evcc")   # "evcc" | "ha_direct"
    data.setdefault("wallbox_connected", "")       # binary_sensor: Auto angesteckt?
    data.setdefault("wallbox_charging",  "")       # binary_sensor: Lädt gerade?
    data.setdefault("wallbox_energy",    "")       # sensor: geladene Energie heute (kWh)
    data.setdefault("wallbox_switch",    "")       # switch/input_boolean: Laden ein/aus
    data.setdefault("wallbox_current",   "")       # number: Ladestrom (A, optional)
    data.setdefault("has_battery",             True)
    data.setdefault("batterie_kapazitaet_kwh", float(_DEV_CFG.get("batterie_kapazitaet_kwh", 9.0)))
    data.setdefault("batterie_min_soc",        int(_DEV_CFG.get("batterie_min_soc", 15)))
    data.setdefault("batterie_ziel_soc",       100)

    # Ampel-Schwellwerte
    data.setdefault("ampel_gruen_kwh",  0.5)   # ab hier grün (Budget sicher)
    data.setdefault("ampel_gelb_kwh",  -1.0)   # ab hier gelb (knapp), darunter rot

    # Prognose-Anbieter
    data.setdefault("forecast_provider",   "forecast_solar")  # "forecast_solar" | "solcast" | "solcast_direct"
    data.setdefault("solcast_api_key",     "")
    data.setdefault("solcast_resource_id", "")

    # Budget-Puffer
    data.setdefault("budget_puffer_kwh", 0.0)

    # Benachrichtigungen
    data.setdefault("notify_target",          "")     # HA-Notification-Service, z.B. "mobile_app_iphone"
    data.setdefault("notify_budget_low",      False)  # Bei Budget fast leer
    data.setdefault("notify_budget_low_kwh",  0.5)    # Schwellwert in kWh
    data.setdefault("notify_deadline_urgent", False)  # Bei Deadline < 60 Min
    data.setdefault("notify_laden_fertig",    False)  # Wenn Auto fertig geladen / abgesteckt

    # Standort (für Sonnenzeiten und Feiertage)
    data.setdefault("latitude",   LATITUDE_DEG)  # Breitengrad, z.B. 51.0 für Köln/Frankfurt
    data.setdefault("bundesland", "")            # Bundesland-Kürzel für Feiertage, z.B. "BY"

    # Sprache
    data.setdefault("language", "auto")  # "auto" | "de" | "en"

    # System
    data.setdefault("update_interval_min", int(_DEV_CFG.get("update_interval_min", 5)))

    # Sensoren (mit Migration aus alten CFG-Schlüsseln)
    if "sensoren" not in data:
        data["sensoren"] = {}
    s = data["sensoren"]
    s.setdefault("pv_remaining",   SENSOREN_DEFAULTS["pv_remaining"])
    s.setdefault("pv_heute_total", SENSOREN_DEFAULTS["pv_heute_total"])
    s.setdefault("pv_morgen",      SENSOREN_DEFAULTS["pv_morgen"])
    s.setdefault("pv_real",        _DEV_CFG.get("sensor_pv_heute",     SENSOREN_DEFAULTS["pv_real"]))
    s.setdefault("batterie_soc",   _DEV_CFG.get("sensor_batterie_soc", SENSOREN_DEFAULTS["batterie_soc"]))
    s.setdefault("pv_leistung",    _DEV_CFG.get("sensor_pv_leistung",  SENSOREN_DEFAULTS["pv_leistung"]))
    s.setdefault("haus_last",      _DEV_CFG.get("sensor_haus_last",    SENSOREN_DEFAULTS["haus_last"]))
    s.setdefault("grid_power",     SENSOREN_DEFAULTS["grid_power"])

    return data


def save_settings(s: dict):
    with open(SETTINGS_PATH, "w") as f:
        json.dump(s, f, indent=2)


# Getter-Funktionen — lesen immer live aus user_settings
def get_sensor(key: str)       -> str:   return user_settings.get("sensoren", {}).get(key, SENSOREN_DEFAULTS[key])

def is_feiertag(dt: date | None = None) -> bool:
    """True wenn dt (Standard: heute) ein Feiertag im konfigurierten Bundesland ist."""
    bl = user_settings.get("bundesland", "")
    if not bl:
        return False
    if dt is None:
        dt = date.today()
    try:
        import holidays as hd
        return dt in hd.Germany(subdiv=bl)
    except Exception:
        return False

def get_ema_today()            -> float:
    wd = "6" if is_feiertag() else str(date.today().weekday())
    return user_settings["haus_ema_wochentag"].get(wd, _DEV_CFG.get("haus_ema_kwh", 11.0))
def get_pv_faktor()            -> float: return user_settings.get("pv_faktor", 1.0)
def get_batt_kap()             -> float: return float(user_settings.get("batterie_kapazitaet_kwh", 9.0))
def get_batt_min_soc()         -> int:   return int(user_settings.get("batterie_min_soc", 15))
def has_battery()              -> bool:  return bool(user_settings.get("has_battery", True))
def get_batt_ziel_soc()        -> int:   return int(user_settings.get("batterie_ziel_soc", 100))
def get_evcc_url()             -> str:   return user_settings.get("evcc_url", "http://localhost:7070")
def get_loadpoint_id()         -> int:   return int(user_settings.get("loadpoint_id", 1))
def get_update_interval()      -> int:   return int(user_settings.get("update_interval_min", 5))
def is_debug_mode()            -> bool:  return bool(user_settings.get("debug_mode", False))

user_settings = load_settings()

# ---------------------------------------------------------------------------
# Debug-Log (rolling buffer, nur wenn debug_mode aktiv)
# ---------------------------------------------------------------------------

_debug_buffer: deque = deque(maxlen=DEBUG_BUFFER_MAX)
_debug_prev: dict = {}   # letzte bekannte Werte für Delta-Erkennung
_last_loop_sig: str = "" # Signatur des letzten Loop-Durchlaufs (Duplikat-Filter)

def dlog(msg: str, category: str = "info"):
    """Schreibt in den Debug-Ringpuffer wenn debug_mode aktiv."""
    if not is_debug_mode():
        return
    ts = datetime.now().strftime("%H:%M:%S")
    _debug_buffer.append({"ts": ts, "cat": category, "msg": msg})
    log.info(f"[DBG] {msg}")

def dlog_delta(key: str, label: str, new_val, unit: str = "", fmt_fn=None, threshold=0.05):
    """Loggt einen Wertewechsel nur wenn er signifikant ist."""
    if not is_debug_mode():
        return
    old_val = _debug_prev.get(key)
    if old_val is None:
        _debug_prev[key] = new_val
        return
    try:
        diff = abs(float(new_val) - float(old_val))
        if diff < threshold:
            _debug_prev[key] = new_val
            return
        fmt = fmt_fn or (lambda v: f"{v:.2f}")
        dlog(f"{label}: {fmt(old_val)}{unit} → {fmt(new_val)}{unit}  (Δ {'+' if float(new_val) > float(old_val) else ''}{fmt(float(new_val)-float(old_val))}{unit})", "delta")
    except (TypeError, ValueError):
        if str(old_val) != str(new_val):
            dlog(f"{label}: {old_val} → {new_val}", "delta")
    _debug_prev[key] = new_val

# ---------------------------------------------------------------------------
# Zustand (live)
# ---------------------------------------------------------------------------

state = {
    "last_update":              None,
    "pv_prognose_kwh":          0.0,
    "pv_heute_kwh":             0.0,
    "batterie_soc":             0,
    "pv_leistung_w":            0.0,
    "haus_last_kwh":            0.0,
    "haus_ema_kwh":             11.0,
    "haus_ema_wochentag":       {},
    "pv_forecast_rest_kwh":     0.0,
    "haus_rest_kwh":            0.0,
    "battery_needs_kwh":        0.0,
    "initial_daily_budget_kwh": None,
    "budget_verfuegbar_kwh":    0.0,
    "charged_today_kwh":        0.0,
    "countdown_kwh":            0.0,
    "noch_offen_kwh":           0.0,
    "einspeisung_heute_kwh":    0.0,
    "laden_schnell":            False,
    "batterie_ziel_soc":        100,
    "ziel_strom_a":             6,
    "car_connected":            False,
    "evcc_online":              True,
    "evcc_mode":                "off",
    "action":                   "start",
    "grund":                    "Initialisierung...",
    "laden_pausiert":           False,
    "pv_aktiv":                 False,
    # backwards compat
    "available_for_car_kwh":    0.0,
    "budget_kwh":               0.0,
    "daily_budget_kwh":         0.0,
}

# ---------------------------------------------------------------------------
# Tages-Budget (persistent)
# ---------------------------------------------------------------------------

BUDGET_ACC_PATH = DATA_DIR / "daily_budget.json"


def _load_daily_budget():
    try:
        if BUDGET_ACC_PATH.exists():
            d = json.loads(BUDGET_ACC_PATH.read_text())
            if d.get("date") == str(date.today()):
                return d
    except Exception:
        pass
    return {
        "date":                    str(date.today()),
        "pv_prognose_kwh":         None,
        "einspeisung_kwh":         0.0,
        "last_loop_ts":            None,
        "pv_reset_done":           False,
        "battery_needs_initial":   None,
        "initial_daily_budget":    None,
        "soc_at_sunset":           None,
        "last_valid_remaining_pv": None,
        "laden_pausiert":          False,
    }


def _save_daily_budget(d):
    try:
        BUDGET_ACC_PATH.write_text(json.dumps(d))
    except Exception:
        pass


_daily_budget = _load_daily_budget()

# ---------------------------------------------------------------------------
# Datenbank
# ---------------------------------------------------------------------------

def init_db():
    with sqlite3.connect(DB_PATH) as conn:
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS tageslog (
                datum            TEXT PRIMARY KEY,
                pv_prognose_kwh  REAL,
                pv_real_kwh      REAL,
                haus_last_kwh    REAL,
                haus_ema_kwh     REAL,
                auto_geladen_kwh REAL,
                budget_kwh       REAL,
                batterie_soc     INTEGER,
                einspeisung_kwh  REAL
            );
            CREATE TABLE IF NOT EXISTS steuerlog (
                ts           TEXT,
                budget_kwh   REAL,
                prognose_kwh REAL,
                pv_kwh       REAL,
                batt_soc     INTEGER,
                ziel_a       INTEGER,
                auto_da      INTEGER,
                action       TEXT,
                grund        TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_steuerlog_ts ON steuerlog(ts);
        """)
        try:
            conn.execute("ALTER TABLE tageslog ADD COLUMN einspeisung_kwh REAL")
        except Exception:
            pass


def db_log_control():
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO steuerlog VALUES (?,?,?,?,?,?,?,?,?)",
            (
                datetime.now().isoformat(timespec="seconds"),
                round(state["budget_kwh"], 2),
                round(state["pv_prognose_kwh"], 2),
                round(state["pv_heute_kwh"], 2),
                int(state["batterie_soc"]),
                int(state["ziel_strom_a"]),
                int(state["car_connected"]),
                state["action"],
                state["grund"],
            ),
        )


def db_update_today(charged_kwh, einspeisung_kwh, haus_ohne_auto=None):
    """Schreibt den aktuellen Tagesstand in die DB. haus_ohne_auto optional überschreibbar."""
    if haus_ohne_auto is None:
        haus_ohne_auto = max(state.get("haus_last_kwh", 0) - charged_kwh, 0)
    with sqlite3.connect(DB_PATH) as conn:
        conn.execute(
            "INSERT OR REPLACE INTO tageslog VALUES (?,?,?,?,?,?,?,?,?)",
            (
                str(date.today()),
                round(state["pv_prognose_kwh"], 2),
                round(state["pv_heute_kwh"], 2),
                round(haus_ohne_auto, 2),
                round(state["haus_ema_kwh"], 2),
                round(charged_kwh, 2),
                round(state["budget_kwh"], 2),
                int(state["batterie_soc"]),
                round(einspeisung_kwh, 2),
            ),
        )


def db_history_days(n=14):
    with sqlite3.connect(DB_PATH) as conn:
        rows = conn.execute(
            """SELECT datum, pv_prognose_kwh, pv_real_kwh, haus_last_kwh,
                      haus_ema_kwh, auto_geladen_kwh, budget_kwh,
                      COALESCE(einspeisung_kwh, 0)
               FROM tageslog ORDER BY datum DESC LIMIT ?""",
            (n,),
        ).fetchall()
    return [
        dict(zip(["datum", "prognose", "real", "haus", "haus_ema", "auto", "budget", "einspeisung"], r))
        for r in rows
    ]


def db_control_log(n=100):
    with sqlite3.connect(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT ts, budget_kwh, ziel_a, auto_da, action, grund FROM steuerlog ORDER BY ts DESC LIMIT ?",
            (n,),
        ).fetchall()
    return [dict(zip(["ts", "budget", "strom_a", "auto", "action", "grund"], r)) for r in rows]

# ---------------------------------------------------------------------------
# HA API
# ---------------------------------------------------------------------------

def ha_sensor(entity_id, required=False):
    try:
        r = requests.get(get_ha_api_url(entity_id), headers=get_ha_headers(), timeout=8)
        val = r.json().get("state", "0")
        return float(val)
    except Exception as e:
        log.warning(f"HA {entity_id}: {e}")
        if required:
            raise
        return 0.0

def ha_set_select(entity_id: str, option: str):
    """Setzt eine HA select-Entity auf den gewünschten Wert."""
    try:
        base = get_ha_api_url()  # liefert z.B. http://supervisor/core/api
        r = requests.post(
            f"{base}/services/select/select_option",
            headers=get_ha_headers(),
            json={"entity_id": entity_id, "option": option},
            timeout=8
        )
        log.info(f"HA select {entity_id} → {option} ({r.status_code}) {r.text[:120]}")
        dlog(f"HA select {entity_id} → {option} | HTTP {r.status_code}", "action")
    except Exception as e:
        log.error(f"ha_set_select {entity_id}: {e}")

def ha_sensor_last_changed(entity_id) -> str | None:
    """Gibt 'last_changed' eines HA Sensors zurück — nur wenn der Wert sich wirklich geändert hat."""
    try:
        r = requests.get(get_ha_api_url(entity_id), headers=get_ha_headers(), timeout=8)
        return r.json().get("last_changed")
    except Exception:
        return None

# ---------------------------------------------------------------------------
# HA Push-Benachrichtigungen
# ---------------------------------------------------------------------------

# Spam-Schutz: welche Notifications wurden heute schon gesendet?
_notify_sent: dict = {"budget_low": False, "deadline_urgent": False, "laden_fertig": False}

def ha_notify(title: str, message: str) -> bool:
    """Sendet eine Push-Benachrichtigung über HA Notification Service.
    Gibt True zurück wenn erfolgreich, False sonst."""
    target = user_settings.get("notify_target", "").strip()
    if not target:
        return False
    try:
        url = get_ha_api_url().rstrip("/") + f"/services/notify/{target}"
        r = requests.post(url, headers=get_ha_headers(), timeout=8,
                          json={"title": title, "message": message})
        ok = r.status_code in (200, 201)
        if not ok:
            log.warning(f"HA notify fehlgeschlagen: HTTP {r.status_code}")
        return ok
    except Exception as e:
        log.warning(f"HA notify Fehler: {e}")
        return False

def check_and_send_notifications(action, budget_verfuegbar_echt, ansteck_urgency, car_connected, charged_today):
    """Prüft Notification-Trigger und sendet Benachrichtigungen (max. 1× pro Ereignis)."""
    # Budget fast leer
    if user_settings.get("notify_budget_low") and user_settings.get("notify_target"):
        threshold = user_settings.get("notify_budget_low_kwh", 0.5)
        if budget_verfuegbar_echt <= threshold and budget_verfuegbar_echt >= 0 and not _notify_sent["budget_low"]:
            ok = ha_notify("⚡ Smart EV Charger",
                           f"Budget fast leer — noch {budget_verfuegbar_echt:.2f} kWh verfügbar.")
            if ok:
                _notify_sent["budget_low"] = True
                log.info("Notification gesendet: Budget fast leer")
        elif budget_verfuegbar_echt > threshold + 0.2:
            _notify_sent["budget_low"] = False  # Reset wenn Budget wieder ausreichend

    # Deadline drängt (< 60 Min)
    if user_settings.get("notify_deadline_urgent") and user_settings.get("notify_target"):
        if ansteck_urgency == "urgent" and not _notify_sent["deadline_urgent"]:
            ok = ha_notify("🔌 Smart EV Charger",
                           "Auto jetzt anschließen — weniger als 1 Stunde bis Budget sinkt!")
            if ok:
                _notify_sent["deadline_urgent"] = True
                log.info("Notification gesendet: Deadline urgent")
        elif ansteck_urgency != "urgent":
            _notify_sent["deadline_urgent"] = False  # Reset wenn Deadline nicht mehr dringend

    # Laden fertig (Auto war angesteckt + hat geladen, jetzt weg)
    if user_settings.get("notify_laden_fertig") and user_settings.get("notify_target"):
        was_charging = state.get("_was_charging", False)
        if was_charging and not car_connected and not _notify_sent["laden_fertig"]:
            ok = ha_notify("✅ Smart EV Charger",
                           f"Laden abgeschlossen — {charged_today:.1f} kWh heute geladen.")
            if ok:
                _notify_sent["laden_fertig"] = True
                log.info("Notification gesendet: Laden fertig")
        if car_connected and action == "laden":
            state["_was_charging"] = True
        if not car_connected:
            if not state.get("_was_charging"):
                _notify_sent["laden_fertig"] = False  # Reset wenn neues Auto angesteckt wird
            state["_was_charging"] = False


# ---------------------------------------------------------------------------
# evcc API
# ---------------------------------------------------------------------------

def _ha_bool(entity_id: str) -> bool:
    """Liest einen HA binary_sensor als bool (on/true/1 → True)."""
    if not entity_id:
        return False
    try:
        r = requests.get(get_ha_api_url(entity_id), headers=get_ha_headers(), timeout=8)
        return r.json().get("state", "off").lower() in ("on", "true", "1", "yes", "connected", "home")
    except Exception:
        return False


def _ha_direct_loadpoint() -> dict:
    """Liefert Loadpoint-Status aus HA-Entities (ohne evcc)."""
    s         = user_settings
    connected = _ha_bool(s.get("wallbox_connected", ""))
    charging  = _ha_bool(s.get("wallbox_charging",  ""))
    min_a     = int(s.get("min_strom_a", 6))
    state["evcc_online"] = True   # kein evcc → kein Badge nötig
    return {
        "connected":           connected,
        "charging":            charging,
        "mode":                "on" if charging else "off",
        "minCurrent":          min_a,
        "maxCurrent":          16,
        "phases":              1,
        "effectiveMinCurrent": min_a,
        "effectiveMaxCurrent": 16,
        "sessionEnergy":       0,   # wird separat über wallbox_energy gelesen
    }


def _ha_direct_set_charging(active: bool):
    """Schaltet Wallbox über HA switch/input_boolean."""
    entity = user_settings.get("wallbox_switch", "").strip()
    if not entity:
        return
    domain  = entity.split(".")[0]
    service = "turn_on" if active else "turn_off"
    try:
        r = requests.post(
            get_ha_api_url().rstrip("/") + f"/services/{domain}/{service}",
            headers=get_ha_headers(),
            json={"entity_id": entity},
            timeout=8,
        )
        log.info(f"HA direct {service} {entity} → {r.status_code}")
    except Exception as e:
        log.error(f"HA direct set_charging({active}): {e}")


def _ha_direct_set_current(amps: int):
    """Setzt Ladestrom über HA number entity."""
    entity = user_settings.get("wallbox_current", "").strip()
    if not entity:
        return
    try:
        r = requests.post(
            get_ha_api_url().rstrip("/") + "/services/number/set_value",
            headers=get_ha_headers(),
            json={"entity_id": entity, "value": str(amps)},
            timeout=8,
        )
        log.info(f"HA direct set_current {entity} → {amps}A ({r.status_code})")
    except Exception as e:
        log.error(f"HA direct set_current({amps}A): {e}")


def evcc_loadpoint():
    if user_settings.get("wallbox_type", "evcc") == "ha_direct":
        return _ha_direct_loadpoint()
    try:
        r = requests.get(f"{get_evcc_url()}/api/state", timeout=8)
        lps = r.json().get("loadpoints", [])
        lp_id = get_loadpoint_id()
        state["evcc_online"] = True
        return lps[lp_id - 1] if len(lps) >= lp_id else {}
    except Exception as e:
        log.warning(f"evcc nicht erreichbar: {e}")
        state["evcc_online"] = False
        return {}


def evcc_charged_today(lp: dict | None = None) -> float:  # noqa: C901
    """Geladene Energie heute in kWh."""
    if user_settings.get("wallbox_type", "evcc") == "ha_direct":
        entity = user_settings.get("wallbox_energy", "").strip()
        if not entity:
            return 0.0
        try:
            return round(float(ha_sensor(entity) or 0), 3)
        except (TypeError, ValueError):
            return 0.0

    today = str(date.today())
    sessions_total = 0.0
    try:
        r = requests.get(f"{get_evcc_url()}/api/sessions", timeout=8)
        sessions = r.json()
        if isinstance(sessions, dict):
            sessions = next(iter(sessions.values()), [])
        for s in sessions:
            if s.get("created", "")[:10] == today:
                sessions_total += (s.get("chargedEnergy", 0) or 0)
    except Exception as e:
        log.warning(f"evcc sessions: {e}")

    # Live-Wert der aktiven Session aus Loadpoint-State (Wh → kWh)
    car_charging     = lp.get("charging", False)  if lp else False
    live_session_kwh = (lp.get("sessionEnergy") or 0) / 1000.0 if lp else 0.0

    if car_charging and live_session_kwh > 0:
        # sessions_total kann noch 0 sein (Session noch nicht abgeschlossen)
        # oder einen veralteten Wert enthalten.
        if sessions_total > live_session_kwh + 0.1:
            # Abgeschlossene frühere Session(s) + aktive Session separat
            total = sessions_total + live_session_kwh
            dlog(f"charged_today: sessions={sessions_total:.3f} + live={live_session_kwh:.3f} = {total:.3f} kWh", "info")
        else:
            # Nur eine Session heute — live-Wert ist genauer
            total = max(sessions_total, live_session_kwh)
            dlog(f"charged_today: sessions={sessions_total:.3f} → live={live_session_kwh:.3f} kWh (live genauer)", "info")
    else:
        total = sessions_total

    return round(total, 3)


def evcc_set_mincurrent(amps: int):
    if user_settings.get("wallbox_type", "evcc") == "ha_direct":
        _ha_direct_set_current(amps)
        return
    try:
        r = requests.post(f"{get_evcc_url()}/api/loadpoints/{get_loadpoint_id()}/mincurrent/{amps}", timeout=8)
        log.info(f"evcc minCurrent={amps}A → {r.text.strip()}")
    except Exception as e:
        log.error(f"evcc mincurrent: {e}")


def evcc_set_maxcurrent(amps: int):
    if user_settings.get("wallbox_type", "evcc") == "ha_direct":
        _ha_direct_set_current(amps)
        return
    try:
        r = requests.post(f"{get_evcc_url()}/api/loadpoints/{get_loadpoint_id()}/maxcurrent/{amps}", timeout=8)
        log.info(f"evcc maxCurrent={amps}A → {r.text.strip()}")
    except Exception as e:
        log.error(f"evcc maxcurrent: {e}")


def evcc_set_mode(mode: str):
    if user_settings.get("wallbox_type", "evcc") == "ha_direct":
        _ha_direct_set_charging(mode in ("minpv", "pv", "now"))
        return
    try:
        r = requests.post(f"{get_evcc_url()}/api/loadpoints/{get_loadpoint_id()}/mode/{mode}", timeout=8)
        log.info(f"evcc mode={mode} → {r.text.strip()}")
    except Exception as e:
        log.error(f"evcc mode: {e}")


# ---------------------------------------------------------------------------
# Growatt Modbus TCP — BatDischargePowerLimit
# ---------------------------------------------------------------------------
# USR IOT Adapter: 192.168.0.47:21  (Modbus RTU over TCP, Slave-ID 1)
# Register 3036 = BatDischargePowerLimit (W, Schreibwert = Watt, Max 10000)
# Growatt MOD TL3-XH Protokoll v1.24, Holding-Register Bereich 3000–3249
# ---------------------------------------------------------------------------
_MODBUS_HOST    = "192.168.0.47"
_MODBUS_PORT    = 21
_MODBUS_SLAVE   = 1
_REG_BAT_DISCH  = 3036   # BatDischargePowerLimit (W)
_BAT_DISCH_MAX  = 10000  # W — Growatt-Default (Vollleistung freigeben)

_modbus_lock = threading.Lock()


def _growatt_write_register(register: int, value: int) -> bool:
    """Schreibt einen Wert in ein Growatt Holding-Register via Modbus TCP."""
    if not _PYMODBUS_OK:
        log.warning("pymodbus nicht verfügbar — Modbus-Schreiben übersprungen")
        return False
    try:
        with _modbus_lock:
            client = _ModbusTcpClient(_MODBUS_HOST, port=_MODBUS_PORT, timeout=5)
            if not client.connect():
                log.error(f"Modbus TCP: Verbindung zu {_MODBUS_HOST}:{_MODBUS_PORT} fehlgeschlagen")
                return False
            result = client.write_register(register, value, slave=_MODBUS_SLAVE)
            client.close()
            if result.isError():
                log.error(f"Modbus Schreibfehler Reg {register}={value}: {result}")
                return False
            log.info(f"Modbus OK: Reg {register} → {value}")
            return True
    except Exception as e:
        log.error(f"Modbus Ausnahme: {e}")
        return False


def growatt_set_discharge_limit(watts: int):
    """Setzt BatDischargePowerLimit auf 'watts'. 0 = Entladung gesperrt, 10000 = max."""
    watts = max(0, min(watts, _BAT_DISCH_MAX))
    dlog(f"[Modbus] BatDischargePowerLimit → {watts} W", "info")
    _growatt_write_register(_REG_BAT_DISCH, watts)


def growatt_reset_discharge_limit():
    """Setzt BatDischargePowerLimit zurück auf Maximum (Growatt-Default)."""
    dlog(f"[Modbus] BatDischargePowerLimit reset → {_BAT_DISCH_MAX} W", "info")
    _growatt_write_register(_REG_BAT_DISCH, _BAT_DISCH_MAX)


# ---------------------------------------------------------------------------
# Schnell-Regler — eigener Thread, läuft alle 12s wenn Schnell aktiv
# Regelt evcc maxcurrent anhand der Netzleistung: Grid > 0W → runter, < 0W → rauf
# Hysterese: nur Änderung wenn Delta ≥ 1A (verhindert Flackern)
# ---------------------------------------------------------------------------
_schnell_thread_running = False
_schnell_thread_lock    = threading.Lock()

def _schnell_regelung_thread():
    """Regelschleife für Schnell-Modus. Startet/stoppt automatisch."""
    global _schnell_thread_running
    log.info("[Schnell-Regler] Gestartet")
    interval     = 12   # Sekunden zwischen Regelschritten
    first_delay  = 4    # Kurz warten damit evcc + Growatt sich einpendeln können

    time.sleep(first_delay)

    while state.get("laden_schnell"):
        if not state.get("car_connected"):
            time.sleep(interval)
            continue
        if not state.get("laden_schnell"):
            break

        # Auto-Deaktivierung: Speicher hat min_soc erreicht → kein Entladen mehr möglich
        batt_soc_now = state.get("batterie_soc") or 0
        min_soc_val  = get_batt_min_soc()
        if batt_soc_now <= min_soc_val:
            log.info(f"[Schnell-Regler] Speicher bei min_soc ({batt_soc_now}% ≤ {min_soc_val}%) → Schnell-Modus deaktiviert")
            state["laden_schnell"] = False
            break

        try:
            # Aktuelle Netzleistung lesen (positiv = Bezug, negativ = Einspeisung)
            grid_w   = ha_sensor(get_sensor("grid_power")) or 0
            lp       = evcc_loadpoint()
            phases   = max(1, min(3, int(lp.get("activePhases") or lp.get("phases") or 3)))
            cur_max  = int(lp.get("maxCurrent") or 16)
            # Im Schnell-Modus immer bis 6A gehen dürfen (Inverter-Limit überbrücken)
            # min_strom_a gilt nur für normalen minpv-Betrieb
            min_a    = 6

            # Wieviel Ampere entspricht dem aktuellen Netz-Ungleichgewicht?
            delta_a = -round(grid_w / 230 / phases)   # positiv wenn wir erhöhen können
            new_max = max(min_a, min(16, cur_max + delta_a))

            dlog(f"[Schnell-Regler] Grid={grid_w:+.0f}W Δ{delta_a:+d}A → {cur_max}A→{new_max}A ({phases}Ph) SOC={batt_soc_now}%", "info")

            if abs(new_max - cur_max) >= 1:
                evcc_set_maxcurrent(new_max)
        except Exception as e:
            log.error(f"[Schnell-Regler] Fehler: {e}")
        time.sleep(interval)

    # Aufräumen: maxcurrent zurücksetzen, evcc zurück auf normalen Modus
    evcc_set_maxcurrent(16)
    if not state.get("laden_schnell"):
        # Sauber deaktivieren: Mode auf off setzen (Haupt-Loop regelt dann neu)
        evcc_set_mode("off")
    _schnell_thread_running = False
    log.info("[Schnell-Regler] Beendet")


def start_schnell_regler():
    """Startet den Schnell-Regler-Thread falls noch nicht aktiv."""
    global _schnell_thread_running
    with _schnell_thread_lock:
        if _schnell_thread_running:
            return
        _schnell_thread_running = True
        t = threading.Thread(target=_schnell_regelung_thread, daemon=True)
        t.start()

# ---------------------------------------------------------------------------
# Sonnenzeiten (Näherung für ~LATITUDE_DEG °N, für ganz Deutschland ausreichend)
# ---------------------------------------------------------------------------

def _daylight_params():
    """Gibt (daylight_total_h, sunset_h) zurück — Näherungsformel basierend auf konfiguriertem Breitengrad."""
    doy = datetime.now().timetuple().tm_yday
    lat = user_settings.get("latitude", LATITUDE_DEG)
    amplitude = 4.5 * (lat / 51.0)   # skaliert mit Breitengrad (51°N = Referenz)
    daylight = 12 + amplitude * math.sin((doy - 80) * 2 * math.pi / 365)
    sunset_h = 12 + daylight / 2
    return daylight, sunset_h


def remaining_daylight_hours() -> float:
    _, sunset_h = _daylight_params()
    now_h = datetime.now().hour + datetime.now().minute / 60
    return max(sunset_h - now_h, 0.25)

# ---------------------------------------------------------------------------
# Optimaler Ansteck-Zeitpunkt
# ---------------------------------------------------------------------------

def calc_ansteck_deadline(budget_kwh, remaining_pv_forecast, pv_leistung, rem_hours, budget_db, haus_ema=10.0, daylight_total=14.0, batt_soc=100, ziel_soc=100, batt_kap=10.0, batt_charge_kw=None):
    """
    Berechnet den SPÄTESTEN Zeitpunkt zum Anschließen des Autos.
    = Wann ist der Speicher voll (ziel_soc)? Ab dann geht PV-Überschuss ins Netz → Budget sinkt.
    Gibt zurück: (zeitstring, grund, urgency, minutes_left)  urgency: "ok" | "warn" | "urgent"
    """
    batt_soc = batt_soc or 0
    if rem_hours <= 0.5 or budget_kwh <= 0.2:
        return None, None, None, None

    # Speicher bereits voll → Budget sinkt jetzt schon
    if batt_soc >= ziel_soc:
        return "JETZT!", "Speicher voll — Überschuss geht ins Netz", "urgent", 0

    # Restkapazität bis ziel_soc
    batt_rest_kwh = max((ziel_soc - batt_soc) / 100 * batt_kap, 0)
    if batt_rest_kwh < 0.1:
        return None, None, None, None

    # Laderate bestimmen — Priorität:
    # 1. CV-Phase (SOC > 85%): Sensor am präzisesten, kennt Drosselung
    # 2. Gelernte Wochentagsrate (aus Steuerlog-History): realistischer Tages-Durchschnitt
    # 3. Forecast-basiert (Fallback wenn noch keine Lernwerte vorhanden)
    haus_kw_est  = haus_ema / max(daylight_total, 1)
    avg_pv_kw    = remaining_pv_forecast / max(rem_hours, 0.5)
    net_pv_kw    = max(avg_pv_kw - haus_kw_est, 0)

    learned_rate = None
    rate_map     = user_settings.get("batt_fill_rate_wochentag", {})
    wd_key       = str(date.today().weekday())
    if wd_key in rate_map:
        learned_rate = rate_map[wd_key]

    cv_threshold = ziel_soc * 0.85
    if batt_soc >= cv_threshold and batt_charge_kw and batt_charge_kw > 0.05:
        charge_rate_kw = batt_charge_kw          # CV-Phase: Sensor
    elif learned_rate and learned_rate > 0.05:
        charge_rate_kw = learned_rate             # Gelernte Durchschnittsrate
    elif net_pv_kw > 0.05:
        charge_rate_kw = net_pv_kw               # Forecast-Fallback
    else:
        charge_rate_kw = DEFAULT_BATT_CHARGE_KW  # Letzter Fallback: konservative Schätzung

    if charge_rate_kw < 0.05:
        return None, None, None, None

    stunden  = batt_rest_kwh / charge_rate_kw
    deadline = datetime.now() + timedelta(hours=stunden)

    # Deadline auf heutigen Sonnenuntergang deckeln
    _, sunset_h = _daylight_params()
    today_sunset = datetime.now().replace(hour=int(sunset_h), minute=int((sunset_h % 1) * 60), second=0, microsecond=0)
    if deadline > today_sunset:
        return None, None, None, None

    deadline_str  = deadline.strftime("%H:%M")
    minutes_left  = round(stunden * 60)

    if minutes_left < 60:
        urgency = "urgent"
        grund   = f"Weniger als 1h bis Budget sinkt — danach nicht mehr {budget_kwh:.1f} kWh nutzbar"
    elif minutes_left < 120:
        urgency = "warn"
        grund   = f"Weniger als 2h bis Budget sinkt — danach nicht mehr {budget_kwh:.1f} kWh nutzbar"
    else:
        urgency = "ok"
        grund   = f"Volles Budget ({budget_kwh:.1f} kWh) nutzbar bis {deadline_str} Uhr"

    return deadline_str + " Uhr", grund, urgency, minutes_left

# ---------------------------------------------------------------------------
# Lernfunktion (täglich 22 Uhr)
# ---------------------------------------------------------------------------

def daily_learning():
    """Täglicher Lernlauf (~22 Uhr): aktualisiert Haus-EMA, PV-Faktor,
    Abend-Entnahme und Batterie-Laderate per exponentieller Glättung (0.7/0.3)."""
    log.info("=== Tages-Lernlauf ===")
    haus_last   = ha_sensor(get_sensor("haus_last"))
    lp          = evcc_loadpoint()
    charged_kwh = evcc_charged_today(lp=lp)

    haus_ohne_auto = max(haus_last - charged_kwh, 0)
    wd     = "6" if is_feiertag() else str(date.today().weekday())  # Feiertag → Sonntag
    wdname = WOCHENTAGE[int(wd)]

    if 1.0 < haus_ohne_auto < 25.0:
        ema_map = user_settings["haus_ema_wochentag"]
        old = ema_map.get(wd, _DEV_CFG.get("haus_ema_kwh", 11.0))
        new = round(old * 0.7 + haus_ohne_auto * 0.3, 2)
        ema_map[wd] = new
        user_settings["haus_ema_wochentag"] = ema_map
        save_settings(user_settings)
        log.info(f"Haus-EMA {wdname}: {old:.2f} → {new:.2f} kWh (Heute: {haus_ohne_auto:.2f} kWh)")
    else:
        log.warning(f"Haus-Verbrauch {haus_ohne_auto:.2f} kWh unplausibel, EMA {wdname} nicht aktualisiert")

    einspeisung_kwh = _daily_budget.get("einspeisung_kwh", 0)
    log.info(f"Einspeisung heute: {einspeisung_kwh:.2f} kWh | Auto geladen: {charged_kwh:.2f} kWh")
    if einspeisung_kwh > 2.0:
        log.warning(f"Hohe Einspeisung ({einspeisung_kwh:.1f} kWh) — System war zu konservativ oder Auto nicht angeschlossen.")

    pv_real           = ha_sensor(get_sensor("pv_real"))
    pv_prognose_heute = _daily_budget.get("pv_prognose_kwh", 0)
    if pv_prognose_heute and pv_prognose_heute > 2.0 and pv_real > 1.0:
        heute_ratio = pv_real / pv_prognose_heute
        if 0.7 <= heute_ratio <= 1.3:
            old_faktor = user_settings.get("pv_faktor", 1.0)
            new_faktor = round(old_faktor * 0.7 + heute_ratio * 0.3, 3)
            user_settings["pv_faktor"] = new_faktor
            save_settings(user_settings)
            log.info(
                f"PV-Faktor: {old_faktor:.3f} → {new_faktor:.3f} "
                f"(real={pv_real:.1f} kWh / forecast={pv_prognose_heute:.1f} kWh = {heute_ratio:.3f})"
            )
        else:
            log.warning(
                f"PV-Faktor NICHT aktualisiert: Abweichung zu groß "
                f"(real={pv_real:.1f} kWh / forecast={pv_prognose_heute:.1f} kWh = {heute_ratio:.2f}x) "
                f"— Forecast-Sensor möglicherweise inkonsistent."
            )
    else:
        log.warning(f"PV-Faktor nicht aktualisiert: real={pv_real:.1f} / forecast={pv_prognose_heute or 0:.1f} kWh")

    # --- Abend-Entnahme lernen (SOC Sonnenuntergang → SOC jetzt) ---
    soc_sunset = _daily_budget.get("soc_at_sunset")
    soc_jetzt  = state.get("batterie_soc")
    batt_kap   = get_batt_kap()
    if soc_sunset is not None and soc_jetzt is not None and soc_sunset > soc_jetzt:
        abend_entnahme = round((soc_sunset - soc_jetzt) / 100 * batt_kap, 2)
        abend_map = user_settings.setdefault("abend_entnahme_wochentag", {str(i): 2.0 for i in range(7)})
        old_abend = abend_map.get(wd, 2.0)
        new_abend = round(old_abend * 0.7 + abend_entnahme * 0.3, 2)
        abend_map[wd] = new_abend
        user_settings["abend_entnahme_wochentag"] = abend_map
        save_settings(user_settings)
        log.info(f"Abend-Entnahme {wdname}: {old_abend:.2f} → {new_abend:.2f} kWh (heute: {abend_entnahme:.2f} kWh, SOC {soc_sunset:.0f}%→{soc_jetzt:.0f}%)")
    else:
        log.info(f"Abend-Entnahme nicht gelernt (soc_sunset={soc_sunset}, soc_jetzt={soc_jetzt})")

    # --- Batterie-Laderate lernen aus Steuerlog ---
    # Suche: frühester Eintrag heute (Morgen-SOC) + erster Eintrag mit SOC >= 95
    try:
        today_str      = str(date.today())
        tomorrow_str   = str(date.today() + timedelta(days=1))
        batt_kap_l     = get_batt_kap()
        with sqlite3.connect(DB_PATH) as conn:
            # Frühester Eintrag heute mit SOC > 5% (Nacht-Werte ignorieren)
            row_start = conn.execute(
                "SELECT ts, batt_soc FROM steuerlog WHERE ts >= ? AND ts < ? AND batt_soc > 5 ORDER BY ts ASC LIMIT 1",
                (today_str, tomorrow_str)
            ).fetchone()
            # Erster Eintrag heute mit SOC >= 95
            row_full = conn.execute(
                "SELECT ts, batt_soc FROM steuerlog WHERE ts >= ? AND ts < ? AND batt_soc >= 95 ORDER BY ts ASC LIMIT 1",
                (today_str, tomorrow_str)
            ).fetchone()

        if row_start and row_full:
            from datetime import datetime as dt
            ts_start = dt.fromisoformat(row_start[0])
            ts_full  = dt.fromisoformat(row_full[0])
            soc_start = row_start[1]
            fill_hours = (ts_full - ts_start).total_seconds() / 3600

            if fill_hours >= 0.5:  # mind. 30min — Ausreißer ignorieren
                batt_filled = max((95 - soc_start) / 100 * batt_kap_l, 0)
                if batt_filled > 0.5:
                    fill_rate = round(batt_filled / fill_hours, 3)
                    rate_map  = user_settings.setdefault("batt_fill_rate_wochentag", {})
                    old_rate  = rate_map.get(wd)
                    if old_rate:
                        new_rate = round(old_rate * 0.7 + fill_rate * 0.3, 3)
                    else:
                        new_rate = fill_rate  # Erster Wert: direkt übernehmen
                    rate_map[wd] = new_rate
                    user_settings["batt_fill_rate_wochentag"] = rate_map
                    save_settings(user_settings)
                    log.info(
                        f"Batt-Laderate {wdname}: {old_rate or '–'} → {new_rate:.3f} kW "
                        f"(SOC {soc_start}%→95% in {fill_hours:.1f}h = {fill_rate:.3f} kW)"
                    )
                else:
                    log.info(f"Batt-Laderate nicht gelernt: SOC-Hub zu klein ({soc_start}%→95%)")
            else:
                log.info(f"Batt-Laderate nicht gelernt: fill_hours={fill_hours:.2f} zu kurz")
        else:
            log.info(f"Batt-Laderate nicht gelernt: SOC heute nicht auf 95% gestiegen (row_start={row_start}, row_full={row_full})")
    except Exception as e:
        log.error(f"Batt-Laderate Lernfehler: {e}")

    db_update_today(charged_kwh, einspeisung_kwh, haus_ohne_auto)

# ---------------------------------------------------------------------------
# Solcast Direkt-API
# ---------------------------------------------------------------------------
def get_ha_language() -> str:
    """Liest HA-Systemsprache über Supervisor API. Fallback: 'de'."""
    try:
        token = os.environ.get("SUPERVISOR_TOKEN", "")
        r = requests.get(
            "http://supervisor/core/api/config",
            headers={"Authorization": f"Bearer {token}"},
            timeout=5
        )
        lang = r.json().get("language", "de")
        return lang[:2].lower()  # "de_DE" → "de"
    except Exception:
        return "de"

_SOLCAST_CACHE_FILE    = DATA_DIR / "solcast_cache.json"
_SOLCAST_CACHE_MIN_MIN = 180  # Minuten zwischen API-Calls (3h → max 8 Calls/Tag)

def fetch_solcast_direct():
    """Ruft Solcast-API direkt ab. Cache 3h. Gibt (remaining_today, total_today, total_tomorrow) zurück."""
    api_key     = user_settings.get("solcast_api_key",     "").strip()
    resource_id = user_settings.get("solcast_resource_id", "").strip()
    if not api_key or not resource_id:
        log.warning("Solcast Direkt: API-Key oder Resource-ID nicht konfiguriert")
        return None, None, None

    # Cache prüfen
    cache = {}
    if _SOLCAST_CACHE_FILE.exists():
        try:
            cache = json.loads(_SOLCAST_CACHE_FILE.read_text())
        except Exception:
            pass
    last_fetch = cache.get("last_fetch_ts")
    if last_fetch:
        age_min = (datetime.now() - datetime.fromisoformat(last_fetch)).total_seconds() / 60
        if age_min < _SOLCAST_CACHE_MIN_MIN:
            dlog(f"Solcast Cache: {age_min:.0f} min alt → kein neuer API-Call", "info")
            return cache.get("remaining_today"), cache.get("total_today"), cache.get("total_tomorrow")

    # API-Call
    try:
        url  = f"https://api.solcast.com.au/rooftop_sites/{resource_id}/forecasts?format=json&hours=48"
        resp = requests.get(url, headers={"Authorization": f"Bearer {api_key}"}, timeout=15)
        resp.raise_for_status()
        forecasts = resp.json().get("forecasts", [])
    except Exception as e:
        log.error(f"Solcast Direkt API-Fehler: {e}")
        return cache.get("remaining_today"), cache.get("total_today"), cache.get("total_tomorrow")

    # Perioden auswerten (UTC → lokal)
    now_local      = datetime.now().astimezone()
    today_date     = now_local.date()
    tomorrow_date  = today_date + timedelta(days=1)
    total_today    = 0.0
    remaining_today = 0.0
    total_tomorrow  = 0.0

    for f in forecasts:
        try:
            period_end   = datetime.fromisoformat(f["period_end"].replace("Z", "+00:00")).astimezone()
            period_start = period_end - timedelta(minutes=30)
            kwh = (f.get("pv_estimate") or 0) * 0.5  # kW × 0.5h
            if period_end.date() == today_date:
                total_today += kwh
                if period_start >= now_local:
                    remaining_today += kwh
            elif period_end.date() == tomorrow_date:
                total_tomorrow += kwh
        except Exception:
            continue

    total_today     = round(total_today,     3)
    remaining_today = round(remaining_today, 3)
    total_tomorrow  = round(total_tomorrow,  3)

    new_cache = {
        "last_fetch_ts":  datetime.now().isoformat(timespec="seconds"),
        "total_today":    total_today,
        "remaining_today": remaining_today,
        "total_tomorrow": total_tomorrow,
    }
    try:
        _SOLCAST_CACHE_FILE.write_text(json.dumps(new_cache, indent=2))
    except Exception as e:
        log.warning(f"Solcast Cache speichern fehlgeschlagen: {e}")

    dlog(f"Solcast Direkt: heute={total_today:.2f} kWh, verbleibend={remaining_today:.2f} kWh, morgen={total_tomorrow:.2f} kWh", "info")
    return remaining_today, total_today, total_tomorrow


# ---------------------------------------------------------------------------
# Steuer-Schleife
# ---------------------------------------------------------------------------

def control_loop():
    """Haupt-Steuerlogik: liest Sensoren, berechnet alle 5 Module (Budget, Gate,
    Countdown, Deadline, Schnell) und setzt evcc-Modus + Mindeststrom."""
    # --- Sensoren lesen ---
    if user_settings.get("forecast_provider") == "solcast_direct":
        _sc_rem, _sc_total, _sc_morgen = fetch_solcast_direct()
        remaining_pv_forecast_raw = _sc_rem   if _sc_rem   is not None else 0.0
        pv_prognose_total_raw     = _sc_total if _sc_total is not None else 0.0
        pv_prognose_morgen        = _sc_morgen if _sc_morgen is not None else 0.0
        # Timestamp aus Cache-Datei
        try:
            _cache = json.loads(_SOLCAST_CACHE_FILE.read_text())
            forecast_last_updated_iso = _cache.get("last_fetch_ts")
        except Exception:
            forecast_last_updated_iso = None
    else:
        remaining_pv_forecast_raw = ha_sensor(get_sensor("pv_remaining"),   required=True)
        pv_prognose_total_raw     = ha_sensor(get_sensor("pv_heute_total"),  required=True)
        pv_prognose_morgen        = ha_sensor(get_sensor("pv_morgen"))
        # last_changed von pv_heute_total — ändert sich nur bei echtem Forecast-Update
        forecast_last_updated_iso = ha_sensor_last_changed(get_sensor("pv_heute_total"))

    # "vor X Min." aus ISO-Timestamp berechnen
    forecast_updated_str = None
    if forecast_last_updated_iso:
        try:
            ts = datetime.fromisoformat(forecast_last_updated_iso.replace("Z", "+00:00"))
            age_min = int((datetime.now().astimezone() - ts.astimezone()).total_seconds() / 60)
            if age_min < 60:
                forecast_updated_str = f"vor {age_min} Min."
            else:
                forecast_updated_str = f"vor {age_min // 60}h {age_min % 60}min"
        except Exception:
            pass
    pv_heute_raw = ha_sensor(get_sensor("pv_real"),      required=True)
    pv_leistung_pre = ha_sensor(get_sensor("pv_leistung"))  # früh lesen für Glitch-Check
    # Glitch-Schutz: Wenn Forecast-Sensoren 0 melden aber PV noch aktiv → letzten Wert halten
    _last_rem   = _daily_budget.get("last_valid_remaining_pv",  remaining_pv_forecast_raw)
    _last_total = _daily_budget.get("last_valid_prognose_total", pv_prognose_total_raw)
    pv_aktiv_now = (pv_leistung_pre or 0) > 150
    if remaining_pv_forecast_raw > 0.05:
        remaining_pv_forecast = remaining_pv_forecast_raw
        if pv_aktiv_now:  # nur bei aktiver PV speichern — kein Nacht-Wert als Fallback
            _daily_budget["last_valid_remaining_pv"] = remaining_pv_forecast
    elif pv_aktiv_now and _last_rem and _last_rem > 0.05:
        remaining_pv_forecast = _last_rem  # Sensor-Glitch, alten Wert halten
        dlog(f"Sensor-Glitch remaining_pv: raw=0 aber PV aktiv → letzter Wert {_last_rem:.2f} kWh", "info")
    elif pv_aktiv_now:
        # Letzter Fallback: aus aktueller Leistung × verbleibende Tageslicht-Stunden schätzen
        _rem_h = remaining_daylight_hours()
        remaining_pv_forecast = round((pv_leistung_pre or 0) / 1000 * _rem_h * 0.65, 2)
        dlog(f"Forecast-Fallback (Sensor komplett tot): {pv_leistung_pre:.0f}W × {_rem_h:.1f}h × 0.65 = {remaining_pv_forecast:.2f} kWh", "info")
    else:
        remaining_pv_forecast = 0.0
    if pv_prognose_total_raw > 0.05:
        pv_prognose_total = pv_prognose_total_raw
        _daily_budget["last_valid_prognose_total"] = pv_prognose_total
    elif pv_aktiv_now and _last_total > 0.05:
        pv_prognose_total = _last_total
        dlog(f"Sensor-Glitch pv_heute_total: raw=0 aber PV aktiv → letzter Wert {_last_total:.2f} kWh", "info")
    else:
        pv_prognose_total = pv_prognose_total_raw
    batt_soc    = ha_sensor(get_sensor("batterie_soc"), required=True) if has_battery() else 100
    pv_leistung = pv_leistung_pre  # bereits oben gelesen

    # Loop-Signatur — Routine-Logs nur bei echten Änderungen
    global _last_loop_sig
    _loop_sig = (
        f"{round(remaining_pv_forecast,1)}|{round(pv_prognose_total,1)}|"
        f"{round(batt_soc)}|{round(pv_leistung,-2)}"
    )
    _loop_sig_changed = _loop_sig != _last_loop_sig

    dlog(f"── Loop Start ──────────────────────────────────────")
    if _loop_sig_changed:
        dlog(f"Sensoren: PV-Forecast-Rest={remaining_pv_forecast:.2f} kWh | PV-Heute-Total={pv_prognose_total:.2f} kWh | PV-Real={pv_heute_raw:.3f} kWh | Batt-SOC={batt_soc:.1f}% | PV-Leistung={pv_leistung:.0f} W")
    dlog_delta("remaining_pv_forecast", "Forecast-Rest", remaining_pv_forecast, " kWh", threshold=0.1)
    dlog_delta("pv_prognose_total",     "Forecast-Gesamt", pv_prognose_total,   " kWh", threshold=0.2)
    dlog_delta("batt_soc",              "Batterie-SOC",    batt_soc,            "%",    threshold=1.0)
    # Growatt "heute" setzt sich erst beim WR-Start zurück (nicht um Mitternacht).
    # Um 0 Uhr setzen wir pv_heute intern auf 0. Sobald der Sensor < 0.5 kWh fällt
    # (Inverter hat für heute zurückgesetzt), nehmen wir den Rohwert.
    if not _daily_budget.get("pv_reset_done", False):
        # Sensor < 0.5 kWh = WR hat heute zurückgesetzt; nach 12 Uhr ist Reset garantiert
        if pv_heute_raw < 0.5 or datetime.now().hour >= 12:
            _daily_budget["pv_reset_done"] = True
            _save_daily_budget(_daily_budget)
            pv_heute = pv_heute_raw
        else:
            pv_heute = 0.0
    else:
        pv_heute = pv_heute_raw
    haus_last   = ha_sensor(get_sensor("haus_last"))
    grid_power  = ha_sensor(get_sensor("grid_power"))

    # --- evcc lesen ---
    lp          = evcc_loadpoint()
    car_connected = lp.get("connected", False)
    car_charging  = lp.get("charging",  False)

    charged_today = evcc_charged_today(lp=lp)

    # --- Fahrzeug-SOC (optional, aus HA-Sensor) ---
    _auto_soc_entity = user_settings.get("sensor_auto_soc", "").strip()
    _auto_batt_kwh   = float(user_settings.get("auto_batterie_kwh", 0.0) or 0.0)
    _auto_ziel_soc   = int(user_settings.get("auto_ziel_soc", 80) or 80)
    auto_soc: float | None = None
    if _auto_soc_entity:
        _raw = ha_sensor(_auto_soc_entity)
        if _raw is not None:
            try: auto_soc = float(_raw)
            except (ValueError, TypeError): auto_soc = None
    # Auto voll wenn Ziel-SOC erreicht
    auto_voll = (auto_soc is not None) and (auto_soc >= _auto_ziel_soc)

    # --- Einstellungen (live aus user_settings) ---
    batt_kap  = get_batt_kap()
    ziel_soc  = get_batt_ziel_soc()
    haus_ema_brutto = get_ema_today()
    wd_heute = str(date.today().weekday())
    abend_entnahme = user_settings.get("abend_entnahme_wochentag", {}).get(wd_heute, 0.0)
    haus_ema  = max(haus_ema_brutto - abend_entnahme, 0)
    pv_faktor = get_pv_faktor()

    # --- Tageswechsel ---
    today = str(date.today())
    if _daily_budget["date"] != today:
        _daily_budget.update({
            "date": today, "pv_prognose_kwh": None, "einspeisung_kwh": 0.0,
            "last_loop_ts": None, "pv_reset_done": False,
            "battery_needs_initial": None, "initial_daily_budget": None,
            "soc_at_sunset": None, "last_valid_remaining_pv": None,
        })
        state["laden_pausiert"] = False
        state["laden_schnell"]  = False

    # --- Budget-Komponenten ---
    rem_hours      = remaining_daylight_hours()
    daylight_total, _ = _daylight_params()
    day_fraction_remaining = min(rem_hours / max(daylight_total, 1), 1.0)

    # ═══════════════════════════════════════════════════════════════════════════
    # MODUL 1 — STABILES TAGES-BUDGET
    # Einmalig beim WR-Start berechnen, danach nur bei Forecast-Drift >5% updaten
    # ═══════════════════════════════════════════════════════════════════════════
    _, sunset_h_local = _daylight_params()
    pv_schwelle   = 150  # Nur Nacht/Ausfall-Erkennung — Budget-Gate regelt den Rest
    pv_aktiv      = pv_leistung > pv_schwelle
    einspeisung_w = max(-grid_power, 0)
    now_ts        = datetime.now().isoformat(timespec="seconds")
    now_h         = datetime.now().hour + datetime.now().minute / 60

    pv_reset_done        = _daily_budget.get("pv_reset_done", False)
    initial_daily_budget = _daily_budget.get("initial_daily_budget")

    if pv_reset_done and initial_daily_budget is None:
        # Erst setzen wenn Forecast plausibel und Uhrzeit ≥ 07:30
        if pv_prognose_total > 2.0 and now_h >= 7.5:
            batt_needs_init  = max((ziel_soc - batt_soc) / 100 * batt_kap, 0) if has_battery() else 0
            haus_pv_anteil   = round(haus_ema * (daylight_total / 24), 3)
            _daily_budget["battery_needs_initial"] = round(batt_needs_init, 3)
            new_budget = round(max(pv_prognose_total * pv_faktor - haus_pv_anteil - batt_needs_init, 0), 2)
            _daily_budget["initial_daily_budget"] = new_budget
            _daily_budget["pv_prognose_kwh"]      = round(pv_prognose_total, 2)
            initial_daily_budget = new_budget
            log.info(f"Tages-Budget eingefroren: {new_budget:.2f} kWh "
                     f"(forecast={pv_prognose_total:.1f}×{pv_faktor:.3f} − haus_pv={haus_pv_anteil:.1f} [{daylight_total:.1f}h] − batt={batt_needs_init:.1f})")
            dlog(f"[M1] Tages-Budget: {pv_prognose_total:.1f}×{pv_faktor:.3f} − haus_pv={haus_pv_anteil:.1f} − batt={batt_needs_init:.1f} = {new_budget:.2f} kWh", "freeze")

    elif initial_daily_budget is not None and rem_hours > 0.5:
        # Forecast-Drift-Prüfung: >5% → Budget sofort neu berechnen
        # Effektiver Forecast = real bereits produziert + Solcast-Rest (aktueller Stand)
        effective_forecast = round(pv_heute + remaining_pv_forecast, 2)
        stored_forecast    = _daily_budget.get("pv_prognose_kwh") or 0
        if stored_forecast > 0 and effective_forecast > 2.0:
            drift = abs(effective_forecast - stored_forecast) / stored_forecast
            if drift > 0.05:
                batt_needs_init = _daily_budget.get("battery_needs_initial", 0) or 0
                haus_pv_anteil  = round(haus_ema * (daylight_total / 24), 3)
                new_budget = round(max(effective_forecast * pv_faktor - haus_pv_anteil - batt_needs_init, 0), 2)
                old_budget = initial_daily_budget
                _daily_budget["initial_daily_budget"] = new_budget
                _daily_budget["pv_prognose_kwh"]      = effective_forecast
                initial_daily_budget = new_budget
                log.info(f"Forecast-Drift {drift*100:.1f}%: Budget {old_budget:.2f} → {new_budget:.2f} kWh "
                         f"(forecast {stored_forecast:.1f} → {effective_forecast:.1f} kWh)")
                dlog(f"[M1] Forecast-Drift {drift*100:.1f}%: {stored_forecast:.1f} → {effective_forecast:.1f} kWh | Budget {old_budget:.2f} → {new_budget:.2f} kWh", "delta")

    # ═══════════════════════════════════════════════════════════════════════════
    # MODUL 2 — LADE-GATE
    # Stabil basierend auf Tages-Budget; Fallback-Floor nur vor WR-Start
    # ═══════════════════════════════════════════════════════════════════════════
    einspeisung_heute_m2  = round(_daily_budget.get("einspeisung_kwh", 0), 2)
    budget_puffer         = round(float(user_settings.get("budget_puffer_kwh", 0)), 2)
    budget_verfuegbar     = round(max((initial_daily_budget or 0) - charged_today - einspeisung_heute_m2, 0), 2)
    budget_verfuegbar_echt = round(max(budget_verfuegbar - budget_puffer, 0), 2)
    # Gate: Hat heute noch PV-Energie zu erwarten? (Forecast-Rest ODER noch etwas Echtzeit-PV)
    hat_pv_rest           = remaining_pv_forecast > 0.05 or pv_leistung > 150
    ueberschuss_fallback  = (initial_daily_budget is None) and einspeisung_w > 500 and hat_pv_rest
    budget_ok             = (budget_verfuegbar_echt > 0 or ueberschuss_fallback) and hat_pv_rest

    # M2-Signatur erweitern
    _loop_sig += f"|{round(budget_verfuegbar,1)}|{budget_ok}"
    _loop_sig_changed = _loop_sig != _last_loop_sig

    if _loop_sig_changed:
        dlog(f"[M2] Gate: budget_verfuegbar={budget_verfuegbar:.2f} | puffer={budget_puffer:.2f} | echt={budget_verfuegbar_echt:.2f} | budget_ok={budget_ok}", "decision")

    # ═══════════════════════════════════════════════════════════════════════════
    # MODUL 3 — COUNTDOWN "WENN JETZT ANSCHLIESSEN"
    # Genau: remaining_pv × faktor − haus_rest_live − batt_rest_live
    # haus_rest auf Sonnenstunden begrenzt (kein Post-Sunset-Verbrauch abziehen)
    # Gedeckelt auf Gate-Budget (kann nicht mehr zeigen als erlaubt)
    # ═══════════════════════════════════════════════════════════════════════════
    haus_heute_ohne_auto = max(haus_last - charged_today, 0)
    elapsed_daylight     = max(daylight_total - rem_hours, 0.5)
    haus_rate_ema        = haus_ema / max(daylight_total, 1)
    haus_rate_actual     = haus_heute_ohne_auto / elapsed_daylight
    haus_rate_eff        = max(haus_rate_ema, haus_rate_actual)
    haus_rest_live       = haus_rate_eff * max(rem_hours, 0)
    batt_rest_live = max((ziel_soc - batt_soc) / 100 * batt_kap, 0) if has_battery() else 0

    # Glitch-Schutz: remaining_pv=0 aber PV produziert → letzten validen Wert nehmen
    remaining_safe = remaining_pv_forecast
    if remaining_pv_forecast < 0.1 and pv_aktiv:
        remaining_safe = _daily_budget.get("last_valid_remaining_pv") or 0
        dlog(f"[M3] Glitch-Schutz: remaining=0 aber PV aktiv → cached {remaining_safe:.2f} kWh", "info")

    countdown_roh = max(remaining_safe * pv_faktor - haus_rest_live - batt_rest_live, 0)
    countdown_kwh = round(min(countdown_roh, budget_verfuegbar_echt), 2)

    # M3-Signatur finalisieren
    _loop_sig += f"|{round(countdown_kwh,1)}"
    _loop_sig_changed = _loop_sig != _last_loop_sig

    if _loop_sig_changed:
        dlog(f"[M3] Countdown: {remaining_safe:.2f}×{pv_faktor:.3f} − haus_rest={haus_rest_live:.2f} − batt={batt_rest_live:.2f} = {countdown_roh:.2f} → gedeckelt {countdown_kwh:.2f} kWh", "info")

    # ═══════════════════════════════════════════════════════════════════════════
    # MODUL 5 — BUDGET-SCHNELL
    # Manuell auslösen → evcc now-Modus, dynamisches maxcurrent (PV + Batterie)
    # Budget-Gate bleibt aktiv. Growatt Load First + DTSU666 hält Netz ≈ 0W.
    # ═══════════════════════════════════════════════════════════════════════════
    laden_schnell_prev = state.get("_laden_schnell_prev", False)
    laden_schnell = state.get("laden_schnell", False)
    if laden_schnell and (not car_connected or rem_hours <= 0.5):
        laden_schnell = False
        state["laden_schnell"] = False
        dlog("[M5] Schnell-Laden auto-deaktiviert (Auto weg oder Sonnenuntergang)", "info")

    if laden_schnell_prev and not laden_schnell:
        # Schnell deaktiviert → maxcurrent zurück auf 16A (evcc Default)
        evcc_set_maxcurrent(16)

    state["_laden_schnell_prev"] = laden_schnell

    # ═══════════════════════════════════════════════════════════════════════════
    # EINSPEISUNG AKKUMULIEREN (für Countdown + Selbstkontrolle)
    # ═══════════════════════════════════════════════════════════════════════════
    last_ts = _daily_budget.get("last_loop_ts")
    if last_ts:
        try:
            elapsed_h = (datetime.fromisoformat(now_ts) - datetime.fromisoformat(last_ts)).total_seconds() / 3600
            elapsed_h = min(elapsed_h, 0.25)
            _daily_budget["einspeisung_kwh"] = _daily_budget.get("einspeisung_kwh", 0) + einspeisung_w / 1000 * elapsed_h
        except Exception:
            pass
    _daily_budget["last_loop_ts"] = now_ts

    # Budget-Änderungsgrund für UI
    budget_change_grund = state.get("budget_change_grund", "")
    ref_budget = state.get("_grund_ref_budget")
    if ref_budget is None:
        state["_grund_ref_budget"] = initial_daily_budget
    elif initial_daily_budget is not None and ref_budget is not None:
        delta = initial_daily_budget - ref_budget
        if abs(delta) >= 0.3:
            richtung = "gestiegen" if delta > 0 else "gesunken"
            budget_change_grund = f"Budget {richtung}: Forecast-Korrektur {'+' if delta > 0 else ''}{delta:.1f} kWh"
            state["_grund_ref_budget"] = initial_daily_budget

    _save_daily_budget(_daily_budget)

    # Aliases für Abwärtskompatibilität (API / DB)
    available_for_car = budget_verfuegbar_echt
    daily_budget      = initial_daily_budget or 0

    log.info(
        f"Remaining={remaining_pv_forecast:.1f} kWh | Haus-EMA={haus_ema:.1f} kWh | "
        f"Speicher={batt_rest_live:.1f} kWh | Budget={daily_budget:.1f} kWh | "
        f"Geladen={charged_today:.1f} kWh | Verfügbar={available_for_car:.1f} kWh"
    )

    # --- Mindeststrom (Schnell: Max aus evcc, sonst konfigurierter Wert) ---
    # Hinweis: target_a wird hier früh gesetzt damit Modul-5-Modbus-Block es nutzen kann
    if laden_schnell:
        target_a = int(lp.get("effectiveMaxCurrent") or lp.get("maxCurrent") or 16)
    else:
        target_a = int(user_settings.get("min_strom_a", 6))

    # ═══════════════════════════════════════════════════════════════════════════
    # ENTSCHEIDUNG
    # ═══════════════════════════════════════════════════════════════════════════
    batt_ok       = (batt_soc >= get_batt_min_soc()) if has_battery() else True
    current_mode  = lp.get("mode", "off")
    current_min_a = lp.get("minCurrent", 6)

    if not user_settings.get("addon_aktiv", True):
        # Schlaf-Modus: Add-on greift nicht in evcc ein — evcc läuft frei
        action = "schlaf"
        grund  = "Add-on inaktiv — evcc läuft frei"

    elif state.get("laden_pausiert"):
        action = "pausiert"
        grund  = "Manuell pausiert"
        if current_mode != "off":
            evcc_set_mode("off")

    elif not car_connected:
        action = "idle"
        grund  = ""
        if current_mode != "off":
            evcc_set_mode("off")

    elif auto_voll:
        action = "auto_voll"
        grund  = f"Fahrzeug-SOC {auto_soc:.0f}% ≥ Ziel {_auto_ziel_soc}%"
        if current_mode != "off":
            evcc_set_mode("off")

    elif not batt_ok:
        action = "batterie_schutz"
        grund  = f"Speicher-SOC {batt_soc:.0f}% < Notfall-Minimum {get_batt_min_soc()}%"
        if current_mode != "off":
            evcc_set_mode("off")

    elif not budget_ok:
        action = "kein_budget"
        if not hat_pv_rest:
            grund = f"Kein PV-Rest heute ({remaining_pv_forecast:.2f} kWh Forecast, {pv_leistung:.0f} W)"
        else:
            grund = f"Budget aufgebraucht — {charged_today:.1f} kWh geladen von {initial_daily_budget or 0:.1f} kWh"
        if current_mode != "off":
            evcc_set_mode("off")

    else:
        if laden_schnell:
            action      = "laden"
            # Modul 5: Schnell-Laden → now-Modus, maxcurrent regelt Schnell-Regler-Thread
            target_mode = "now"
            cur_max_a   = int(lp.get("maxCurrent") or 16)
            grund = (f"⚡ Schnell | PV {pv_leistung/1000:.1f}kW"
                     f" | max {cur_max_a}A | {countdown_kwh:.1f} kWh Budget")
            if current_mode != "now":
                evcc_set_mode("now")
                start_schnell_regler()   # Sicherheit: Thread starten falls noch nicht läuft
        else:
            target_mode = "minpv"
            if ueberschuss_fallback:
                grund = f"PV-Überschuss {einspeisung_w/1000:.1f} kW ins Netz → Auto laden | {target_a}A"
            else:
                grund = f"Budget {budget_verfuegbar:.1f} kWh | Geladen {charged_today:.1f} kWh | {target_a}A"
            if current_min_a != target_a:
                evcc_set_mincurrent(target_a)
            if current_mode != target_mode:
                evcc_set_mode(target_mode)
            # Lädt gerade wirklich? Sonst "bereit" anzeigen (Auto voll oder warte auf PV)
            action = "laden" if car_charging else "bereit"

    _batt_charge_raw = ha_sensor(user_settings.get("growatt_battery_charge_power", "sensor.growatt_battery_charge_power")) or 0
    # Sensor liefert Watt → in kW umrechnen
    batt_charge_kw = _batt_charge_raw / 1000 if _batt_charge_raw > 20 else _batt_charge_raw
    ansteck_deadline, ansteck_grund, ansteck_urgency, ansteck_minutes_left = calc_ansteck_deadline(
        initial_daily_budget or 0, remaining_pv_forecast, pv_leistung, rem_hours, _daily_budget,
        haus_ema=haus_ema, daylight_total=daylight_total,
        batt_soc=batt_soc, ziel_soc=ziel_soc, batt_kap=batt_kap,
        batt_charge_kw=batt_charge_kw
    )

    charge_power_kw = (lp.get("chargePower") or 0) / 1000
    if charge_power_kw < 0.1:
        charge_power_kw = target_a * 230 / 1000
    remaining_min = int(budget_verfuegbar_echt / charge_power_kw * 60) if charge_power_kw > 0 and budget_verfuegbar_echt > 0 else 0
    remaining_h   = remaining_min // 60
    remaining_m   = remaining_min % 60

    einspeisung_heute = round(_daily_budget.get("einspeisung_kwh", 0), 2)
    noch_offen = round(max((initial_daily_budget or 0) - charged_today - einspeisung_heute, 0), 2)

    # Sonnenuntergang berechnen — dieser Zeitpunkt = PV Ende = Budget-Ende
    _, sunset_h   = _daylight_params()
    today_sunset  = datetime.now().replace(hour=int(sunset_h), minute=int((sunset_h % 1) * 60), second=0, microsecond=0)
    pv_ende_str   = today_sunset.strftime("%H:%M") + " Uhr"

    # "Laden möglich bis" — wann ist Budget bei aktueller Ladeleistung aufgebraucht?
    laden_bis = None
    if budget_verfuegbar_echt > 0.1 and charge_power_kw > 0.1:
        laden_bis_dt = datetime.now() + timedelta(hours=budget_verfuegbar_echt / charge_power_kw)
        if laden_bis_dt <= today_sunset:
            laden_bis = laden_bis_dt.strftime("%H:%M") + " Uhr"
        else:
            laden_bis = "nach Sonnenuntergang"

    state.update({
        # Zeitstempel
        "last_update":             datetime.now().strftime("%d.%m.%Y %H:%M:%S"),
        # PV
        "pv_prognose_kwh":         round(pv_prognose_morgen if rem_hours <= 0.5 else pv_prognose_total, 2),
        "pv_prognose_heute_kwh":   round(pv_prognose_total, 2),
        "pv_prognose_morgen_kwh":  round(pv_prognose_morgen or 0, 2),
        "pv_heute_kwh":            round(pv_heute, 3),
        "pv_forecast_rest_kwh":    round(remaining_pv_forecast, 2),
        "forecast_updated_str":    forecast_updated_str,
        "pv_forecast_effective_kwh": round(pv_heute + remaining_pv_forecast, 2),
        "pv_leistung_w":           round(pv_leistung, 0),
        "pv_aktiv":                pv_aktiv,
        # Batterie
        "batterie_soc":            int(batt_soc),
        "batterie_ziel_soc":       ziel_soc,
        "batterie_min_soc":        get_batt_min_soc(),
        "batterie_kapazitaet_kwh": get_batt_kap(),
        "battery_needs_kwh":       round(batt_rest_live, 2),
        # Haus
        "haus_last_kwh":           round(haus_last, 2),
        "haus_real_kwh":           round(haus_heute_ohne_auto, 2),
        "haus_rest_kwh":           round(haus_rest_live, 2),
        "haus_ema_kwh":            round(haus_ema, 2),
        "haus_ema_brutto_kwh":     round(haus_ema_brutto, 2),
        "abend_entnahme_kwh":      round(abend_entnahme, 2),
        "haus_ema_wochentag":        user_settings.get("haus_ema_wochentag", {}),
        "haus_ema_wochentag_name":   WOCHENTAGE[date.today().weekday()],
        "batt_fill_rate_wochentag":  user_settings.get("batt_fill_rate_wochentag", {}),
        "batt_fill_rate_heute_kw":   user_settings.get("batt_fill_rate_wochentag", {}).get(str(date.today().weekday())),
        # Budget (Modul 1+2)
        "initial_daily_budget_kwh": round(initial_daily_budget, 2) if initial_daily_budget is not None else None,
        "budget_verfuegbar_kwh":    budget_verfuegbar,
        "budget_puffer_kwh":        budget_puffer,
        "budget_verfuegbar_echt_kwh": budget_verfuegbar_echt,
        "charged_today_kwh":        round(charged_today, 2),
        "einspeisung_heute_kwh":    einspeisung_heute,
        "einspeisung_w":            round(einspeisung_w, 0),
        "noch_offen_kwh":           noch_offen,
        "laden_bis":                laden_bis,
        "pv_ende_str":              pv_ende_str,
        "hat_pv_rest":              hat_pv_rest,
        "budget_ampel":             "gruen" if budget_verfuegbar >= user_settings.get("ampel_gruen_kwh", 0.5) else "gelb" if budget_verfuegbar > 0 else "rot",
        "budget_change_grund":      budget_change_grund,
        # Countdown (Modul 3)
        "countdown_kwh":            countdown_kwh,
        # Connect-Deadline (Modul 4)
        "ansteck_deadline":         ansteck_deadline,
        "ansteck_grund":            ansteck_grund,
        "ansteck_urgency":          ansteck_urgency,
        "ansteck_minutes_left":     ansteck_minutes_left,
        # Schnell-Laden (Modul 5)
        "laden_schnell":            laden_schnell,
        "laden_schnell_moeglich":   hat_pv_rest and (budget_verfuegbar_echt > 0 or ueberschuss_fallback),
        # Steuerung
        "action":                   action,
        "grund":                    grund,
        "car_connected":            car_connected,
        "auto_soc":                 auto_soc,
        "auto_ziel_soc":            _auto_ziel_soc,
        "auto_batt_kwh":            _auto_batt_kwh,
        "auto_voll":                auto_voll,
        "evcc_online":              state.get("evcc_online", True),
        "evcc_mode":                lp.get("mode", "?"),
        "ziel_strom_a":             target_a,
        "charge_power_kw":          round(charge_power_kw, 2),
        "remaining_time_min":       remaining_min,
        "remaining_time_str":       f"{remaining_h}h {remaining_m:02d}min" if remaining_min > 0 else "–",
        "budget_at_laden_start":    round(initial_daily_budget or 0, 2),
        "laden_pausiert":           state.get("laden_pausiert", False),
        "addon_aktiv":              user_settings.get("addon_aktiv", True),
        "is_after_sunset":          rem_hours <= 0.5 and not pv_aktiv,
        # Einstellungen
        "min_strom_a":              user_settings.get("min_strom_a", 6),
        "pv_faktor":                round(pv_faktor, 3),
        "debug_mode":               is_debug_mode(),
        # Abwärtskompatibilität für DB/API
        "available_for_car_kwh":    budget_verfuegbar_echt,
        "budget_kwh":               budget_verfuegbar_echt,
        "daily_budget_kwh":         round(initial_daily_budget or 0, 2),
    })

    # SOC bei Sonnenuntergang einmalig speichern (Abend-Lernfunktion)
    if rem_hours <= 0.5 and not pv_aktiv and _daily_budget.get("soc_at_sunset") is None:
        _daily_budget["soc_at_sunset"] = batt_soc
        _save_daily_budget(_daily_budget)
        log.info(f"SOC bei Sonnenuntergang: {batt_soc:.1f}%")
        dlog(f"Sonnenuntergang: SOC={batt_soc:.1f}% gespeichert", "freeze")

    log.info(
        f"Budget={initial_daily_budget or 0:.1f} kWh | Verfügbar={budget_verfuegbar:.1f} kWh | "
        f"Geladen={charged_today:.1f} kWh | Countdown={countdown_kwh:.1f} kWh | "
        f"Auto={'✓' if car_connected else '✗'} | {action}"
    )

    if action != state.get("_last_logged_action", ""):
        dlog(f"ACTION WECHSEL: {state.get('_last_logged_action','–')} → {action} | Grund: {grund}", "action")
        db_log_control()
        state["_last_logged_action"] = action
    if _loop_sig_changed:
        dlog(f"── Loop Ende ── Action: {action} | Countdown: {countdown_kwh:.2f} kWh | Deadline: {ansteck_deadline or '–'} ({ansteck_urgency or 'n/a'})")
        _last_loop_sig = _loop_sig
    db_update_today(charged_today, einspeisung_heute)
    check_and_send_notifications(action, budget_verfuegbar_echt, ansteck_urgency, car_connected, charged_today)

# ---------------------------------------------------------------------------
# Haupt-Thread
# ---------------------------------------------------------------------------

LEARNING_DATE_PATH = DATA_DIR / "last_learning_date.txt"


def _load_last_learning_date():
    try:
        if LEARNING_DATE_PATH.exists():
            return date.fromisoformat(LEARNING_DATE_PATH.read_text().strip())
    except Exception:
        pass
    return None


def _save_last_learning_date(d):
    try:
        LEARNING_DATE_PATH.write_text(str(d))
    except Exception:
        pass


def scheduler():
    """Hintergrund-Thread: führt control_loop() im konfigurierten Intervall aus
    und startet täglich den Lernlauf ab LEARNING_HOUR Uhr."""
    last_learning_date = _load_last_learning_date()
    while True:
        try:
            control_loop()
        except Exception as e:
            log.error(f"Control loop Fehler: {e}", exc_info=True)

        now = datetime.now()
        if now.hour >= LEARNING_HOUR and now.date() != last_learning_date:
            try:
                daily_learning()
                last_learning_date = now.date()
                _save_last_learning_date(last_learning_date)
            except Exception as e:
                log.error(f"Learning Fehler: {e}", exc_info=True)

        # Bei "laden" oder "pausiert" (Auto angesteckt): 1 Minute — evcc kann sonst selbst laden
        action = state.get("action")
        interval = 60 if action in ("laden", "pausiert") else get_update_interval() * 60
        time.sleep(interval)

# ---------------------------------------------------------------------------
# Web-UI
# ---------------------------------------------------------------------------

TEMPLATE = r"""<!DOCTYPE html>
<html lang="de">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Smart EV Charger</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;600;700&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet">
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
  :root {
    --bg: #080c14;
    --surface: #0d1421;
    --surface-2: #131d2e;
    --card-bg: #0d1421;
    --border: #1e2d47;
    --border-bright: #2a4066;
    --text: #e8f4fd;
    --muted: #5a7a9a;
    --accent: #00d4ff;
    --accent-dim: rgba(0,212,255,0.12);
    --green: #00ff88;
    --yellow: #ffb800;
    --red: #ff3d5a;
    --orange: #ff6b2b;
    --green-dim: rgba(0,255,136,0.12);
    --red-dim: rgba(255,61,90,0.12);
    --yellow-dim: rgba(255,184,0,0.12);
  }
  :root.light {
    --bg: #f0f4f8;
    --surface: #ffffff;
    --surface-2: #e8eef5;
    --card-bg: #ffffff;
    --border: #d0dae6;
    --border-bright: #a0b4c8;
    --text: #0f1f30;
    --muted: #6080a0;
    --accent: #0099bb;
    --accent-dim: rgba(0,153,187,0.12);
    --green: #007a40;
    --yellow: #b07800;
    --red: #cc1f36;
    --orange: #b84a10;
    --green-dim: rgba(0,122,64,0.1);
    --red-dim: rgba(204,31,54,0.1);
    --yellow-dim: rgba(176,120,0,0.1);
  }
  html { transition: background 0.2s, color 0.2s; }
  /* ── Reset & Base ── */
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }

  body {
    background: var(--bg);
    color: var(--text);
    font-family: 'Space Grotesk', system-ui, sans-serif;
    min-height: 100vh;
    position: relative;
    overflow-x: hidden;
  }

  /* ── Background mesh ── */
  body::before {
    content: '';
    position: fixed; inset: 0;
    background:
      radial-gradient(ellipse 80% 60% at -10% -5%, rgba(0,100,200,0.18) 0%, transparent 60%),
      radial-gradient(ellipse 50% 40% at 110% 110%, rgba(0,212,255,0.08) 0%, transparent 55%);
    pointer-events: none; z-index: 0;
  }
  body::after {
    content: '';
    position: fixed; inset: 0;
    background-image: radial-gradient(circle, rgba(0,212,255,0.07) 1px, transparent 1px);
    background-size: 24px 24px;
    pointer-events: none; z-index: 0;
  }

  /* ── Layout ── */
  #app {
    position: relative; z-index: 1;
    max-width: 1400px;
    margin: 0 auto;
    padding: 1.25rem 1rem 3rem;
  }

  /* ── Typography ── */
  .mono { font-family: 'JetBrains Mono', monospace; }
  .label-sm { font-size: 0.72rem; font-weight: 500; letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); }
  .val-lg { font-family: 'JetBrains Mono', monospace; font-size: 2rem; font-weight: 600; line-height: 1; }
  .val-xl { font-family: 'JetBrains Mono', monospace; font-size: 2.6rem; font-weight: 700; line-height: 1; }

  /* ── Cards ── */
  .card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 16px;
    padding: 1.25rem;
    backdrop-filter: blur(12px);
    transition: transform 0.2s ease, border-color 0.2s ease, box-shadow 0.2s ease;
    animation: fadeSlideIn 0.4s ease both;
  }
  .card:hover {
    transform: translateY(-2px);
    border-color: var(--border-bright);
    box-shadow: 0 8px 32px rgba(0,0,0,0.4), 0 0 0 1px rgba(0,212,255,0.06);
  }
  .card-title {
    font-size: 0.72rem;
    font-weight: 600;
    letter-spacing: 0.1em;
    text-transform: uppercase;
    color: var(--muted);
    margin-bottom: 1rem;
  }

  /* ── Grids ── */
  .grid-3 {
    display: grid;
    grid-template-columns: repeat(3, 1fr);
    gap: 1rem;
    margin-bottom: 1rem;
  }
  .grid-2 {
    display: grid;
    grid-template-columns: repeat(2, 1fr);
    gap: 1rem;
    margin-bottom: 1rem;
  }
  @media (max-width: 1100px) { .grid-3 { grid-template-columns: 1fr 1fr; } }
  @media (max-width: 700px)  { .grid-3, .grid-2 { grid-template-columns: 1fr; } }

  /* ── Hero / Top Bar ── */
  .hero-card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 20px;
    padding: 1.5rem;
    margin-bottom: 1rem;
    backdrop-filter: blur(12px);
    animation: fadeSlideIn 0.35s ease both;
    transition: border-color 0.3s, box-shadow 0.3s;
  }
  .hero-card.is-charging {
    border-color: rgba(0,212,255,0.4);
    box-shadow: 0 0 40px rgba(0,212,255,0.12), inset 0 0 60px rgba(0,212,255,0.03);
  }
  .hero-top {
    display: flex;
    align-items: center;
    justify-content: space-between;
    margin-bottom: 1.25rem;
  }
  .hero-brand {
    display: flex;
    align-items: center;
    gap: 0.75rem;
  }
  .hero-brand-icon {
    width: 36px; height: 36px;
    background: var(--accent-dim);
    border: 1px solid rgba(0,212,255,0.3);
    border-radius: 10px;
    display: flex; align-items: center; justify-content: center;
    font-size: 1.1rem;
  }
  .hero-brand-name {
    font-size: 0.72rem;
    font-weight: 700;
    letter-spacing: 0.15em;
    text-transform: uppercase;
    color: var(--muted);
  }
  .nav-menu-wrap { position: relative; }
  .nav-menu-btn {
    background: var(--surface-2);
    border: 1px solid var(--border);
    color: var(--text);
    border-radius: 10px;
    padding: 0.4rem 0.8rem;
    cursor: pointer;
    font-size: 1.1rem;
    transition: all 0.15s;
  }
  .nav-menu-btn:hover { border-color: var(--border-bright); }
  .nav-menu-dropdown {
    display: none;
    position: absolute;
    top: calc(100% + 0.5rem);
    right: 0;
    background: var(--surface-2);
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 0.4rem;
    flex-direction: column;
    gap: 0.25rem;
    min-width: 160px;
    z-index: 100;
    box-shadow: 0 8px 32px rgba(0,0,0,0.4);
  }
  .nav-menu-dropdown.open { display: flex; }
  .tab-btn { display: block; text-align: left; width: 100%; }
  .tab-btn {
    background: none;
    border: none;
    color: var(--muted);
    border-radius: 7px;
    padding: 0.4rem 1rem;
    cursor: pointer;
    font-size: 0.82rem;
    font-weight: 600;
    font-family: 'Space Grotesk', sans-serif;
    letter-spacing: 0.03em;
    transition: all 0.15s;
    position: relative;
    overflow: hidden;
  }
  .tab-btn::after {
    content: '';
    position: absolute; inset: 0;
    background: radial-gradient(circle at 50% 50%, rgba(255,255,255,0.15), transparent 70%);
    transform: scale(0);
    transition: transform 0.3s;
  }
  .tab-btn:hover { color: var(--text); }
  .tab-btn.active {
    background: var(--accent-dim);
    border: 1px solid rgba(0,212,255,0.3);
    color: var(--accent);
  }

  /* ── Hero Status Body ── */
  .hero-body {
    display: flex;
    align-items: center;
    gap: 1.5rem;
    flex-wrap: wrap;
  }
  .hero-status-icon {
    flex-shrink: 0;
    width: 64px; height: 64px;
    border-radius: 18px;
    display: flex; align-items: center; justify-content: center;
    font-size: 1.8rem;
    transition: all 0.3s;
  }
  .hero-status-icon.laden {
    background: var(--accent-dim);
    border: 1px solid rgba(0,212,255,0.4);
    box-shadow: 0 0 24px rgba(0,212,255,0.2);
    animation: iconPulse 2s ease-in-out infinite;
  }
  .hero-status-icon.idle      { background: rgba(90,122,154,0.15); border: 1px solid var(--border); }
  .hero-status-icon.schlaf    { background: var(--yellow-dim); border: 1px solid rgba(255,184,0,0.3); }
  .hero-status-icon.pausiert  { background: var(--yellow-dim); border: 1px solid rgba(255,184,0,0.3); }
  .hero-status-icon.kein_budget { background: var(--yellow-dim); border: 1px solid rgba(255,184,0,0.3); }
  .hero-status-icon.batterie_schutz { background: var(--red-dim); border: 1px solid rgba(255,61,90,0.3); }

  .hero-status-info { flex: 1; min-width: 200px; }
  .hero-action-label {
    font-size: 1.6rem;
    font-weight: 700;
    letter-spacing: -0.01em;
    line-height: 1.1;
    margin-bottom: 0.2rem;
  }
  .hero-action-label.laden { color: var(--accent); }
  .hero-action-label.idle  { color: var(--muted); }
  .hero-action-label.pausiert { color: var(--yellow); }
  .hero-action-label.kein_budget { color: var(--yellow); }
  .hero-action-label.batterie_schutz { color: var(--red); }

  .hero-sub { font-size: 0.82rem; color: var(--muted); }

  /* ── Hero Power Bar ── */
  .hero-power-row {
    display: flex;
    align-items: center;
    gap: 1rem;
    flex-wrap: wrap;
    margin-top: 0.6rem;
  }
  .hero-kw {
    font-family: 'JetBrains Mono', monospace;
    font-size: 2.2rem;
    font-weight: 700;
    color: var(--accent);
    line-height: 1;
    transition: color 0.3s;
  }
  .hero-kw.off { color: var(--muted); }
  .hero-kw-unit { font-size: 0.9rem; color: var(--muted); margin-left: 0.25rem; }

  .hero-charge-bar-wrap {
    flex: 1;
    min-width: 180px;
  }
  .hero-charge-bar-track {
    height: 6px;
    background: var(--border);
    border-radius: 3px;
    overflow: hidden;
    margin-bottom: 0.35rem;
  }
  .hero-charge-bar-fill {
    height: 100%;
    border-radius: 3px;
    background: linear-gradient(90deg, var(--accent), var(--green));
    transition: width 0.8s cubic-bezier(.4,0,.2,1);
    box-shadow: 0 0 8px rgba(0,212,255,0.5);
  }
  .hero-charge-bar-fill.off {
    background: var(--border-bright);
    box-shadow: none;
  }

  .hero-stats-row {
    display: flex;
    gap: 1.5rem;
    flex-wrap: wrap;
    margin-top: 0.75rem;
    padding-top: 0.75rem;
    border-top: 1px solid var(--border);
  }
  .hero-stat {
    display: flex;
    flex-direction: column;
    gap: 0.2rem;
  }
  .hero-stat-label { font-size: 0.68rem; font-weight: 600; letter-spacing: 0.09em; text-transform: uppercase; color: var(--muted); }
  .hero-stat-val { font-family: 'JetBrains Mono', monospace; font-size: 1.1rem; font-weight: 600; color: var(--text); }

  /* Energie-Fluss Animation */
  .energy-flow {
    display: none;
    flex-direction: column;
    align-items: center;
    gap: 0;
    width: 20px;
    height: 64px;
    flex-shrink: 0;
    position: relative;
    overflow: hidden;
  }
  .energy-flow.active { display: flex; }
  .energy-flow-line {
    position: absolute;
    inset: 0;
    background: linear-gradient(to bottom, transparent, var(--accent), transparent);
    animation: energyFlow 1.5s linear infinite;
    opacity: 0.6;
  }
  @keyframes energyFlow {
    0%   { transform: translateY(100%); }
    100% { transform: translateY(-100%); }
  }
  @keyframes iconPulse {
    0%, 100% { box-shadow: 0 0 20px rgba(0,212,255,0.2); }
    50%       { box-shadow: 0 0 36px rgba(0,212,255,0.45); }
  }
  @keyframes connectBlink {
    0%, 100% { opacity: 1; }
    50%       { opacity: 0.3; }
  }
  .connect-blink { animation: connectBlink var(--blink-speed, 2s) ease-in-out infinite; }
  @keyframes fadeSlideIn {
    from { opacity: 0; transform: translateY(12px); }
    to   { opacity: 1; transform: translateY(0); }
  }

  /* ── Stat Rows ── */
  .stat { display: flex; justify-content: space-between; align-items: center; padding: 0.5rem 0; border-bottom: 1px solid rgba(30,45,71,0.7); }
  .stat:last-child { border-bottom: none; }
  .stat-label { color: var(--muted); font-size: 0.82rem; }
  .stat-value { font-family: 'JetBrains Mono', monospace; font-weight: 600; font-size: 0.95rem; }

  /* ── Budget Card ── */
  .budget-main-val {
    font-family: 'JetBrains Mono', monospace;
    font-size: 3rem;
    font-weight: 700;
    line-height: 1;
    transition: color 0.3s;
  }
  .budget-main-val.no-budget {
    font-family: 'Space Grotesk', sans-serif;
    font-size: 1.1rem;
    font-weight: 500;
    color: var(--muted);
  }
  .budget-main-val.positive { color: var(--green); text-shadow: 0 0 20px rgba(0,255,136,0.3); }
  .budget-main-val.negative { color: var(--red); text-shadow: 0 0 20px rgba(255,61,90,0.3); }
  .budget-main-val.zero     { color: var(--muted); }

  .budget-breakdown {
    display: flex;
    flex-direction: column;
    gap: 0.1rem;
    margin: 0.75rem 0;
    padding: 0.75rem;
    background: var(--surface-2);
    border-radius: 10px;
    border: 1px solid var(--border);
  }
  .budget-row {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 0.3rem 0;
  }
  .budget-row + .budget-row { border-top: 1px solid rgba(30,45,71,0.5); }
  .budget-row-label { font-size: 0.8rem; color: var(--muted); }
  .budget-row-val { font-family: 'JetBrains Mono', monospace; font-size: 0.88rem; font-weight: 600; }
  .budget-row.total .budget-row-label { color: var(--text); font-weight: 600; font-size: 0.85rem; }
  .budget-row.total .budget-row-val { font-size: 1rem; }

  .budget-bar-wrap { margin: 0.75rem 0 0.25rem; }
  .budget-bar {
    height: 10px;
    background: var(--surface-2);
    border-radius: 5px;
    overflow: hidden;
    border: 1px solid var(--border);
  }
  .budget-bar-fill {
    height: 100%;
    border-radius: 5px;
    transition: width 0.8s cubic-bezier(.4,0,.2,1), background 0.4s;
    background: linear-gradient(90deg, var(--accent), var(--green));
  }

  /* ── Sensor / Info Cards ── */
  .sensor-grid-inner {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 0.5rem;
  }
  .sensor-tile {
    background: var(--surface-2);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 0.65rem 0.75rem;
  }
  .sensor-tile-label { font-size: 0.68rem; letter-spacing: 0.07em; text-transform: uppercase; color: var(--muted); margin-bottom: 0.25rem; }
  .sensor-tile-val { font-family: 'JetBrains Mono', monospace; font-size: 1.1rem; font-weight: 600; }

  /* ── EMA Table ── */
  table { width: 100%; border-collapse: collapse; font-size: 0.82rem; }
  th { color: var(--muted); font-weight: 600; font-size: 0.72rem; letter-spacing: 0.07em; text-transform: uppercase; text-align: left; padding: 0.4rem 0.5rem; border-bottom: 1px solid var(--border); }
  td { padding: 0.4rem 0.5rem; border-bottom: 1px solid rgba(30,45,71,0.5); font-family: 'JetBrains Mono', monospace; font-size: 0.82rem; }
  tr:last-child td { border-bottom: none; }

  /* ── Log Table ── */
  .action-laden          { color: var(--accent); }
  .action-idle           { color: var(--muted); }
  .action-kein_budget    { color: var(--yellow); }
  .action-batterie_schutz{ color: var(--red); }
  .action-pausiert       { color: var(--orange); }
  .ts { color: var(--muted); font-family: 'JetBrains Mono', monospace; font-size: 0.78rem; }

  /* ── Badge ── */
  .badge { display: inline-flex; align-items: center; gap: 0.3rem; padding: 0.2rem 0.65rem; border-radius: 20px; font-size: 0.75rem; font-weight: 700; letter-spacing: 0.04em; }
  .badge-green  { background: var(--green-dim);  color: var(--green);  border: 1px solid rgba(0,255,136,0.2); }
  .badge-yellow { background: var(--yellow-dim); color: var(--yellow); border: 1px solid rgba(255,184,0,0.2); }
  .badge-red    { background: var(--red-dim);    color: var(--red);    border: 1px solid rgba(255,61,90,0.2); }
  .badge-accent { background: var(--accent-dim); color: var(--accent); border: 1px solid rgba(0,212,255,0.2); }
  .badge-muted  { background: rgba(90,122,154,0.1); color: var(--muted); border: 1px solid rgba(90,122,154,0.2); }

  /* ── Pause Button ── */
  .pause-btn {
    display: flex; align-items: center; justify-content: center; gap: 0.5rem;
    padding: 0.6rem 1.25rem;
    border-radius: 10px;
    border: 1px solid var(--border-bright);
    background: var(--surface-2);
    color: var(--text);
    font-family: 'Space Grotesk', sans-serif;
    font-size: 0.85rem;
    font-weight: 600;
    cursor: pointer;
    transition: all 0.15s;
    position: relative;
    overflow: hidden;
    flex-shrink: 0;
  }
  .pause-btn::after {
    content: '';
    position: absolute; inset: 0;
    background: radial-gradient(circle at var(--rx,50%) var(--ry,50%), rgba(255,255,255,0.12), transparent 60%);
    transform: scale(0);
    transition: transform 0.4s;
  }
  .pause-btn:active::after { transform: scale(2.5); }
  .pause-btn:hover { border-color: var(--border-bright); background: var(--border); }
  .pause-btn.active { background: var(--red-dim); border-color: rgba(255,61,90,0.4); color: var(--red); }
  .hero-controls {
    display: flex;
    gap: 0.5rem;
    margin-top: 1.5rem;
    margin-bottom: 1.25rem;
    padding-top: 1.25rem;
    border-top: 1px solid var(--border);
    align-items: stretch;
  }
  /* ── Control Buttons ── */
  .ctrl-btn {
    flex: 1;
    background: var(--surface-2);
    border: 1px solid var(--border);
    color: var(--muted);
    border-radius: 10px;
    padding: 0.5rem 0.4rem;
    cursor: pointer;
    font-size: 0.8rem;
    font-weight: 700;
    font-family: 'Space Grotesk', sans-serif;
    transition: background 0.15s, border-color 0.15s, color 0.15s;
    white-space: nowrap;
  }
  .ctrl-btn:active { opacity: 0.75; }
  /* Grün = aktiv/gut */
  .ctrl-btn.state-green {
    background: var(--green-dim);
    border-color: rgba(0,255,136,0.35);
    color: var(--green);
  }
  /* Gelb = inaktiv/schläft/pausiert */
  .ctrl-btn.state-yellow {
    background: var(--yellow-dim);
    border-color: rgba(255,184,0,0.35);
    color: var(--yellow);
  }
  /* Schnell */
  .schnell-btn.active   { background: var(--accent-dim); border-color: rgba(0,212,255,0.4); color: var(--accent); }
  .schnell-btn.disabled { opacity: 0.4; cursor: not-allowed; pointer-events: none; }
  .schnell-btn.available { border-color: rgba(0,212,255,0.4); color: var(--accent); }

  /* ── Toggle Switch ── */
  .toggle-switch { position:relative; display:inline-block; width:44px; height:24px; cursor:pointer; }
  .toggle-switch input { opacity:0; width:0; height:0; }
  .toggle-slider {
    position:absolute; inset:0; background:var(--surface); border:1px solid var(--border);
    border-radius:24px; transition:0.2s;
  }
  .toggle-slider::before {
    content:""; position:absolute; width:18px; height:18px; left:2px; top:2px;
    background:var(--muted); border-radius:50%; transition:0.2s;
  }
  .toggle-switch input:checked + .toggle-slider { background:var(--green-dim); border-color:rgba(0,255,136,0.4); }
  .toggle-switch input:checked + .toggle-slider::before { transform:translateX(20px); background:var(--green); }

  /* ── Grund Box ── */
  .grund-box {
    background: var(--surface-2);
    border-left: 3px solid var(--border-bright);
    border-radius: 0 8px 8px 0;
    padding: 0.6rem 0.75rem;
    font-size: 0.8rem;
    color: var(--muted);
    line-height: 1.5;
    margin-top: 0.5rem;
  }
  .grund-box.laden  { border-left-color: var(--accent); }
  .grund-box.yellow { border-left-color: var(--yellow); }
  .grund-box.red    { border-left-color: var(--red); }

  /* ── Connect/Restzeit Box ── */
  .info-box {
    border-radius: 12px;
    padding: 1rem;
    margin-bottom: 1rem;
    text-align: center;
    border: 1px solid var(--border);
    background: var(--surface-2);
  }
  .info-box.green  { border-color: rgba(0,255,136,0.3);  background: var(--green-dim); }
  .info-box.blue   { border-color: rgba(0,212,255,0.3);  background: var(--accent-dim); }
  .info-box.yellow { border-color: rgba(255,204,0,0.35); background: rgba(255,204,0,0.07); }
  .info-box.red    { border-color: rgba(255,80,80,0.35); background: rgba(255,80,80,0.07); }
  .info-box-label  { font-size: 0.68rem; letter-spacing: 0.1em; text-transform: uppercase; color: var(--muted); margin-bottom: 0.4rem; }
  .info-box-val    { font-family: 'JetBrains Mono', monospace; font-size: 2.2rem; font-weight: 700; line-height: 1; }
  .info-box-sub    { font-size: 0.78rem; color: var(--muted); margin-top: 0.35rem; }

  /* ── Slider ── */
  .slider-wrap { margin: 0.5rem 0; }
  input[type=range] {
    -webkit-appearance: none;
    width: 100%;
    height: 4px;
    border-radius: 2px;
    background: var(--border);
    outline: none;
    cursor: pointer;
  }
  input[type=range]::-webkit-slider-thumb {
    -webkit-appearance: none;
    width: 18px; height: 18px;
    border-radius: 50%;
    background: var(--accent);
    border: 2px solid var(--surface);
    box-shadow: 0 0 8px rgba(0,212,255,0.4);
    cursor: pointer;
    transition: box-shadow 0.15s;
  }
  input[type=range]::-webkit-slider-thumb:hover {
    box-shadow: 0 0 14px rgba(0,212,255,0.6);
  }
  input[type=range].red-thumb::-webkit-slider-thumb { background: var(--red); box-shadow: 0 0 8px rgba(255,61,90,0.4); }
  input[type=range].green-thumb::-webkit-slider-thumb { background: var(--green); box-shadow: 0 0 8px rgba(0,255,136,0.4); }

  /* ── Config inputs ── */
  .tab-content { display: none; }
  .tab-content.active { display: block; }
  .cfg-label { display: block; font-size: 0.78rem; color: var(--muted); font-weight: 600; letter-spacing: 0.05em; text-transform: uppercase; margin-bottom: 0.35rem; }
  .cfg-input {
    width: 100%;
    background: var(--surface-2);
    border: 1px solid var(--border);
    color: var(--text);
    border-radius: 8px;
    padding: 0.55rem 0.85rem;
    font-size: 0.9rem;
    font-family: 'Space Grotesk', sans-serif;
    transition: border-color 0.15s;
  }
  .cfg-input:focus { outline: none; border-color: var(--accent); box-shadow: 0 0 0 2px rgba(0,212,255,0.1); }
  .cfg-input.mono { font-family: 'JetBrains Mono', monospace; font-size: 0.82rem; }
  .cfg-test-btn {
    background: var(--accent-dim);
    border: 1px solid rgba(0,212,255,0.3);
    color: var(--accent);
    border-radius: 8px;
    padding: 0.5rem 0.9rem;
    cursor: pointer;
    font-size: 0.8rem;
    font-family: 'Space Grotesk', sans-serif;
    font-weight: 600;
    white-space: nowrap;
    transition: all 0.15s;
    position: relative; overflow: hidden;
  }
  .cfg-test-btn:hover { background: rgba(0,212,255,0.2); }
  .cfg-save-btn {
    background: linear-gradient(135deg, var(--accent), rgba(0,180,220,1));
    color: #000;
    border: none;
    border-radius: 10px;
    padding: 0.75rem 2.5rem;
    font-size: 0.95rem;
    font-weight: 700;
    font-family: 'Space Grotesk', sans-serif;
    letter-spacing: 0.05em;
    cursor: pointer;
    transition: opacity 0.15s, box-shadow 0.15s;
    position: relative; overflow: hidden;
  }
  .cfg-save-btn:hover { opacity: 0.9; box-shadow: 0 4px 20px rgba(0,212,255,0.3); }
  .sensor-row {
    background: var(--surface-2);
    border: 1px solid var(--border);
    border-radius: 10px;
    padding: 0.85rem;
  }
  .sensor-row .slabel { font-weight: 700; font-size: 0.85rem; margin-bottom: 0.15rem; color: var(--text); }
  .sensor-row .sdesc  { font-size: 0.75rem; color: var(--muted); margin-bottom: 0.5rem; }

  .chart-container { position: relative; height: 220px; }

  /* ── Entity Search Modal ── */
  #entity-modal { position:fixed; inset:0; z-index:1000; background:rgba(0,0,0,0.7); display:none; align-items:flex-start; justify-content:center; padding:4rem 1rem 1rem; }
  #entity-modal.open { display:flex; }
  #entity-modal-card { background:var(--card-bg); border:1px solid var(--border); border-radius:16px; width:100%; max-width:560px; max-height:70vh; display:flex; flex-direction:column; overflow:hidden; }
  #entity-modal-header { padding:1rem; border-bottom:1px solid var(--border); display:flex; align-items:center; justify-content:space-between; gap:0.75rem; }
  #entity-search-input { flex:1; background:var(--surface); border:1px solid var(--border); border-radius:8px; padding:0.45rem 0.75rem; color:var(--text); font-size:0.85rem; font-family:'JetBrains Mono',monospace; outline:none; }
  #entity-search-input:focus { border-color:var(--accent); }
  #entity-modal-close { background:none; border:none; color:var(--muted); cursor:pointer; font-size:1.2rem; padding:0.2rem 0.4rem; }
  #entity-results { overflow-y:auto; flex:1; }
  .entity-item { padding:0.6rem 1rem; cursor:pointer; border-bottom:1px solid rgba(255,255,255,0.04); display:flex; align-items:baseline; gap:0.75rem; }
  .entity-item:hover { background:var(--surface); }
  .entity-id { font-family:'JetBrains Mono',monospace; font-size:0.8rem; color:var(--text); flex:1; }
  .entity-state { font-family:'JetBrains Mono',monospace; font-size:0.78rem; color:var(--green); white-space:nowrap; }
  .entity-name { font-size:0.72rem; color:var(--muted); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:140px; }
  #entity-loading { padding:1.5rem; text-align:center; color:var(--muted); font-size:0.85rem; }

  /* ── Collapsible cards ── */
  .card-title.collapsible { cursor:pointer; user-select:none; display:flex; justify-content:space-between; align-items:center; }
  .card-title.collapsible::after { content:"▾"; font-size:1rem; color:var(--muted); margin-left:0.5rem; flex-shrink:0; transition:transform 0.25s; }
  .card-title.collapsible.collapsed::after { transform:rotate(-90deg); }
  .card-body.collapsed { display:none; }

  /* ── Card animation delays ── */
  .card:nth-child(1) { animation-delay: 0.05s; }
  .card:nth-child(2) { animation-delay: 0.1s; }
  .card:nth-child(3) { animation-delay: 0.15s; }
  .card:nth-child(4) { animation-delay: 0.2s; }
  .card:nth-child(5) { animation-delay: 0.25s; }
  .card:nth-child(6) { animation-delay: 0.3s; }

  /* ── Dividers ── */
  .divider { border: none; border-top: 1px solid var(--border); margin: 1rem 0; }

  /* ── Mobile tweaks ── */
  @media (max-width: 480px) {
    .hero-kw { font-size: 1.8rem; }
    .budget-main-val { font-size: 2.2rem; }
    .hero-body { gap: 0.75rem; }
    #app { padding: 0.75rem 0.75rem 2rem; }
  }
</style>
</head>
<body>
<div id="app">

<!-- ══════════════════ HERO CARD ══════════════════ -->
<div class="hero-card" id="hero-card">
  <div class="hero-top">
    <div class="hero-brand">
      <div class="hero-brand-icon">⚡</div>
      <div>
        <div class="hero-brand-name">Smart EV Charger</div>
        <div style="font-size:0.7rem; color:var(--muted); margin-top:0.1rem; display:flex; align-items:center; gap:0.4rem;">
          <span id="last-update">–</span>
          <span id="evcc-badge" style="display:none; font-size:0.65rem; font-weight:700; padding:0.1rem 0.4rem; border-radius:4px; background:var(--red-dim); color:var(--red); border:1px solid rgba(255,61,90,0.3);">evcc offline</span>
        </div>
      </div>
    </div>
    <div style="display:flex; gap:0.5rem; align-items:center;">
      <button class="nav-menu-btn" onclick="toggleTheme()" id="theme-btn" title="Hell/Dunkel">🌙</button>
    <div class="nav-menu-wrap" id="nav-menu-wrap">
      <button class="nav-menu-btn" onclick="toggleNavMenu()" id="nav-menu-btn">☰</button>
      <div class="nav-menu-dropdown" id="nav-menu-dropdown">
        <button class="tab-btn active" data-tab="status" onclick="showTab('status');toggleNavMenu()" data-i18n="tab_status">⚡ Status</button>
        <button class="tab-btn"        data-tab="config" onclick="showTab('config');toggleNavMenu()" data-i18n="tab_config">⚙ Config</button>
        <button class="tab-btn"        data-tab="debug"  onclick="showTab('debug');toggleNavMenu()"  data-i18n="tab_debug">🔍 Debug</button>
      </div>
    </div>
    </div><!-- /theme+nav wrapper -->
  </div>
  <div class="hero-controls">
    <button id="aktiv-btn"   class="ctrl-btn state-green" onclick="toggleAktiv()"  >🤖 Smart aktiv</button>
    <button id="pause-btn"   class="ctrl-btn state-green" onclick="togglePause()"  >▶ Laden bereit</button>
    <button id="schnell-btn" class="ctrl-btn schnell-btn" onclick="toggleSchnell()">⚡ Schnell</button>
  </div>

  <div class="hero-body">
    <!-- Energy flow line (visible only when charging) -->
    <div class="energy-flow" id="energy-flow">
      <div class="energy-flow-line"></div>
    </div>

    <!-- Status Icon -->
    <div class="hero-status-icon idle" id="hero-icon">⏳</div>

    <!-- Action Label + Sub -->
    <div class="hero-status-info">
      <div class="hero-action-label idle" id="action">–</div>
      <div class="hero-sub" id="grund" style="display:none">–</div>
    </div>

    <!-- Power + Bar -->
    <div style="flex:1; min-width:220px;">
      <div class="hero-power-row">
        <div>
          <span class="hero-kw off" id="hero-kw">0.0</span>
          <span class="hero-kw-unit">kW</span>
        </div>
        <div class="hero-charge-bar-wrap">
          <div class="hero-charge-bar-track">
            <div class="hero-charge-bar-fill off" id="hero-charge-bar" style="width:0%"></div>
          </div>
          <div style="display:flex; justify-content:space-between; font-size:0.68rem; color:var(--muted);">
            <span id="hero-bar-label-l">0 kWh geladen</span>
            <span id="hero-bar-label-r">–</span>
          </div>
        </div>
      </div>
    </div>
  </div>

  <!-- Bottom stats strip -->
  <div class="hero-stats-row">
    <div class="hero-stat">
      <span class="hero-stat-label" data-i18n="hero_stat_car">Auto</span>
      <span class="hero-stat-val" id="car-status">–</span>
    </div>
    <div class="hero-stat">
      <span class="hero-stat-label" data-i18n="hero_stat_evcc_mode">evcc Modus</span>
      <span class="hero-stat-val" id="evcc-mode">–</span>
    </div>
    <div class="hero-stat">
      <span class="hero-stat-label" data-i18n="hero_stat_target_current">Ziel-Strom</span>
      <span class="hero-stat-val" id="ziel-strom">–</span>
    </div>
    <div class="hero-stat">
      <span class="hero-stat-label" data-i18n="hero_stat_battery_soc">Batterie SOC</span>
      <span class="hero-stat-val" id="batt-soc">–</span>
    </div>
    <div class="hero-stat" id="auto-soc-tile" style="display:none;">
      <span class="hero-stat-label" data-i18n="hero_stat_auto_soc">Auto SOC</span>
      <span class="hero-stat-val" id="auto-soc-val">–</span>
    </div>
    <div class="hero-stat">
      <span class="hero-stat-label" data-i18n="hero_stat_pv_now">PV jetzt</span>
      <span class="hero-stat-val" id="pv-leistung">–</span>
    </div>
    <div class="hero-stat">
      <span class="hero-stat-label" data-i18n="hero_stat_charged_today">Geladen heute</span>
      <span class="hero-stat-val" id="charged">–</span>
    </div>
  </div>
</div>

<!-- ══════════════════ SETUP BANNER ══════════════════ -->
<div id="setup-banner" style="display:none; margin-bottom:1rem; padding:0.85rem 1rem;
     background:rgba(255,184,0,0.08); border:1px solid rgba(255,184,0,0.35);
     border-radius:12px; align-items:center; justify-content:space-between; gap:1rem; flex-wrap:wrap;">
  <div>
    <div style="font-weight:700; color:var(--yellow); font-size:0.85rem; margin-bottom:0.2rem;">
      ⚠ <span data-i18n="setup_banner_title">Einrichtung nicht abgeschlossen</span>
    </div>
    <div style="font-size:0.78rem; color:var(--muted);" data-i18n="setup_banner_hint">
      Bitte evcc-URL, Sensoren und Batterieeinstellungen im Config-Tab hinterlegen.
    </div>
  </div>
  <button onclick="showTab('config');toggleNavMenu()"
    style="background:var(--yellow-dim); border:1px solid rgba(255,184,0,0.4); color:var(--yellow);
           border-radius:8px; padding:0.45rem 1.1rem; cursor:pointer; font-size:0.82rem;
           font-family:'Space Grotesk',sans-serif; white-space:nowrap; flex-shrink:0;">
    <span data-i18n="setup_banner_btn">⚙ Config öffnen</span>
  </button>
</div>

<!-- ══════════════════ STATUS TAB ══════════════════ -->
<div id="tab-status" class="tab-content active">

  <!-- Connect / Restzeit Info Boxes (hidden by default) -->
  <div id="connect-box" class="info-box" style="display:none; margin-bottom:1rem;">
    <div class="info-box-label" id="connect-box-label" data-i18n="infobox_connect_until">🔌 Auto anschließen bis</div>
    <div class="info-box-val" id="connect-time" style="color:var(--accent)">–</div>
    <div class="info-box-sub" id="connect-grund">–</div>
  </div>
  <div id="restzeit-box" class="info-box green" style="display:none; margin-bottom:1rem;">
    <div class="info-box-label" data-i18n="infobox_remaining_time">Budget fertig geladen in</div>
    <div class="info-box-val" id="restzeit-gross" style="color:var(--green)">–</div>
    <div class="info-box-sub">
      <span data-i18n="infobox_remaining_still">noch</span> <span id="restzeit-kwh" style="color:var(--text)">–</span> kWh bei
      <span id="restzeit-kw"  style="color:var(--text)">–</span> kW
    </div>
    <div class="info-box-sub" style="margin-top:0.4rem; border-top:1px solid rgba(255,255,255,0.1); padding-top:0.4rem;">
      <span data-i18n="infobox_charged">Geladen</span> <span id="restzeit-charged" style="color:var(--text)">–</span> kWh
      &nbsp;|&nbsp; <span data-i18n="infobox_total_budget">Budget gesamt</span> <span id="restzeit-budget" style="color:var(--text)">–</span> kWh
    </div>
  </div>

  <div class="grid-3">

    <!-- ── Budget Card ── -->
    <div class="card">
      <div class="card-title" data-i18n="card_available_budget">Verfügbares Budget</div>

      <div style="display:flex; align-items:flex-end; gap:0.5rem; margin-bottom:0.25rem;">
        <div class="budget-main-val zero" id="available-for-car">–</div>
        <div style="font-size:1rem; color:var(--muted); padding-bottom:0.4rem;">kWh</div>
      </div>

      <div id="budget-change-grund" style="font-size:0.78rem; margin-bottom:0.5rem; display:none;"></div>

      <div class="budget-breakdown">
        <div class="budget-row">
          <span class="budget-row-label">📅 <span data-i18n="budget_daily">Tages-Budget</span> <span id="budget-ampel" style="font-size:0.9rem;">⬤</span></span>
          <span class="budget-row-val" id="daily-budget" style="color:var(--accent); font-weight:600;">–</span>
        </div>
        <div class="budget-row">
          <span class="budget-row-label">🚗 <span data-i18n="budget_already_charged">− Bereits geladen</span></span>
          <span class="budget-row-val" id="charged-budget" style="color:var(--muted)">–</span>
        </div>
        <div class="budget-row">
          <span class="budget-row-label">📤 <span data-i18n="budget_feed_today">− Einspeisung heute</span></span>
          <span class="budget-row-val" id="einspeisung-heute" style="color:var(--muted)">–</span>
        </div>
        <div class="budget-row" style="border-top:1px solid var(--border); margin-top:0.3rem; padding-top:0.3rem;">
          <span class="budget-row-label" style="color:var(--text); font-weight:600;">⚡ <span data-i18n="budget_equals_available">= Verfügbar</span></span>
          <span class="budget-row-val" id="avail-display" style="color:var(--text); font-weight:600;">–</span>
        </div>
      </div>

      <!-- Dreisegment-Balken: geladen | eingespeist | verfügbar -->
      <div style="margin-top:0.75rem;">
        <div style="display:flex; height:10px; border-radius:6px; overflow:hidden; background:var(--surface-2);">
          <div id="bar-charged"     style="height:100%; width:0%; background:var(--green); transition:width 0.5s;"></div>
          <div id="bar-einspeisung" style="height:100%; width:0%; background:var(--red);   transition:width 0.5s;"></div>
          <div id="bar-puffer"      style="height:100%; width:0%; background:#f59e0b;      transition:width 0.5s; margin-left:auto;"></div>
        </div>
        <div style="display:flex; justify-content:space-between; font-size:0.68rem; margin-top:0.25rem;">
          <span style="color:var(--green)">⬤ <span id="bar-charged-label">–</span> <span data-i18n="budget_bar_charged">geladen</span></span>
          <span style="color:var(--red)">⬤ <span id="bar-eins-label">–</span> <span data-i18n="budget_bar_feed_in">ins Netz</span></span>
          <span id="bar-puffer-wrap" style="color:#f59e0b; display:none;">⬤ <span id="bar-puffer-label">–</span> <span data-i18n="budget_bar_buffer">Puffer</span></span>
          <span style="color:var(--muted)">⬤ <span id="bar-avail-label">–</span> <span data-i18n="budget_bar_available">verfügbar</span></span>
        </div>
      </div>


      <!-- Budget = 0 ab Sonnenuntergang -->
      <div id="budget-ende-box" style="margin-top:0.4rem; font-size:0.82rem; color:var(--muted);">
        ☀️ <span data-i18n="budget_zero_at">Budget = 0 ab ca.</span> <span id="budget-ende-val" style="color:var(--text); font-weight:600;">–</span>
      </div>

      <div id="budget-until" style="display:none;"></div>
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.4rem;" id="pv-faktor-info">–</div>

      <!-- Morgen-Vorschau -->
      <div id="morgen-box" style="margin-top:0.75rem; padding:0.5rem 0.65rem; background:var(--surface-2); border:1px solid var(--border); border-radius:8px; font-size:0.78rem; color:var(--muted); display:none;">
        🌅 <span data-i18n="morgen_prognose">Morgen Prognose:</span>
        <strong id="morgen-kwh" style="color:var(--text);">–</strong>
        <span style="margin-left:0.4rem;" id="morgen-budget-text" style="color:var(--muted);"></span>
      </div>
    </div>

    <!-- ── Sensoren Card ── -->
    <div class="card">
      <div class="card-title" data-i18n="card_live_sensors">Live-Sensoren</div>
      <div class="sensor-grid-inner">
        <div class="sensor-tile">
          <div class="sensor-tile-label" data-i18n="sensor_pv_today">PV heute</div>
          <div class="sensor-tile-val" id="pv-heute" style="color:var(--yellow)">–</div>
        </div>
        <div class="sensor-tile">
          <div class="sensor-tile-label" data-i18n="sensor_battery_target">Speicher Ziel</div>
          <div class="sensor-tile-val" id="batt-ziel" style="color:var(--muted)">–</div>
        </div>
        <div class="sensor-tile">
          <div class="sensor-tile-label" data-i18n="sensor_house_real">Haus real</div>
          <div class="sensor-tile-val" id="haus-real" style="color:var(--text)">–</div>
        </div>
        <div class="sensor-tile">
          <div class="sensor-tile-label" data-i18n="sensor_total_load">Gesamt-Last</div>
          <div class="sensor-tile-val" id="haus-last" style="color:var(--muted)">–</div>
        </div>
      </div>
      <hr class="divider">
      <!-- PV Tages-Fortschritt -->
      <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.3rem;">
        <div style="font-size:0.72rem; color:var(--muted);" data-i18n="pv_forecast_today">☀️ PV Prognose heute</div>
        <div style="font-size:0.72rem; font-family:'JetBrains Mono',monospace;" id="pv-forecast-label">–</div>
      </div>
      <div style="background:var(--surface-2); border-radius:6px; height:8px; overflow:hidden; margin-bottom:0.15rem;">
        <div id="pv-forecast-bar" style="height:100%; width:0%; border-radius:6px; background:linear-gradient(90deg,var(--yellow),#ffdd00); transition:width 0.5s;"></div>
      </div>
      <div style="display:flex; justify-content:space-between; margin-top:0.1rem;">
        <div style="font-size:0.68rem; color:var(--muted);" id="pv-forecast-pct">0%</div>
        <div style="font-size:0.68rem; color:var(--muted);" id="forecast-updated">–</div>
      </div>
      <hr class="divider">
      <div style="font-size:0.72rem; color:var(--muted);" data-i18n="pv_correction_factor">PV-Korrekturfaktor</div>
      <div style="font-family:'JetBrains Mono',monospace; font-weight:600; margin-top:0.2rem;" id="pv-faktor-val">–</div>
    </div>

    <!-- ── Einstellungen Card ── -->
    <div class="card">
      <div class="card-title" data-i18n="card_settings">Einstellungen</div>
      <div style="margin-bottom:1rem;">
        <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.5rem;">
          <span class="label-sm" data-i18n="setting_min_current">Mindeststrom (evcc)</span>
          <span style="font-family:'JetBrains Mono',monospace; font-weight:700; color:var(--green);" id="min-strom-val">–</span>
        </div>
        <div class="slider-wrap">
          <input type="range" id="min-strom-slider" min="6" max="16" step="1" class="green-thumb">
        </div>
        <div style="display:flex; justify-content:space-between; font-size:0.72rem; color:var(--muted);">
          <span>6A · 1.4 kW</span><span>16A · 3.7 kW</span>
        </div>
        <div id="strom-status" style="font-size:0.72rem; color:var(--muted); margin-top:0.35rem; min-height:1rem;"></div>
      </div>

      <div class="card-title" style="margin-bottom:0.5rem;" data-i18n="ema_weekday">Haus-EMA / Wochentag</div>
      <table id="ema-table"><tbody></tbody></table>
    </div>

  </div><!-- /grid-3 -->

  <div class="card" style="margin-bottom:1rem;">
    <div class="card-title collapsible" data-body="body-chart-budget" data-i18n="chart_budget_vs_charged">14 Tage — Budget vs. Geladen</div>
    <div id="body-chart-budget" class="card-body">
      <div class="chart-container" style="height:240px;"><canvas id="chartBudget"></canvas></div>
    </div>
  </div>

  <div class="grid-2">
    <div class="card">
      <div class="card-title collapsible" data-body="body-chart-days" data-i18n="chart_14_days_energy">Letzte 14 Tage — Energie</div>
      <div id="body-chart-days" class="card-body">
        <div class="chart-container"><canvas id="chartDays"></canvas></div>
      </div>
    </div>
    <div class="card">
      <div class="card-title collapsible" data-body="body-chart-ema" data-i18n="chart_ema_learning">Haus-EMA Lernkurve</div>
      <div id="body-chart-ema" class="card-body">
        <div class="chart-container"><canvas id="chartEMA"></canvas></div>
      </div>
    </div>
  </div>

  <div class="card" style="margin-bottom:1rem;">
    <div class="card-title collapsible" data-body="body-log" data-i18n="table_control_log">Steuerungsprotokoll</div>
    <div id="body-log" class="card-body">
      <table>
        <thead><tr><th data-i18n="table_time">Zeit</th><th data-i18n="table_budget">Budget</th><th data-i18n="table_current">Strom</th><th data-i18n="table_car">Auto</th><th data-i18n="table_action">Aktion</th><th data-i18n="table_reason">Grund</th></tr></thead>
        <tbody id="log-table"></tbody>
      </table>
      <div style="margin-top:0.75rem; text-align:center;">
        <button id="log-mehr-btn" onclick="logMehr()"
          style="background:none; border:1px solid var(--border); color:var(--muted); border-radius:8px;
                 padding:0.35rem 1.2rem; cursor:pointer; font-size:0.8rem; font-family:'Space Grotesk',sans-serif; display:none;">
          <span data-i18n="btn_load_more">Mehr laden</span>
        </button>
      </div>
    </div>
  </div>

</div><!-- /tab-status -->

<!-- ══════════════════ CONFIG TAB ══════════════════ -->
<div id="tab-config" class="tab-content">

  <div class="grid-3">
    <!-- evcc / Wallbox Verbindung -->
    <div class="card">
      <div class="card-title" data-i18n="card_evcc_connection">Wallbox Verbindung</div>

      <!-- Wallbox-Typ Auswahl -->
      <div style="margin-bottom:0.85rem; padding-bottom:0.75rem; border-bottom:1px solid var(--border);">
        <select id="cfg-wallbox-type" class="cfg-input" onchange="onWallboxTypeChange()">
          <option value="evcc" data-i18n="cfg_wallbox_type_evcc">evcc (empfohlen)</option>
          <option value="ha_direct" data-i18n="cfg_wallbox_type_ha">Direkt über Home Assistant</option>
        </select>
        <div style="font-size:0.72rem; color:var(--muted); margin-top:0.3rem;" data-i18n="cfg_wallbox_type_hint">evcc bietet die beste Integration. HA-Direkt für go-eCharger, Easee & Co.</div>
      </div>

      <!-- evcc-Felder -->
      <div id="wallbox-evcc-fields">
        <div style="margin-bottom:0.85rem;">
          <label class="cfg-label" data-i18n="cfg_evcc_url">evcc URL</label>
          <div style="display:flex; gap:0.5rem;">
            <input type="text" id="cfg-evcc-url" class="cfg-input" placeholder="http://192.168.x.x:7070" data-i18n-placeholder="cfg_evcc_url_placeholder">
            <button class="cfg-test-btn" onclick="testEvcc()" data-i18n="btn_test">Test</button>
          </div>
          <div id="evcc-test-result" style="font-size:0.78rem; margin-top:0.4rem; min-height:1.2rem;"></div>
        </div>
        <div>
          <label class="cfg-label" data-i18n="cfg_loadpoint">Ladepunkt</label>
          <select id="cfg-loadpoint-id" class="cfg-input">
            <option value="1" data-i18n="cfg_loadpoint_default">Loadpoint 1 — bitte zuerst testen</option>
          </select>
        </div>
      </div>

      <!-- HA-Direkt-Felder -->
      <div id="wallbox-ha-fields" style="display:none;">
        <div style="margin-bottom:0.65rem;">
          <label class="cfg-label" data-i18n="cfg_wb_connected">Auto angesteckt (binary_sensor)</label>
          <div style="display:flex; gap:0.5rem;">
            <input type="text" id="cfg-wb-connected" class="cfg-input" placeholder="binary_sensor.wallbox_car_connected">
            <button class="cfg-test-btn" onclick="openEntitySearch('cfg-wb-connected')">🔍</button>
          </div>
        </div>
        <div style="margin-bottom:0.65rem;">
          <label class="cfg-label" data-i18n="cfg_wb_charging">Lädt gerade (binary_sensor)</label>
          <div style="display:flex; gap:0.5rem;">
            <input type="text" id="cfg-wb-charging" class="cfg-input" placeholder="binary_sensor.wallbox_charging">
            <button class="cfg-test-btn" onclick="openEntitySearch('cfg-wb-charging')">🔍</button>
          </div>
        </div>
        <div style="margin-bottom:0.65rem;">
          <label class="cfg-label" data-i18n="cfg_wb_energy">Energie heute (sensor, kWh)</label>
          <div style="display:flex; gap:0.5rem;">
            <input type="text" id="cfg-wb-energy" class="cfg-input" placeholder="sensor.wallbox_energy_session_kwh">
            <button class="cfg-test-btn" onclick="openEntitySearch('cfg-wb-energy')">🔍</button>
          </div>
        </div>
        <div style="margin-bottom:0.65rem;">
          <label class="cfg-label" data-i18n="cfg_wb_switch">Laden ein/aus (switch/input_boolean)</label>
          <div style="display:flex; gap:0.5rem;">
            <input type="text" id="cfg-wb-switch" class="cfg-input" placeholder="switch.wallbox_charging">
            <button class="cfg-test-btn" onclick="openEntitySearch('cfg-wb-switch')">🔍</button>
          </div>
        </div>
        <div>
          <label class="cfg-label" data-i18n="cfg_wb_current">Ladestrom (number, Ampere)</label>
          <div style="display:flex; gap:0.5rem;">
            <input type="text" id="cfg-wb-current" class="cfg-input" placeholder="number.wallbox_charge_current">
            <button class="cfg-test-btn" onclick="openEntitySearch('cfg-wb-current')">🔍</button>
          </div>
        </div>
      </div>
    </div>

    <!-- Fahrzeug (optional) -->
    <div class="card">
      <div class="card-title" data-i18n="card_vehicle">🚗 Fahrzeug (optional)</div>
      <div style="font-size:0.75rem; color:var(--muted); margin-bottom:0.85rem;" data-i18n="card_vehicle_hint">Wenn dein Fahrzeug den SOC an HA meldet, kann das Add-on präziser steuern und automatisch stoppen wenn das Ziel erreicht ist.</div>
      <div style="margin-bottom:0.65rem;">
        <label class="cfg-label" data-i18n="cfg_auto_soc_sensor">Fahrzeug-SOC Sensor</label>
        <div style="display:flex; gap:0.5rem;">
          <input type="text" id="cfg-auto-soc" class="cfg-input" placeholder="sensor.mein_auto_soc">
          <button class="cfg-test-btn" onclick="openEntitySearch('cfg-auto-soc')">🔍</button>
        </div>
      </div>
      <div style="margin-bottom:0.65rem;">
        <label class="cfg-label" data-i18n="cfg_auto_batterie_kwh">Fahrzeug-Batteriegröße (kWh)</label>
        <input type="number" id="cfg-auto-batt-kwh" class="cfg-input" min="0" max="200" step="0.5" placeholder="0 = nicht genutzt">
      </div>
      <div>
        <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.35rem;">
          <label class="cfg-label" style="margin:0" data-i18n="cfg_auto_ziel_soc">Ziel-SOC Fahrzeug</label>
          <span id="cfg-auto-ziel-soc-val" style="font-family:'JetBrains Mono',monospace; color:var(--accent); font-weight:700;">80%</span>
        </div>
        <input type="range" id="cfg-auto-ziel-soc" min="20" max="100" step="5"
          oninput="document.getElementById('cfg-auto-ziel-soc-val').textContent=this.value+'%'">
        <div style="display:flex; justify-content:space-between; font-size:0.72rem; color:var(--muted);">
          <span>20%</span><span>100%</span>
        </div>
      </div>
    </div>

    <!-- Batterie -->
    <div class="card">
      <div class="card-title" data-i18n="card_battery">Batterie</div>
      <!-- Schalter: Heimspeicher vorhanden -->
      <div style="display:flex; align-items:center; justify-content:space-between; margin-bottom:0.85rem; padding-bottom:0.75rem; border-bottom:1px solid var(--border);">
        <div>
          <div style="font-size:0.82rem; font-weight:600; color:var(--text);" data-i18n="cfg_has_battery">Heimspeicher vorhanden</div>
          <div style="font-size:0.72rem; color:var(--muted);" data-i18n="cfg_has_battery_hint">Deaktivieren wenn kein Batteriespeicher vorhanden ist</div>
        </div>
        <label class="toggle-switch">
          <input type="checkbox" id="cfg-has-battery" checked onchange="onHasBatteryChange()">
          <span class="toggle-slider"></span>
        </label>
      </div>
      <div id="battery-fields">
      <div style="margin-bottom:0.85rem;">
        <label class="cfg-label" data-i18n="cfg_battery_capacity">Kapazität (kWh)</label>
        <input type="number" id="cfg-batt-kap" class="cfg-input" min="1" max="100" step="0.1">
      </div>
      <div style="margin-bottom:0.85rem;">
        <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.35rem;">
          <label class="cfg-label" style="margin:0" data-i18n="cfg_battery_target_soc">Ziel-SOC</label>
          <span id="cfg-ziel-soc-val" style="font-family:'JetBrains Mono',monospace; color:var(--green); font-weight:700;">100%</span>
        </div>
        <input type="range" id="cfg-ziel-soc" min="50" max="100" step="5" class="green-thumb"
          oninput="document.getElementById('cfg-ziel-soc-val').textContent=this.value+'%'">
        <div style="display:flex; justify-content:space-between; font-size:0.72rem; color:var(--muted);">
          <span>50%</span><span>100%</span>
        </div>
      </div>
      <div>
        <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.35rem;">
          <label class="cfg-label" style="margin:0" data-i18n="cfg_battery_min_soc">Notfall-Min SOC</label>
          <span id="cfg-min-soc-val" style="font-family:'JetBrains Mono',monospace; color:var(--red); font-weight:700;">15%</span>
        </div>
        <input type="range" id="cfg-min-soc" min="5" max="30" step="1" class="red-thumb"
          oninput="document.getElementById('cfg-min-soc-val').textContent=this.value+'%'">
        <div style="display:flex; justify-content:space-between; font-size:0.72rem; color:var(--muted);">
          <span>5%</span><span>30%</span>
        </div>
      </div>
      <div style="margin-top:1rem; padding-top:1rem; border-top:1px solid var(--border);">
        <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.35rem;">
          <span class="cfg-label" style="margin:0;" data-i18n="cfg_battery_needs">Speicher-Bedarf (eingefroren)</span>
          <span style="font-family:'JetBrains Mono',monospace; font-weight:700; color:var(--yellow);" id="batt-needs-val">–</span>
        </div>
        <div style="font-size:0.72rem; color:var(--muted); margin-bottom:0.5rem;" id="batt-needs-info">–</div>
        <button id="batt-needs-reset-btn" onclick="resetBatteryNeeds()"
          style="background:var(--card-bg); border:1px solid var(--yellow); color:var(--yellow); border-radius:8px;
                 padding:0.35rem 1rem; cursor:pointer; font-size:0.8rem; font-family:'Space Grotesk',sans-serif; width:100%;">
          <span data-i18n="btn_reset_battery_needs">⟳ Speicher-Bedarf neu berechnen</span>
        </button>
        <div id="batt-reset-status" style="font-size:0.72rem; color:var(--muted); margin-top:0.35rem; min-height:1rem;"></div>
      </div>
      </div><!-- /battery-fields -->
    </div>

    <!-- System -->
    <div class="card">
      <div class="card-title" data-i18n="card_system">System</div>
      <div style="margin-bottom:0.85rem;">
        <label class="cfg-label" data-i18n="cfg_haus_verbrauch">Ø Tagesverbrauch Haus (kWh)</label>
        <input type="number" id="cfg-haus-verbrauch" class="cfg-input" min="1" max="50" step="0.5">
        <div style="font-size:0.72rem; color:var(--muted); margin-top:0.3rem;" data-i18n="cfg_haus_verbrauch_hint">Startwert für die Lernfunktion. Bei Änderung wird die EMA für alle Wochentage zurückgesetzt.</div>
      </div>
      <div style="margin-bottom:0.85rem;">
        <label class="cfg-label" data-i18n="cfg_update_interval">Update-Intervall (Min)</label>
        <input type="number" id="cfg-interval" class="cfg-input" min="1" max="60">
        <div style="font-size:0.72rem; color:var(--muted); margin-top:0.3rem;" data-i18n="cfg_interval_hint">Beim Laden immer 1 Minute</div>
      </div>
      <div style="margin-bottom:0.85rem;">
        <label class="cfg-label" data-i18n="cfg_language">Sprache / Language</label>
        <select id="cfg-language" class="cfg-input" onchange="onLangChange()">
          <option value="auto" data-i18n="lang_auto">Automatisch (HA Systemsprache)</option>
          <option value="de">Deutsch</option>
          <option value="en">English</option>
        </select>
      </div>
      <div style="margin-bottom:0.85rem;">
        <label class="cfg-label">Breitengrad (°N)</label>
        <input type="number" id="cfg-latitude" class="cfg-input" min="35" max="72" step="0.1">
        <div style="font-size:0.72rem; color:var(--muted); margin-top:0.25rem;">
          Für Sonnenzeiten-Berechnung — z.B. 51.0 (Frankfurt), 48.1 (München), 53.6 (Hamburg)
        </div>
      </div>
      <div style="margin-bottom:0.85rem;">
        <label class="cfg-label" data-i18n="cfg_bundesland">Bundesland (Feiertage)</label>
        <select id="cfg-bundesland" class="cfg-input">
          <option value=""  data-i18n="cfg_bundesland_none">Keine (Feiertage ignorieren)</option>
          <option value="BB">Brandenburg</option>
          <option value="BE">Berlin</option>
          <option value="BW">Baden-Württemberg</option>
          <option value="BY">Bayern</option>
          <option value="HB">Bremen</option>
          <option value="HE">Hessen</option>
          <option value="HH">Hamburg</option>
          <option value="MV">Mecklenburg-Vorpommern</option>
          <option value="NI">Niedersachsen</option>
          <option value="NW">Nordrhein-Westfalen</option>
          <option value="RP">Rheinland-Pfalz</option>
          <option value="SH">Schleswig-Holstein</option>
          <option value="SL">Saarland</option>
          <option value="SN">Sachsen</option>
          <option value="ST">Sachsen-Anhalt</option>
          <option value="TH">Thüringen</option>
        </select>
        <div style="font-size:0.72rem; color:var(--muted); margin-top:0.25rem;" data-i18n="cfg_bundesland_hint">
          Feiertage werden wie Sonntag behandelt — das EMA-Budget lernt Feiertage separat.
        </div>
      </div>
      <div style="padding:0.75rem; background:var(--accent-dim); border:1px solid rgba(0,212,255,0.2); border-radius:10px; font-size:0.8rem; color:var(--muted);">
        <div style="color:var(--accent); font-weight:700; margin-bottom:0.3rem; font-size:0.75rem; letter-spacing:0.06em; text-transform:uppercase;" data-i18n="ha_connection">HA Verbindung</div>
        <span data-i18n="ha_auto_supervisor">Automatisch über HA Supervisor — kein Token oder URL nötig.</span>
      </div>
    </div>
  </div>

  <!-- Prognose-Anbieter -->
  <div class="card" style="margin-bottom:1rem;">
    <div class="card-title" data-i18n="card_forecast_provider">☀️ Prognose-Anbieter</div>
    <div style="margin-bottom:0.85rem;">
      <label class="cfg-label" data-i18n="cfg_provider">Anbieter</label>
      <select id="cfg-forecast-provider" class="cfg-input" onchange="onProviderChange()">
        <option value="forecast_solar" data-i18n="provider_forecast_solar">Forecast.Solar (Standard)</option>
        <option value="solcast" data-i18n="provider_solcast_hacs">Solcast (HACS: solcast_solar)</option>
        <option value="solcast_direct" data-i18n="provider_solcast_direct">Solcast (Direkt API — kein HACS nötig)</option>
      </select>
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.3rem;" id="provider-hint">
        Forecast.Solar: kostenlos, in HA direkt integrierbar.
      </div>
    </div>

    <!-- Solcast Direkt-API Felder -->
    <div id="solcast-direct-fields" style="display:none; margin-bottom:0.85rem;">
      <label class="cfg-label" data-i18n="cfg_solcast_api_key">Solcast API-Key</label>
      <input type="password" id="cfg-solcast-api-key" class="cfg-input" autocomplete="off" data-i18n-placeholder="cfg_solcast_api_key_placeholder" placeholder="z.B. AbCdEf-12345-...">
      <label class="cfg-label" style="margin-top:0.6rem;" data-i18n="cfg_solcast_resource_id">Resource-ID (Rooftop-ID)</label>
      <input type="text" id="cfg-solcast-resource-id" class="cfg-input" data-i18n-placeholder="cfg_solcast_resource_id_placeholder" placeholder="z.B. 1234-abcd-5678-efgh">
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.4rem;" data-i18n="solcast_details_hint">
        Unter <strong>solcast.com → Rooftop Sites → Details</strong> zu finden.
        Cache: 3h (max. 8 API-Calls/Tag, kostenloses Limit: 10/Tag).
      </div>
    </div>

    <div id="provider-sensor-btn">
      <button class="cfg-test-btn" style="width:100%; padding:0.45rem;" onclick="fillProviderDefaults()" data-i18n="btn_fill_provider_defaults">
        ⟳ Sensor-IDs mit Anbieter-Defaults füllen
      </button>
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.4rem;" data-i18n="fill_defaults_hint">
        Überschreibt nur die 3 Forecast-Sensoren (PV verbleibend, heute gesamt, morgen).
        Eigene Sensoren für WR, Batterie etc. bleiben unverändert.
      </div>
    </div>
  </div>

  <!-- Sensoren -->
  <div class="card" style="margin-bottom:1rem;" id="sensoren-card">
    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:0.85rem;">
      <div class="card-title" style="margin:0" data-i18n="card_sensors">Sensoren</div>
      <button class="cfg-test-btn" onclick="testAllSensors()" data-i18n="btn_test_all_sensors">Alle testen</button>
    </div>
    <!-- WR-Hersteller -->
    <div style="margin-bottom:1rem; padding-bottom:0.85rem; border-bottom:1px solid var(--border);">
      <label class="cfg-label" data-i18n="cfg_wr_provider">Wechselrichter-Hersteller</label>
      <div style="display:flex; gap:0.5rem;">
        <select id="cfg-wr-provider" class="cfg-input" style="flex:1;">
          <option value=""       data-i18n="cfg_wr_manual">Manuell / Sonstige</option>
          <option value="growatt">Growatt</option>
          <option value="fronius">Fronius (Symo / Gen24)</option>
          <option value="sma">SMA (Sunny Boy / Tripower)</option>
          <option value="huawei">Huawei SUN2000</option>
          <option value="solaredge">SolarEdge</option>
          <option value="kostal">Kostal Plenticore</option>
          <option value="e3dc">E3/DC</option>
          <option value="enphase">Enphase</option>
        </select>
        <button class="cfg-test-btn" onclick="fillWrDefaults()" data-i18n="btn_fill_wr_defaults">Defaults füllen</button>
      </div>
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.3rem;" data-i18n="cfg_wr_hint">
        Füllt WR-spezifische Sensor-IDs mit typischen Standardwerten. Bitte danach testen &amp; ggf. anpassen.
      </div>
    </div>
    <div id="sensoren-grid" style="display:grid; grid-template-columns:repeat(auto-fit,minmax(320px,1fr)); gap:0.75rem;"></div>
  </div>

  <!-- Budget-Puffer + Ampel -->
  <div class="card">
    <div class="card-title" data-i18n="card_budget_buffer">Budget-Puffer &amp; Ampel</div>
    <div style="margin-bottom:0.85rem;">
      <label class="cfg-label" data-i18n="cfg_budget_buffer">🟠 Budget-Puffer (kWh)</label>
      <input type="number" id="cfg-budget-puffer" class="cfg-input" min="0" max="20" step="0.1">
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.25rem;" data-i18n="budget_buffer_hint">
        Diese kWh am Ende des Budgets werden nie zum Laden verwendet — Laden stoppt früher.
        Im Balken orange am rechten Ende dargestellt.
      </div>
    </div>
    <div style="margin-bottom:0.85rem;">
      <label class="cfg-label" data-i18n="cfg_ampel_green">🟢 Grün ab (kWh) — Budget sicher</label>
      <input type="number" id="cfg-ampel-gruen" class="cfg-input" min="-5" max="10" step="0.1">
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.25rem;" data-i18n="ampel_green_hint">Budget ≥ dieser Wert → grün</div>
    </div>
    <div>
      <label class="cfg-label" data-i18n="cfg_ampel_yellow">🟡 Gelb ab (kWh) — Budget knapp</label>
      <input type="number" id="cfg-ampel-gelb" class="cfg-input" min="-10" max="5" step="0.1">
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.25rem;" data-i18n="ampel_yellow_hint">Budget ≥ dieser Wert → gelb, darunter → 🔴 rot</div>
    </div>
  </div>

  <!-- Benachrichtigungen -->
  <div class="card" style="margin-bottom:1rem;">
    <div class="card-title">🔔 Benachrichtigungen</div>
    <div style="margin-bottom:0.85rem;">
      <label class="cfg-label">HA Notification Target</label>
      <div style="display:flex; gap:0.5rem;">
        <input type="text" id="cfg-notify-target" class="cfg-input" placeholder="z.B. mobile_app_mein_iphone">
        <button class="cfg-test-btn" onclick="testNotify()">Test</button>
      </div>
      <div id="notify-test-result" style="font-size:0.78rem; margin-top:0.4rem; min-height:1.2rem;"></div>
      <div style="font-size:0.72rem; color:var(--muted); margin-top:0.25rem;">
        In HA unter <strong>Einstellungen → Companion App → Benachrichtigungen</strong> zu finden.
        Leer lassen = keine Benachrichtigungen.
      </div>
    </div>

    <div style="display:flex; flex-direction:column; gap:0.7rem;">
      <!-- Budget fast leer -->
      <div style="display:flex; align-items:center; justify-content:space-between; gap:0.75rem; flex-wrap:wrap;">
        <div style="flex:1; min-width:180px;">
          <div style="font-size:0.82rem; font-weight:600; color:var(--text);">⚡ Budget fast leer</div>
          <div style="font-size:0.72rem; color:var(--muted);">Benachrichtigung wenn verfügbares Budget unter Schwellwert sinkt</div>
        </div>
        <div style="display:flex; align-items:center; gap:0.6rem; flex-shrink:0;">
          <input type="number" id="cfg-notify-budget-kwh" class="cfg-input"
                 style="width:80px; margin:0;" min="0.1" max="10" step="0.1" value="0.5">
          <span style="font-size:0.75rem; color:var(--muted);">kWh</span>
          <label class="toggle-switch">
            <input type="checkbox" id="cfg-notify-budget-low">
            <span class="toggle-slider"></span>
          </label>
        </div>
      </div>

      <!-- Deadline drängt -->
      <div style="display:flex; align-items:center; justify-content:space-between; gap:0.75rem;">
        <div style="flex:1;">
          <div style="font-size:0.82rem; font-weight:600; color:var(--text);">🔌 Ansteck-Deadline drängt</div>
          <div style="font-size:0.72rem; color:var(--muted);">Wenn weniger als 1h bis das Budget sinkt</div>
        </div>
        <label class="toggle-switch" style="flex-shrink:0;">
          <input type="checkbox" id="cfg-notify-deadline">
          <span class="toggle-slider"></span>
        </label>
      </div>

      <!-- Laden fertig -->
      <div style="display:flex; align-items:center; justify-content:space-between; gap:0.75rem;">
        <div style="flex:1;">
          <div style="font-size:0.82rem; font-weight:600; color:var(--text);">✅ Laden fertig</div>
          <div style="font-size:0.72rem; color:var(--muted);">Wenn das Auto abgesteckt wird nachdem es geladen hat</div>
        </div>
        <label class="toggle-switch" style="flex-shrink:0;">
          <input type="checkbox" id="cfg-notify-laden-fertig">
          <span class="toggle-slider"></span>
        </label>
      </div>
    </div>
  </div>

  <!-- Export / Import -->
  <div class="card" style="margin-bottom:1rem;">
    <div class="card-title" data-i18n="card_backup">Backup &amp; Wiederherstellung</div>
    <div style="display:flex; gap:0.75rem; flex-wrap:wrap; margin-bottom:0.6rem;">
      <button class="cfg-test-btn" style="flex:1; padding:0.55rem;" onclick="exportConfig()" data-i18n="btn_export_config">
        ⬇ Config exportieren
      </button>
      <button class="cfg-test-btn" style="flex:1; padding:0.55rem;" onclick="document.getElementById('import-file').click()" data-i18n="btn_import_config">
        ⬆ Config importieren
      </button>
      <input type="file" id="import-file" accept=".json" style="display:none" onchange="importConfig(this)">
    </div>
    <div id="backup-result" style="font-size:0.78rem; min-height:1rem; color:var(--muted);"></div>
    <div style="font-size:0.72rem; color:var(--muted); margin-top:0.3rem;" data-i18n="backup_hint">
      Export speichert alle Einstellungen inkl. Sensor-IDs. Import überschreibt die aktuelle Konfiguration.
    </div>
  </div>

  <!-- Speichern -->
  <div style="text-align:center; margin-bottom:2rem;">
    <button class="cfg-save-btn" onclick="saveConfig()" data-i18n="btn_save_config">Konfiguration speichern</button>
    <div id="cfg-save-result" style="font-size:0.85rem; margin-top:0.6rem; min-height:1.5rem;"></div>
  </div>

</div><!-- /tab-config -->

<div id="tab-debug" class="tab-content">
  <div class="card" style="margin-bottom:1rem;">
    <div style="display:flex; align-items:center; justify-content:space-between; flex-wrap:wrap; gap:1rem;">
      <div>
        <div class="card-label" data-i18n="card_debug_mode">Debug-Modus</div>
        <div class="card-sub" style="margin-top:0.25rem;" data-i18n="debug_mode_desc">Detaillierte Erklärungen bei jedem Wertewechsel</div>
      </div>
      <label style="display:flex; align-items:center; gap:0.75rem; cursor:pointer;">
        <span id="debug-mode-label" style="color:var(--muted); font-size:0.85rem;">AUS</span>
        <div id="debug-toggle" onclick="toggleDebugMode()" style="width:48px;height:26px;border-radius:13px;background:var(--border);position:relative;cursor:pointer;transition:background 0.2s;">
          <div id="debug-knob" style="width:20px;height:20px;border-radius:50%;background:#fff;position:absolute;top:3px;left:3px;transition:left 0.2s;"></div>
        </div>
      </label>
    </div>
  </div>
  <div class="card">
    <div style="display:flex; align-items:center; justify-content:space-between; margin-bottom:0.75rem;">
      <div class="card-label" data-i18n="card_debug_log">Debug-Log</div>
      <button onclick="clearDebugLog()" style="background:var(--border);color:var(--muted);border:none;padding:0.3rem 0.75rem;border-radius:6px;cursor:pointer;font-size:0.8rem;" data-i18n="btn_clear_log">Leeren</button>
    </div>
    <div id="debug-log" style="font-family:'JetBrains Mono',monospace;font-size:0.78rem;line-height:1.6;max-height:60vh;overflow-y:auto;color:var(--muted);">
      <span style="color:var(--border);">— Debug-Modus aktivieren um Logs zu sehen —</span>
    </div>
  </div>
</div><!-- /tab-debug -->

<!-- ══════════════════ ENTITY SEARCH MODAL ══════════════════ -->
<div id="entity-modal" onclick="if(event.target===this)closeEntitySearch()">
  <div id="entity-modal-card">
    <div id="entity-modal-header">
      <input id="entity-search-input" type="text" placeholder="sensor. suchen…" oninput="filterEntities(this.value)" autocomplete="off" spellcheck="false">
      <button id="entity-modal-close" onclick="closeEntitySearch()">✕</button>
    </div>
    <div id="entity-results"><div id="entity-loading">…</div></div>
  </div>
</div>

</div><!-- /app -->

<script>
// ─── i18n ─────────────────────────────────────────────────────────────────────
const TRANSLATIONS = {
  de: {
    tab_status:"⚡ Status", tab_config:"⚙ Config", tab_debug:"🔍 Debug",
    btn_schlaf:"Schlaf",
    btn_schnell:"⚡ Schnell möglich", btn_schnell_on:"⚡ Schnell AN", btn_schnell_off:"Schnell nicht möglich",
    hero_stat_car:"Auto", hero_stat_evcc_mode:"evcc Modus",
    hero_stat_target_current:"Ziel-Strom", hero_stat_battery_soc:"Batterie SOC",
    hero_stat_pv_now:"PV jetzt", hero_stat_charged_today:"Geladen heute",
    hero_day_complete:"Tag abgeschlossen", hero_no_budget:"Kein Budget",
    badge_car_disconnected:"Nicht verbunden", badge_charging:"Lädt", badge_connected:"Verbunden",
    action_laden:"Laden", action_idle:"Bereit", action_bereit:"Warte auf PV / Auto voll",
    action_auto_voll:"Auto voll", action_kein_budget:"Kein Budget",
    action_pausiert:"Pausiert", action_batterie_schutz:"Batterieschutz", action_start:"Start", action_schlaf:"Schlaf",
    morgen_prognose:"Morgen Prognose:",
    infobox_connect_until:"🔌 Auto anschließen bis",
    infobox_remaining_time:"Budget fertig geladen in",
    infobox_remaining_still:"noch", infobox_charged:"Geladen", infobox_total_budget:"Budget gesamt",
    card_available_budget:"Verfügbares Budget",
    budget_daily:"Tages-Budget", budget_already_charged:"− Bereits geladen",
    budget_feed_today:"− Einspeisung heute", budget_equals_available:"= Verfügbar",
    budget_bar_charged:"geladen", budget_bar_feed_in:"ins Netz",
    budget_bar_buffer:"Puffer", budget_bar_available:"verfügbar",
    budget_zero_at:"Budget = 0 ab ca.",
    pv_budget_fully_available:"(Budget voll ausschöpfbar)",
    pv_less_than_budget:"(weniger als Budget — PV limitiert)",
    card_live_sensors:"Live-Sensoren",
    sensor_pv_today:"PV heute", sensor_battery_target:"Speicher Ziel",
    sensor_house_real:"Haus real", sensor_total_load:"Gesamt-Last",
    pv_forecast_today:"☀️ PV Prognose heute", pv_correction_factor:"PV-Korrekturfaktor",
    card_settings:"Einstellungen", setting_min_current:"Mindeststrom (evcc)",
    ema_weekday:"Haus-EMA / Wochentag",
    setup_banner_title:"Einrichtung nicht abgeschlossen",
    setup_banner_hint:"Bitte evcc-URL, Sensoren und Batterieeinstellungen im Config-Tab hinterlegen.",
    setup_banner_btn:"⚙ Config öffnen",
    cfg_bundesland:"Bundesland (Feiertage)", cfg_bundesland_none:"Keine (Feiertage ignorieren)",
    cfg_bundesland_hint:"Feiertage werden wie Sonntag behandelt — EMA lernt sie separat.",
    chart_budget_vs_charged:"14 Tage — Budget vs. Geladen",
    chart_budget:"Budget", chart_charged:"Geladen",
    chart_14_days_energy:"Letzte 14 Tage — Energie", chart_ema_learning:"Haus-EMA Lernkurve",
    chart_pv_forecast:"PV Prognose", chart_pv_real:"PV Real",
    chart_car_charged:"Auto geladen", chart_house:"Haus",
    chart_feed_in:"Einspeisung", chart_house_real:"Haus real", chart_ema_learned:"EMA (gelernt)",
    table_control_log:"Steuerungsprotokoll",
    table_time:"Zeit", table_budget:"Budget", table_current:"Strom",
    table_car:"Auto", table_action:"Aktion", table_reason:"Grund",
    btn_load_more:"Mehr laden",
    day_monday:"Montag", day_tuesday:"Dienstag", day_wednesday:"Mittwoch",
    day_thursday:"Donnerstag", day_friday:"Freitag", day_saturday:"Samstag", day_sunday:"Sonntag",
    today_label:"heute",
    cfg_haus_verbrauch:"Ø Tagesverbrauch Haus (kWh)",
    cfg_haus_verbrauch_hint:"Startwert für die Lernfunktion. Bei Änderung wird die EMA für alle Wochentage zurückgesetzt.",
    card_vehicle:"🚗 Fahrzeug (optional)",
    card_vehicle_hint:"Wenn dein Fahrzeug den SOC an HA meldet, kann das Add-on präziser steuern und automatisch stoppen wenn das Ziel erreicht ist.",
    cfg_auto_soc_sensor:"Fahrzeug-SOC Sensor",
    cfg_auto_batterie_kwh:"Fahrzeug-Batteriegröße (kWh)",
    cfg_auto_ziel_soc:"Ziel-SOC Fahrzeug",
    hero_stat_auto_soc:"Auto SOC",
    action_auto_voll:"Auto voll",
    card_evcc_connection:"Wallbox Verbindung",
    cfg_wallbox_type:"Wallbox-Steuerung",
    cfg_wallbox_type_evcc:"evcc (empfohlen)",
    cfg_wallbox_type_ha:"Direkt über Home Assistant",
    cfg_wallbox_type_hint:"evcc bietet die beste Integration. HA-Direkt für go-eCharger, Easee & Co.",
    cfg_wb_connected:"Auto angesteckt (binary_sensor)",
    cfg_wb_charging:"Lädt gerade (binary_sensor)",
    cfg_wb_energy:"Energie heute (sensor, kWh)",
    cfg_wb_switch:"Laden ein/aus (switch/input_boolean)",
    cfg_wb_current:"Ladestrom (number, Ampere)",
    cfg_evcc_url:"evcc URL",
    cfg_evcc_url_placeholder:"http://192.168.x.x:7070",
    btn_test:"Test", cfg_loadpoint:"Ladepunkt",
    cfg_loadpoint_default:"Loadpoint 1 — bitte zuerst testen",
    evcc_testing:"Verbindung wird getestet…",
    evcc_connection_error:"Verbindungsfehler:",
    card_battery:"Batterie",
    cfg_has_battery:"Heimspeicher vorhanden", cfg_has_battery_hint:"Deaktivieren wenn kein Batteriespeicher vorhanden",
    cfg_battery_capacity:"Kapazität (kWh)",
    cfg_battery_target_soc:"Ziel-SOC", cfg_battery_min_soc:"Notfall-Min SOC",
    cfg_battery_needs:"Speicher-Bedarf (eingefroren)",
    btn_reset_battery_needs:"⟳ Speicher-Bedarf neu berechnen",
    battery_needs_calculating:"Wird berechnet…",
    battery_needs_connection_error:"Verbindungsfehler",
    card_system:"System", cfg_update_interval:"Update-Intervall (Min)",
    cfg_interval_hint:"Beim Laden immer 1 Minute",
    cfg_language:"Sprache / Language", lang_auto:"Automatisch (HA Systemsprache)",
    ha_connection:"HA Verbindung",
    ha_auto_supervisor:"Automatisch über HA Supervisor — kein Token oder URL nötig.",
    card_forecast_provider:"☀️ Prognose-Anbieter", cfg_provider:"Anbieter",
    provider_forecast_solar:"Forecast.Solar (Standard)",
    provider_solcast_hacs:"Solcast (HACS: solcast_solar)",
    provider_solcast_direct:"Solcast (Direkt API — kein HACS nötig)",
    cfg_solcast_api_key:"Solcast API-Key",
    cfg_solcast_api_key_placeholder:"z.B. AbCdEf-12345-...",
    cfg_solcast_resource_id:"Resource-ID (Rooftop-ID)",
    cfg_solcast_resource_id_placeholder:"z.B. 1234-abcd-5678-efgh",
    solcast_details_hint:"Unter solcast.com → Rooftop Sites → Details zu finden. Cache: 3h (max. 8 API-Calls/Tag, kostenloses Limit: 10/Tag).",
    cfg_wr_provider:"Wechselrichter-Hersteller", cfg_wr_manual:"Manuell / Sonstige",
    cfg_wr_hint:"Füllt WR-spezifische Sensor-IDs mit typischen Standardwerten. Bitte danach testen & ggf. anpassen.",
    btn_fill_wr_defaults:"Defaults füllen", wr_ids_filled:"WR-Sensor-IDs gefüllt — bitte testen & speichern!",
    btn_fill_provider_defaults:"⟳ Sensor-IDs mit Anbieter-Defaults füllen",
    fill_defaults_hint:"Überschreibt nur die 3 Forecast-Sensoren (PV verbleibend, heute gesamt, morgen). Eigene Sensoren für WR, Batterie etc. bleiben unverändert.",
    sensor_ids_filled:"Sensor-IDs gefüllt — bitte testen & speichern!",
    card_sensors:"Sensoren", btn_test_all_sensors:"Alle testen",
    card_budget_buffer:"Budget-Puffer & Ampel",
    cfg_budget_buffer:"🟠 Budget-Puffer (kWh)",
    budget_buffer_hint:"Diese kWh am Ende des Budgets werden nie zum Laden verwendet — Laden stoppt früher. Im Balken orange am rechten Ende dargestellt.",
    cfg_ampel_green:"🟢 Grün ab (kWh) — Budget sicher",
    ampel_green_hint:"Budget ≥ dieser Wert → grün",
    cfg_ampel_yellow:"🟡 Gelb ab (kWh) — Budget knapp",
    ampel_yellow_hint:"Budget ≥ dieser Wert → gelb, darunter → 🔴 rot",
    card_backup:"Backup & Wiederherstellung",
    btn_export_config:"⬇ Config exportieren", btn_import_config:"⬆ Config importieren",
    backup_hint:"Export speichert alle Einstellungen inkl. Sensor-IDs. Import überschreibt die aktuelle Konfiguration.",
    btn_save_config:"Konfiguration speichern",
    config_saving:"Speichern…",
    config_save_success:"✓ Gespeichert — neue Werte gelten ab dem nächsten Zyklus",
    config_connection_error:"✗ Verbindungsfehler",
    card_debug_mode:"Debug-Modus",
    debug_mode_desc:"Detaillierte Erklärungen bei jedem Wertewechsel",
    debug_off:"AUS", debug_on:"AN",
    card_debug_log:"Debug-Log", btn_clear_log:"Leeren",
    debug_activate_message:"— Debug-Modus aktivieren um Logs zu sehen —",
    debug_log_cleared:"— Log geleert —",
    debug_no_entries:"— Noch keine Einträge. Warte auf nächsten Loop… —",
    sensor_unavailable:"Sensor nicht verfügbar",
    sensor_no_entity_id:"Keine entity_id angegeben",
    pv_forecast_pct_suffix:"% des Tagesforecasts",
    infobox_connect_urgent:"⚠️ Budget sinkt — Auto anschließen!",
    hint_forecast_solar:"Forecast.Solar: kostenlos, in HA direkt integrierbar (Integration: Forecast.Solar).",
    hint_solcast_hacs:"Solcast: genauer durch ML + historische Daten. Kostenlos bis 10 API-Calls/Tag (HACS: solcast_solar).",
    hint_solcast_direct:"Solcast Direkt: Add-on ruft Solcast-API direkt ab — kein HACS nötig. API-Key + Resource-ID erforderlich. Cache: 3h.",
  },
  en: {
    tab_status:"⚡ Status", tab_config:"⚙ Config", tab_debug:"🔍 Debug",
    btn_schlaf:"Sleep",
    btn_schnell:"⚡ Fast charge possible", btn_schnell_on:"⚡ Fast ON", btn_schnell_off:"Fast charge unavailable",
    hero_stat_car:"Car", hero_stat_evcc_mode:"evcc Mode",
    hero_stat_target_current:"Target Current", hero_stat_battery_soc:"Battery SOC",
    hero_stat_pv_now:"PV now", hero_stat_charged_today:"Charged today",
    hero_day_complete:"Day complete", hero_no_budget:"No budget",
    badge_car_disconnected:"Not connected", badge_charging:"Charging", badge_connected:"Connected",
    action_laden:"Charging", action_idle:"Ready", action_bereit:"Waiting for PV / Car full",
    action_auto_voll:"Car full", action_kein_budget:"No Budget",
    action_pausiert:"Paused", action_batterie_schutz:"Battery Protection", action_start:"Start", action_schlaf:"Sleep",
    morgen_prognose:"Tomorrow forecast:",
    infobox_connect_until:"🔌 Connect car by",
    infobox_remaining_time:"Budget fully charged in",
    infobox_remaining_still:"still", infobox_charged:"Charged", infobox_total_budget:"Total budget",
    card_available_budget:"Available Budget",
    budget_daily:"Daily Budget", budget_already_charged:"− Already charged",
    budget_feed_today:"− Feed-in today", budget_equals_available:"= Available",
    budget_bar_charged:"charged", budget_bar_feed_in:"to grid",
    budget_bar_buffer:"buffer", budget_bar_available:"available",
    budget_zero_at:"Budget = 0 from approx.",
    pv_budget_fully_available:"(budget fully usable)",
    pv_less_than_budget:"(less than budget — PV limited)",
    card_live_sensors:"Live Sensors",
    sensor_pv_today:"PV today", sensor_battery_target:"Battery Target",
    sensor_house_real:"House actual", sensor_total_load:"Total Load",
    pv_forecast_today:"☀️ PV Forecast today", pv_correction_factor:"PV Correction Factor",
    card_settings:"Settings", setting_min_current:"Min Current (evcc)",
    ema_weekday:"House EMA / Weekday",
    setup_banner_title:"Setup not complete",
    setup_banner_hint:"Please configure evcc URL, sensors and battery settings in the Config tab.",
    setup_banner_btn:"⚙ Open Config",
    cfg_bundesland:"Federal State (Holidays)", cfg_bundesland_none:"None (ignore holidays)",
    cfg_bundesland_hint:"Holidays are treated like Sunday — EMA learns them separately.",
    chart_budget_vs_charged:"14 Days — Budget vs. Charged",
    chart_budget:"Budget", chart_charged:"Charged",
    chart_14_days_energy:"Last 14 Days — Energy", chart_ema_learning:"House EMA Learning Curve",
    chart_pv_forecast:"PV Forecast", chart_pv_real:"PV Real",
    chart_car_charged:"Car charged", chart_house:"House",
    chart_feed_in:"Feed-in", chart_house_real:"House actual", chart_ema_learned:"EMA (learned)",
    table_control_log:"Control Log",
    table_time:"Time", table_budget:"Budget", table_current:"Current",
    table_car:"Car", table_action:"Action", table_reason:"Reason",
    btn_load_more:"Load more",
    day_monday:"Monday", day_tuesday:"Tuesday", day_wednesday:"Wednesday",
    day_thursday:"Thursday", day_friday:"Friday", day_saturday:"Saturday", day_sunday:"Sunday",
    today_label:"today",
    cfg_haus_verbrauch:"Ø Daily House Consumption (kWh)",
    cfg_haus_verbrauch_hint:"Seed value for the learning function. Changing this resets the EMA for all weekdays.",
    card_vehicle:"🚗 Vehicle (optional)",
    card_vehicle_hint:"If your vehicle reports SOC to HA, the add-on can control more precisely and stop automatically when the target is reached.",
    cfg_auto_soc_sensor:"Vehicle SOC Sensor",
    cfg_auto_batterie_kwh:"Vehicle Battery Size (kWh)",
    cfg_auto_ziel_soc:"Vehicle Target SOC",
    hero_stat_auto_soc:"Car SOC",
    action_auto_voll:"Car full",
    card_evcc_connection:"Wallbox Connection",
    cfg_wallbox_type:"Wallbox Control",
    cfg_wallbox_type_evcc:"evcc (recommended)",
    cfg_wallbox_type_ha:"Direct via Home Assistant",
    cfg_wallbox_type_hint:"evcc offers the best integration. HA-Direct for go-eCharger, Easee & Co.",
    cfg_wb_connected:"Car connected (binary_sensor)",
    cfg_wb_charging:"Currently charging (binary_sensor)",
    cfg_wb_energy:"Energy today (sensor, kWh)",
    cfg_wb_switch:"Charging on/off (switch/input_boolean)",
    cfg_wb_current:"Charge current (number, Amps)",
    cfg_evcc_url:"evcc URL",
    cfg_evcc_url_placeholder:"http://192.168.x.x:7070",
    btn_test:"Test", cfg_loadpoint:"Loadpoint",
    cfg_loadpoint_default:"Loadpoint 1 — please test first",
    evcc_testing:"Testing connection…",
    evcc_connection_error:"Connection error:",
    card_battery:"Battery",
    cfg_has_battery:"Home battery installed", cfg_has_battery_hint:"Disable if no battery storage present",
    cfg_battery_capacity:"Capacity (kWh)",
    cfg_battery_target_soc:"Target SOC", cfg_battery_min_soc:"Emergency Min SOC",
    cfg_battery_needs:"Storage Needs (frozen)",
    btn_reset_battery_needs:"⟳ Recalculate Storage Needs",
    battery_needs_calculating:"Calculating…",
    battery_needs_connection_error:"Connection error",
    card_system:"System", cfg_update_interval:"Update Interval (Min)",
    cfg_interval_hint:"Always 1 minute while charging",
    cfg_language:"Language", lang_auto:"Automatic (HA system language)",
    ha_connection:"HA Connection",
    ha_auto_supervisor:"Automatic via HA Supervisor — no token or URL needed.",
    card_forecast_provider:"☀️ Forecast Provider", cfg_provider:"Provider",
    provider_forecast_solar:"Forecast.Solar (Default)",
    provider_solcast_hacs:"Solcast (HACS: solcast_solar)",
    provider_solcast_direct:"Solcast (Direct API — no HACS needed)",
    cfg_solcast_api_key:"Solcast API Key",
    cfg_solcast_api_key_placeholder:"e.g. AbCdEf-12345-...",
    cfg_solcast_resource_id:"Resource ID (Rooftop ID)",
    cfg_solcast_resource_id_placeholder:"e.g. 1234-abcd-5678-efgh",
    solcast_details_hint:"Find at solcast.com → Rooftop Sites → Details. Cache: 3h (max. 8 API calls/day, free limit: 10/day).",
    cfg_wr_provider:"Inverter Manufacturer", cfg_wr_manual:"Manual / Other",
    cfg_wr_hint:"Fills inverter-specific sensor IDs with typical default values. Please test & adjust afterwards.",
    btn_fill_wr_defaults:"Fill defaults", wr_ids_filled:"Inverter sensor IDs filled — please test & save!",
    btn_fill_provider_defaults:"⟳ Fill Sensor IDs with Provider Defaults",
    fill_defaults_hint:"Only overwrites the 3 forecast sensors (PV remaining, today total, tomorrow). Custom sensors for inverter, battery etc. remain unchanged.",
    sensor_ids_filled:"Sensor IDs filled — please test & save!",
    card_sensors:"Sensors", btn_test_all_sensors:"Test all",
    card_budget_buffer:"Budget Buffer & Traffic Light",
    cfg_budget_buffer:"🟠 Budget Buffer (kWh)",
    budget_buffer_hint:"These kWh at the end of the budget are never used for charging — charging stops earlier. Shown in orange at the right end of the bar.",
    cfg_ampel_green:"🟢 Green from (kWh) — Budget safe",
    ampel_green_hint:"Budget ≥ this value → green",
    cfg_ampel_yellow:"🟡 Yellow from (kWh) — Budget tight",
    ampel_yellow_hint:"Budget ≥ this value → yellow, below → 🔴 red",
    card_backup:"Backup & Restore",
    btn_export_config:"⬇ Export Config", btn_import_config:"⬆ Import Config",
    backup_hint:"Export saves all settings including sensor IDs. Import overwrites the current configuration.",
    btn_save_config:"Save Configuration",
    config_saving:"Saving…",
    config_save_success:"✓ Saved — new values apply from next cycle",
    config_connection_error:"✗ Connection error",
    card_debug_mode:"Debug Mode",
    debug_mode_desc:"Detailed explanations for every value change",
    debug_off:"OFF", debug_on:"ON",
    card_debug_log:"Debug Log", btn_clear_log:"Clear",
    debug_activate_message:"— Activate debug mode to see logs —",
    debug_log_cleared:"— Log cleared —",
    debug_no_entries:"— No entries yet. Waiting for next cycle… —",
    sensor_unavailable:"Sensor unavailable",
    sensor_no_entity_id:"No entity_id specified",
    pv_forecast_pct_suffix:"% of day forecast",
    infobox_connect_urgent:"⚠️ Budget dropping — connect car!",
    hint_forecast_solar:"Forecast.Solar: free, directly integratable in HA (Integration: Forecast.Solar).",
    hint_solcast_hacs:"Solcast: more accurate via ML + historical data. Free up to 10 API calls/day (HACS: solcast_solar).",
    hint_solcast_direct:"Solcast Direct: add-on calls Solcast API directly — no HACS needed. API key + resource ID required. Cache: 3h.",
  }
};

let _lang = 'de';

function t(key) {
  return (TRANSLATIONS[_lang] || TRANSLATIONS.de)[key] || TRANSLATIONS.de[key] || key;
}

function applyTranslations(lang) {
  _lang = (TRANSLATIONS[lang] ? lang : 'de');
  document.querySelectorAll('[data-i18n]').forEach(el => {
    const val = t(el.dataset.i18n);
    if (val) el.textContent = val;
  });
  document.querySelectorAll('[data-i18n-placeholder]').forEach(el => {
    const val = t(el.dataset.i18nPlaceholder);
    if (val) el.placeholder = val;
  });
}

// ─── Theme ────────────────────────────────────────────────────────────────────
function applyTheme(light) {
  document.documentElement.classList.toggle("light", light);
  const btn = document.getElementById("theme-btn");
  if (btn) btn.textContent = light ? "🌙" : "☀️";
}
function toggleTheme() {
  const isLight = !document.documentElement.classList.contains("light");
  localStorage.setItem("theme", isLight ? "light" : "dark");
  applyTheme(isLight);
}
// Beim Start sofort anwenden (vor erstem Render)
(function() {
  const saved = localStorage.getItem("theme");
  const preferLight = saved ? saved === "light" : window.matchMedia("(prefers-color-scheme: light)").matches;
  applyTheme(preferLight);
})();

function onHasBatteryChange() {
  const hasBatt = document.getElementById("cfg-has-battery").checked;
  document.getElementById("battery-fields").style.display = hasBatt ? "" : "none";
}

function onWallboxTypeChange() {
  const v = document.getElementById("cfg-wallbox-type")?.value || "evcc";
  document.getElementById("wallbox-evcc-fields").style.display = v === "evcc" ? "" : "none";
  document.getElementById("wallbox-ha-fields").style.display   = v === "ha_direct" ? "" : "none";
}

function onLangChange() {
  const lang = document.getElementById("cfg-language").value;
  // Sofort anwenden (Vorschau)
  const active = (lang === "auto") ? (_activeLangFromConfig || "de") : lang;
  applyTranslations(active);
}

let _activeLangFromConfig = "de";

// ─── Action Labels (sprachabhängig) ───────────────────────────────────────────
function getActionLabels() {
  return {
    laden:           t("action_laden"),
    idle:            t("action_idle"),
    bereit:          t("action_bereit"),
    auto_voll:       t("action_auto_voll"),
    kein_budget:     t("action_kein_budget"),
    pausiert:        t("action_pausiert"),
    batterie_schutz: t("action_batterie_schutz"),
    start:           t("action_start"),
  };
}

const ACTION_LABELS = {
  laden:"Laden", idle:"Bereit", bereit:"Warte auf PV / Auto voll",
  auto_voll:"Auto voll", kein_budget:"Kein Budget", pausiert:"Pausiert",
  batterie_schutz:"Batterieschutz", start:"Start", schlaf:"Schlaf"
};

const ACTION_ICONS = {
  laden:"⚡", idle:"⏸", bereit:"🔋", auto_voll:"🚗",
  kein_budget:"☁", pausiert:"⏸", batterie_schutz:"🔋", start:"⏳", schlaf:"😴"
};

function setHeroStatus(action) {
  const iconEl   = document.getElementById("hero-icon");
  const actionEl = document.getElementById("action");
  iconEl.className   = "hero-status-icon " + action;
  iconEl.textContent = ACTION_ICONS[action] || "⏳";
  actionEl.className = "hero-action-label " + action;
  actionEl.textContent = t("action_" + action) || ACTION_LABELS[action] || action;
}

function fmt(v, unit="", dec=1) {
  if (v === null || v === undefined) return "–";
  return Number(v).toFixed(dec) + (unit ? " " + unit : "");
}

const BASE = window.location.pathname.replace(/\/$/, "");

// ─── Nav-Menü ─────────────────────────────────────────────────────────────────
function toggleNavMenu() {
  const dd = document.getElementById("nav-menu-dropdown");
  dd.classList.toggle("open");
}
// Klick außerhalb schließt Menü
document.addEventListener("click", function(e) {
  const wrap = document.getElementById("nav-menu-wrap");
  if (wrap && !wrap.contains(e.target)) {
    document.getElementById("nav-menu-dropdown").classList.remove("open");
  }
});

// ─── Tab-Navigation ───────────────────────────────────────────────────────────
function showTab(name) {
  document.querySelectorAll(".tab-content").forEach(el => el.classList.remove("active"));
  document.querySelectorAll(".tab-btn").forEach(el => el.classList.remove("active"));
  document.getElementById("tab-" + name).classList.add("active");
  document.querySelector(".tab-btn[data-tab='" + name + "']").classList.add("active");
  if (name === "config") {
    buildSensorFields();
    loadConfig();
  }
  if (name === "debug") {
    loadDebugState();
  }
}

// ─── Count-up animation for kW display ───────────────────────────────────────
let _lastKw = 0;
function animateKw(targetKw) {
  const el = document.getElementById("hero-kw");
  if (targetKw === null) { el.textContent = "–"; _lastKw = 0; return; }
  const start = _lastKw;
  const diff  = targetKw - start;
  if (Math.abs(diff) < 0.05) { el.textContent = targetKw.toFixed(2); _lastKw = targetKw; return; }
  const steps = 20;
  let i = 0;
  const step = () => {
    i++;
    const v = start + diff * (i / steps);
    el.textContent = v.toFixed(2);
    if (i < steps) requestAnimationFrame(step);
    else { el.textContent = targetKw.toFixed(2); _lastKw = targetKw; }
  };
  requestAnimationFrame(step);
}

// ─── Status Tab ───────────────────────────────────────────────────────────────
async function loadState() {
  const r = await fetch(BASE + "/api/state");
  const s = await r.json();

  document.getElementById("last-update").textContent = s.last_update || "–";
  const evccBadge = document.getElementById("evcc-badge");
  evccBadge.style.display = s.evcc_online === false ? "inline" : "none";

  // Hero card charging state
  const heroCard = document.getElementById("hero-card");
  const isLaden  = s.action === "laden";
  heroCard.classList.toggle("is-charging", isLaden);

  // Energy flow animation
  document.getElementById("energy-flow").classList.toggle("active", isLaden);

  // Hero icon
  const iconEl = document.getElementById("hero-icon");
  iconEl.className = "hero-status-icon " + (s.action || "idle");
  iconEl.textContent = ACTION_ICONS[s.action] || "⏳";

  // Action label
  const actionEl = document.getElementById("action");
  actionEl.className = "hero-action-label " + (s.action || "idle");
  actionEl.textContent = t("action_" + s.action) || ACTION_LABELS[s.action] || s.action || "–";

  // Grund
  const grundEl = document.getElementById("grund");
  if (s.action === "idle" || !s.grund) { grundEl.style.display = "none"; }
  else { grundEl.style.display = ""; grundEl.textContent = s.grund; }

  // kW display — nur bei aktivem Laden anzeigen, sonst "—"
  const heroKwEl = document.getElementById("hero-kw");
  heroKwEl.classList.toggle("off", !isLaden);
  const kw = isLaden ? (s.charge_power_kw || 0) : 0;
  animateKw(isLaden ? kw : null);

  // Charge progress bar
  const avail  = s.is_after_sunset ? 0 : Math.max(s.available_for_car_kwh || 0, 0);
  const total  = Math.max(avail + (s.charged_today_kwh || 0), s.charged_today_kwh || 0);
  const pct    = total > 0 ? Math.min((s.charged_today_kwh || 0) / total * 100, 100) : 0;
  const barEl  = document.getElementById("hero-charge-bar");
  barEl.style.width = pct + "%";
  barEl.classList.toggle("off", !isLaden && pct === 0);

  document.getElementById("hero-bar-label-l").textContent = fmt(s.charged_today_kwh, "kWh") + " " + t("budget_bar_charged");
  document.getElementById("hero-bar-label-r").textContent = avail > 0 ? fmt(avail, "kWh") + " " + t("budget_bar_available") : (s.is_after_sunset ? t("hero_day_complete") : t("hero_no_budget"));

  // Hero bottom stats
  document.getElementById("car-status").innerHTML = !s.car_connected
    ? '<span class="badge badge-red">' + t("badge_car_disconnected") + '</span>'
    : s.evcc_mode === "minpv"
      ? '<span class="badge badge-green">' + t("badge_charging") + '</span>'
      : '<span class="badge badge-yellow">' + t("badge_connected") + '</span>';

  const modeColors = {minpv:"badge-green", off:"badge-muted", pv:"badge-accent"};
  document.getElementById("evcc-mode").innerHTML =
    '<span class="badge ' + (modeColors[s.evcc_mode] || "badge-yellow") + '">' + s.evcc_mode + '</span>';

  document.getElementById("ziel-strom").textContent = fmt(s.ziel_strom_a, "A", 0);
  document.getElementById("batt-soc").textContent   = fmt(s.batterie_soc, "%", 0);
  document.getElementById("pv-leistung").textContent = fmt(s.pv_leistung_w, "W", 0);

  // Auto-SOC Tile (nur wenn Sensor konfiguriert)
  const autoSocTile = document.getElementById("auto-soc-tile");
  const autoSocVal  = document.getElementById("auto-soc-val");
  if (s.auto_soc != null) {
    autoSocTile.style.display = "";
    autoSocVal.textContent = Math.round(s.auto_soc) + "% / " + (s.auto_ziel_soc || 80) + "%";
  } else {
    autoSocTile.style.display = "none";
  }
  document.getElementById("charged").textContent    = fmt(s.charged_today_kwh, "kWh");

  // Budget Card
  const afterSunset = s.is_after_sunset;
  const rawAvail    = s.budget_verfuegbar_echt_kwh != null ? s.budget_verfuegbar_echt_kwh : (s.budget_verfuegbar_kwh || s.available_for_car_kwh || 0);
  const initBudget  = s.initial_daily_budget_kwh;

  // Tages-Budget (stabil, eingefroren)
  document.getElementById("daily-budget").textContent  = initBudget != null ? initBudget.toFixed(2) + " kWh" : "–";
  document.getElementById("charged-budget").textContent = fmt(s.charged_today_kwh, "kWh");
  document.getElementById("avail-display").textContent  = afterSunset ? "–" : (rawAvail > 0 ? rawAvail.toFixed(2) + " kWh" : "0 kWh");

  // Einspeisung + Noch-offen
  const einsColor = (s.einspeisung_heute_kwh || 0) > 2 ? "var(--yellow)" : "var(--muted)";
  const einspEl   = document.getElementById("einspeisung-heute");
  einspEl.textContent = fmt(s.einspeisung_heute_kwh, "kWh");
  einspEl.style.color = einsColor;

  // Ampel
  const ampelEl = document.getElementById("budget-ampel");
  const ampelColors = {gruen: "var(--green)", gelb: "var(--yellow)", rot: "var(--red)"};
  ampelEl.style.color = ampelColors[s.budget_ampel] || "var(--muted)";
  ampelEl.title = s.budget_ampel === "gruen" ? "Budget sicher" : s.budget_ampel === "gelb" ? "Budget knapp" : "Kein Budget erwartet";

  // Haupt-Anzeige (großer Wert oben)
  const availEl = document.getElementById("available-for-car");
  if (afterSunset) {
    availEl.className = "budget-main-val zero";
    availEl.textContent = "–";
  } else if (rawAvail > 0) {
    availEl.className = "budget-main-val positive";
    availEl.textContent = "+" + rawAvail.toFixed(1) + " kWh";
  } else {
    availEl.className = "budget-main-val no-budget";
    availEl.textContent = "Kein Budget zur Verfügung";
  }

  // Budget-Änderungsgrund
  const bcgEl = document.getElementById("budget-change-grund");
  if (s.budget_change_grund && rawAvail > 0) {
    const isUp = s.budget_change_grund.includes("gestiegen");
    bcgEl.style.color   = isUp ? "var(--green)" : "var(--yellow)";
    bcgEl.textContent   = (isUp ? "↑ " : "↓ ") + s.budget_change_grund;
    bcgEl.style.display = "";
  } else {
    bcgEl.style.display = "none";
  }

  document.getElementById("budget-until").style.display = "none";

  // Info-Zeile: Zusammensetzung des Budget
  document.getElementById("pv-faktor-info").innerHTML =
    'PV Real: <span style="color:var(--text)">' + fmt(s.pv_heute_kwh,"kWh") + '</span>' +
    ' | Rest: <span style="color:var(--muted)">' + fmt(s.pv_forecast_rest_kwh,"kWh") + '</span>' +
    ' | Faktor: <span style="color:var(--muted)">' + ((s.pv_faktor || 1).toFixed(3)) + '</span>' +
    (initBudget != null ? ' | Budget: <span style="color:var(--accent)">' + initBudget.toFixed(1) + ' kWh</span>' : '');

  // Viersegment-Balken (geladen | einspeisung | [verfügbar] | puffer)
  const budgetTotal   = s.initial_daily_budget_kwh || 0;
  const budgetCharged = s.charged_today_kwh || 0;
  const budgetEins    = s.einspeisung_heute_kwh || 0;
  const budgetPuffer  = s.budget_puffer_kwh || 0;
  const budgetAvail   = s.budget_verfuegbar_echt_kwh != null ? s.budget_verfuegbar_echt_kwh : 0;
  if (budgetTotal > 0) {
    document.getElementById("bar-charged").style.width     = Math.min(budgetCharged / budgetTotal * 100, 100).toFixed(1) + "%";
    document.getElementById("bar-einspeisung").style.width = Math.min(budgetEins    / budgetTotal * 100, 100).toFixed(1) + "%";
    document.getElementById("bar-puffer").style.width      = budgetPuffer > 0 ? Math.min(budgetPuffer / budgetTotal * 100, 100).toFixed(1) + "%" : "0%";
  }
  const pufferWrap = document.getElementById("bar-puffer-wrap");
  if (pufferWrap) pufferWrap.style.display = budgetPuffer > 0 ? "" : "none";
  document.getElementById("bar-charged-label").textContent = budgetCharged.toFixed(1) + " kWh";
  document.getElementById("bar-eins-label").textContent    = budgetEins.toFixed(1)    + " kWh";
  document.getElementById("bar-puffer-label").textContent  = budgetPuffer.toFixed(1)  + " kWh";
  document.getElementById("bar-avail-label").textContent   = budgetAvail.toFixed(1)   + " kWh";

  // Budget = 0 ab Sonnenuntergang
  document.getElementById("budget-ende-val").textContent = s.pv_ende_str || "–";

  // Morgen-Vorschau
  const morgenKwh = s.pv_prognose_morgen_kwh || 0;
  const morgenBox = document.getElementById("morgen-box");
  if (morgenKwh > 0.5) {
    morgenBox.style.display = "";
    document.getElementById("morgen-kwh").textContent = morgenKwh.toFixed(1) + " kWh";
    const pv_f = s.pv_faktor || 1;
    const haus  = s.haus_ema_kwh || 10;
    const morgenBudget = Math.max(morgenKwh * pv_f - haus, 0);
    document.getElementById("morgen-budget-text").textContent =
      morgenBudget > 0 ? "→ ca. " + morgenBudget.toFixed(1) + " kWh Budget" : "→ kein Budget erwartet";
  } else {
    morgenBox.style.display = "none";
  }

  // Sensor tiles
  document.getElementById("pv-heute").textContent  = fmt(s.pv_heute_kwh,  "kWh");
  document.getElementById("batt-ziel").textContent = fmt(s.batterie_ziel_soc, "%", 0);
  document.getElementById("haus-real").textContent = fmt(s.haus_real_kwh, "kWh");
  document.getElementById("haus-last").textContent = fmt(s.haus_last_kwh, "kWh");

  // PV Tages-Fortschritt
  const pvReal   = s.pv_heute_kwh || 0;
  const pvEff    = s.pv_forecast_effective_kwh || 0;
  const pvPct    = pvEff > 0 ? Math.min(pvReal / pvEff * 100, 100) : 0;
  const pvColor  = pvPct >= 90 ? "var(--green)" : pvPct >= 50 ? "var(--yellow)" : "var(--accent)";
  document.getElementById("pv-forecast-bar").style.width      = pvPct.toFixed(1) + "%";
  document.getElementById("pv-forecast-bar").style.background = "linear-gradient(90deg," + pvColor + ",#ffdd00)";
  document.getElementById("pv-forecast-label").textContent    = pvReal.toFixed(1) + " / " + pvEff.toFixed(1) + " kWh";
  document.getElementById("pv-forecast-pct").textContent      = pvPct.toFixed(0) + t("pv_forecast_pct_suffix");
  document.getElementById("forecast-updated").textContent     = s.forecast_updated_str ? "🔄 " + s.forecast_updated_str : "";

  // EMA-Tabelle (Montag=0 wie Python weekday())
  const wt       = [t("day_monday"),t("day_tuesday"),t("day_wednesday"),t("day_thursday"),t("day_friday"),t("day_saturday"),t("day_sunday")];
  const emaMap   = s.haus_ema_wochentag || {};
  const todayIdx = (new Date().getDay() + 6) % 7; // 0=Mo … 6=So
  document.querySelector("#ema-table tbody").innerHTML = wt.map((name, i) => {
    const val     = emaMap[String(i)];
    const isToday = i === todayIdx;
    return '<tr style="' + (isToday ? "color:var(--accent);font-weight:600;" : "color:var(--muted);") + '">' +
      '<td>' + (isToday ? "▶ " : "") + name + '</td>' +
      '<td style="text-align:right">' + (val !== undefined ? Number(val).toFixed(1) + " kWh" : "–") + '</td>' +
      (isToday ? '<td style="text-align:right;color:var(--muted);font-size:0.78rem;">' + fmt(s.haus_real_kwh,"kWh") + ' ' + t("today_label") + '</td>' : "<td></td>") +
      '</tr>';
  }).join("");

  const pf      = s.pv_faktor;
  const pfColor = Math.abs(pf - 1.0) < 0.05 ? "var(--green)" : Math.abs(pf - 1.0) < 0.15 ? "var(--yellow)" : "var(--red)";
  document.getElementById("pv-faktor-val").innerHTML =
    '<span style="color:' + pfColor + '">' + (pf !== undefined ? Number(pf).toFixed(3) : "–") + '</span>' +
    '<span style="color:var(--muted);font-size:0.78rem;margin-left:0.4rem;">(' + (pf !== undefined ? (pf*100).toFixed(1)+"%" : "") + ')</span>';

  // Buttons synchronisieren
  updateAktivBtn(s.addon_aktiv !== false);
  updatePauseBtn(!!s.laden_pausiert);
  updateSchnellBtn(!!s.laden_schnell, s.laden_schnell_moeglich !== false);

  // Slider
  const slider = document.getElementById("min-strom-slider");
  if (!slider._dragging) {
    slider.value = s.min_strom_a || 6;
    document.getElementById("min-strom-val").textContent = (s.min_strom_a || 6) + "A";
  }

  // Speicher-Bedarf
  const battNeeds = s.battery_needs_kwh;
  const battSoc   = s.batterie_soc;
  const battZiel  = s.batterie_ziel_soc;
  document.getElementById("batt-needs-val").textContent  = battNeeds != null ? battNeeds.toFixed(2) + " kWh" : "–";
  const battKap = s.batterie_kapazitaet_kwh || 10.2;
  document.getElementById("batt-needs-info").textContent = (battSoc != null && battZiel != null)
    ? "Eingefroren bei WR-Start · Aktuell " + battSoc + "% → Ziel " + battZiel + "% · Live-Bedarf " + (Math.max((battZiel - battSoc) / 100 * battKap, 0)).toFixed(2) + " kWh"
    : "";

  // Ansteck-Deadline
  const connectBox = document.getElementById("connect-box");
  if (!s.car_connected && s.ansteck_deadline) {
    const urgency  = s.ansteck_urgency || "ok";
    const isUrgent = urgency === "urgent";
    const isWarn   = urgency === "warn";
    connectBox.style.display = "block";
    // Blink-Geschwindigkeit: je näher die Deadline, desto schneller (2.0s → 0.5s)
    const mins = (s.ansteck_minutes_left != null) ? s.ansteck_minutes_left : (isUrgent ? 0 : 90);
    const blinkSpeed = isUrgent ? "1.5s" : (Math.max(1.5, Math.min(5.0, mins / 12))).toFixed(1) + "s";
    connectBox.style.setProperty("--blink-speed", blinkSpeed);
    connectBox.className = "info-box connect-blink " + (isUrgent ? "red" : isWarn ? "yellow" : "green");
    const timeEl = document.getElementById("connect-time");
    timeEl.style.color   = isUrgent ? "var(--red)" : isWarn ? "var(--yellow)" : "var(--green)";
    timeEl.textContent   = s.ansteck_deadline;
    document.getElementById("connect-box-label").textContent =
      isUrgent ? t("infobox_connect_urgent") : t("infobox_connect_until");
    document.getElementById("connect-grund").textContent = s.ansteck_grund || "–";
  } else {
    connectBox.style.display = "none";
  }

  // Restzeit
  const restBox = document.getElementById("restzeit-box");
  if (s.action === "laden" && s.remaining_time_min > 0) {
    restBox.style.display = "block";
    document.getElementById("restzeit-gross").textContent   = s.remaining_time_str || "–";
    document.getElementById("restzeit-kwh").textContent     = fmt(s.budget_verfuegbar_kwh != null ? s.budget_verfuegbar_kwh : s.available_for_car_kwh, "", 1);
    document.getElementById("restzeit-kw").textContent      = fmt(s.charge_power_kw, "", 2);
    document.getElementById("restzeit-charged").textContent = fmt(s.charged_today_kwh, "", 1);
    document.getElementById("restzeit-budget").textContent  = fmt(s.budget_at_laden_start, "", 1);
  } else {
    restBox.style.display = "none";
  }
}

// ─── Charts ───────────────────────────────────────────────────────────────────
let chartDays = null, chartEMA = null, chartBudget = null;

async function loadHistory() {
  const r    = await fetch(BASE + "/api/history");
  const data = (await r.json()).reverse();
  const labels = data.map(d => d.datum.slice(5));
  const opts = {
    responsive: true, maintainAspectRatio: false,
    plugins: { legend: { labels: { color: "#5a7a9a", font: { size: 11 } } } },
    scales: {
      x: { ticks: { color: "#3a5a7a", font: { size: 10 } }, grid: { color: "#1e2d47" } },
      y: { ticks: { color: "#3a5a7a", font: { size: 10 } }, grid: { color: "#1e2d47" } }
    }
  };
  if (chartBudget) chartBudget.destroy();
  chartBudget = new Chart(document.getElementById("chartBudget"), {
    type: "bar",
    data: { labels, datasets: [
      { label:t("chart_budget"),  data:data.map(d=>d.budget), backgroundColor:"rgba(255,184,0,.3)",  borderColor:"#ffb800", borderWidth:1, borderRadius:3 },
      { label:t("chart_charged"), data:data.map(d=>d.auto),   backgroundColor:"rgba(0,255,136,.45)", borderColor:"#00ff88", borderWidth:1, borderRadius:3 },
    ]},
    options: { ...opts, scales: {
      x: opts.scales.x,
      y: { ...opts.scales.y, beginAtZero: true,
           title: { display: true, text: "kWh", color: "#3a5a7a", font: { size: 10 } } }
    }}
  });
  if (chartDays) chartDays.destroy();
  chartDays = new Chart(document.getElementById("chartDays"), {
    type: "bar",
    data: { labels, datasets: [
      { label:t("chart_pv_forecast"), data:data.map(d=>d.prognose),       backgroundColor:"rgba(0,212,255,.25)",  borderColor:"#00d4ff", borderWidth:1 },
      { label:t("chart_pv_real"),     data:data.map(d=>d.real),           backgroundColor:"rgba(0,255,136,.25)",  borderColor:"#00ff88", borderWidth:1 },
      { label:t("chart_car_charged"), data:data.map(d=>d.auto),           backgroundColor:"rgba(255,184,0,.5)",   borderColor:"#ffb800", borderWidth:1 },
      { label:t("chart_house"),       data:data.map(d=>d.haus),           backgroundColor:"rgba(90,122,154,.25)", borderColor:"#5a7a9a", borderWidth:1 },
      { label:t("chart_feed_in"),     data:data.map(d=>d.einspeisung||0), backgroundColor:"rgba(255,61,90,.3)",   borderColor:"#ff3d5a", borderWidth:1 },
    ]},
    options: opts
  });
  if (chartEMA) chartEMA.destroy();
  chartEMA = new Chart(document.getElementById("chartEMA"), {
    type: "line",
    data: { labels, datasets: [
      { label:t("chart_house_real"),  data:data.map(d=>d.haus),     borderColor:"#5a7a9a", backgroundColor:"rgba(90,122,154,.1)",  pointRadius:3, tension:0.3 },
      { label:t("chart_ema_learned"),data:data.map(d=>d.haus_ema), borderColor:"#00ff88", backgroundColor:"rgba(0,255,136,.08)",   pointRadius:3, tension:0.4, borderWidth:2 },
    ]},
    options: opts
  });
}

// ─── Log ─────────────────────────────────────────────────────────────────────
let _logData = [], _logVisible = 10;

function renderLog() {
  document.getElementById("log-table").innerHTML = _logData.slice(0, _logVisible).map(row =>
    '<tr>' +
    '<td class="ts">' + row.ts.slice(11,16) + '</td>' +
    '<td>' + fmt(row.budget,"kWh") + '</td>' +
    '<td>' + row.strom_a + 'A</td>' +
    '<td>' + (row.auto ? "✓" : "–") + '</td>' +
    '<td class="action-' + row.action + '">' + (t("action_" + row.action) || row.action) + '</td>' +
    '<td style="color:var(--muted);font-size:0.75rem">' + (row.grund||"").slice(0,60) + '</td>' +
    '</tr>'
  ).join("");
  document.getElementById("log-mehr-btn").style.display = _logVisible < _logData.length ? "inline-block" : "none";
}
function logMehr() { _logVisible += 20; renderLog(); }
async function loadLog() {
  _logData    = await (await fetch(BASE + "/api/log")).json();
  _logVisible = 10;
  renderLog();
}

// ─── Pause ───────────────────────────────────────────────────────────────────
async function resetBatteryNeeds() {
  const btn = document.getElementById("batt-needs-reset-btn");
  const sta = document.getElementById("batt-reset-status");
  btn.disabled = true;
  sta.textContent = t("battery_needs_calculating");
  try {
    const r = await fetch(BASE + "/api/battery_needs_reset", {method:"POST"});
    const d = await r.json();
    if (d.ok) {
      sta.style.color = "var(--green)";
      sta.textContent = "✓ Neu gesetzt: " + d.battery_needs_kwh.toFixed(2) + " kWh (SOC " + d.soc + "% → " + d.ziel_soc + "%)";
    } else {
      sta.style.color = "var(--red)";
      sta.textContent = "Fehler: " + (d.error || "Unbekannt");
    }
  } catch(e) {
    sta.style.color = "var(--red)";
    sta.textContent = t("battery_needs_connection_error");
  }
  btn.disabled = false;
  setTimeout(() => { sta.textContent = ""; sta.style.color = "var(--muted)"; }, 5000);
}

async function toggleAktiv() {
  const btn   = document.getElementById("aktiv-btn");
  const aktiv = btn.dataset.aktiv !== "1";
  updateAktivBtn(aktiv);
  setHeroStatus(aktiv ? "idle" : "schlaf");
  try {
    await fetch(BASE + "/api/aktiv", {method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify({aktiv})});
  } catch(e) { console.error(e); updateAktivBtn(!aktiv); setHeroStatus(!aktiv ? "idle" : "schlaf"); }
}
function updateAktivBtn(aktiv) {
  const btn = document.getElementById("aktiv-btn");
  btn.dataset.aktiv = aktiv ? "1" : "0";
  btn.textContent   = aktiv ? "🤖 Smart aktiv" : "😴 Smart schläft";
  btn.classList.toggle("state-green",  aktiv);
  btn.classList.toggle("state-yellow", !aktiv);
}

async function togglePause() {
  const btn      = document.getElementById("pause-btn");
  const pausiert = btn.dataset.pausiert !== "1";
  updatePauseBtn(pausiert);
  setHeroStatus(pausiert ? "pausiert" : "idle");
  try {
    await fetch(BASE + "/api/pause", {method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify({pausiert})});
  } catch(e) { console.error(e); updatePauseBtn(!pausiert); setHeroStatus(!pausiert ? "pausiert" : "idle"); }
}
function updatePauseBtn(pausiert) {
  const btn = document.getElementById("pause-btn");
  btn.dataset.pausiert = pausiert ? "1" : "0";
  btn.textContent      = pausiert ? "⏸ Laden pausiert" : "▶ Laden bereit";
  btn.classList.toggle("state-green",  !pausiert);
  btn.classList.toggle("state-yellow",  pausiert);
}

async function toggleSchnell() {
  const btn = document.getElementById("schnell-btn");
  if (btn.classList.contains("disabled")) return;
  const aktiv = btn.dataset.aktiv !== "1";
  try {
    await fetch(BASE + "/api/schnell", {method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify({aktiv})});
    updateSchnellBtn(aktiv, btn.dataset.moeglich === "1");
  } catch(e) { console.error(e); }
}
function updateSchnellBtn(aktiv, moeglich) {
  const btn = document.getElementById("schnell-btn");
  btn.dataset.aktiv    = aktiv    ? "1" : "0";
  btn.dataset.moeglich = moeglich ? "1" : "0";
  btn.classList.remove("active", "available", "disabled");
  if (!moeglich) {
    btn.textContent = t("btn_schnell_off");
    btn.classList.add("disabled");
  } else if (aktiv) {
    btn.textContent = t("btn_schnell_on");
    btn.classList.add("active");
  } else {
    btn.textContent = t("btn_schnell");
    btn.classList.add("available");
  }
}

// ─── Slider ──────────────────────────────────────────────────────────────────
(function() {
  const slider = document.getElementById("min-strom-slider");
  const val    = document.getElementById("min-strom-val");
  const status = document.getElementById("strom-status");
  slider.addEventListener("mousedown",  () => slider._dragging = true);
  slider.addEventListener("touchstart", () => slider._dragging = true, {passive:true});
  slider.addEventListener("input",      () => val.textContent = slider.value + "A");
  slider.addEventListener("mouseup",  saveStrom);
  slider.addEventListener("touchend", saveStrom);
  slider.addEventListener("keyup",    saveStrom);
  async function saveStrom() {
    slider._dragging = false;
    const a = parseInt(slider.value);
    val.textContent    = a + "A";
    status.textContent = "Speichern…";
    try {
      const r  = await fetch(BASE + "/api/settings", { method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify({min_strom_a:a}) });
      const ok = (await r.json()).ok;
      status.textContent = ok ? "✓ " + a + "A gespeichert" : "Fehler";
    } catch { status.textContent = "Fehler"; }
    setTimeout(() => status.textContent = "", 2500);
  }
})();

// ─── Config Tab ───────────────────────────────────────────────────────────────
const SENSOREN_DEF_JS = [
  {key:"pv_remaining",   label:"PV verbleibend heute",    desc:"Forecast.Solar — heute noch erwartete PV-Energie (kWh)"},
  {key:"pv_heute_total", label:"PV Prognose heute gesamt", desc:"Forecast.Solar — Tages-Gesamtprognose (kWh)"},
  {key:"pv_morgen",      label:"PV Prognose morgen",       desc:"Forecast.Solar — morgige Gesamtprognose (kWh)"},
  {key:"pv_real",        label:"PV produziert heute real", desc:"Wechselrichter — tatsächlich erzeugte Energie heute (kWh)"},
  {key:"batterie_soc",   label:"Batterie SOC",             desc:"Aktueller Ladestand des Speichers (%)"},
  {key:"pv_leistung",    label:"PV Leistung aktuell",      desc:"Aktuelle PV-Erzeugungsleistung (W)"},
  {key:"haus_last",      label:"Haus Gesamtlast heute",    desc:"Gesamter Hausverbrauch heute inkl. Auto-Laden (kWh)"},
  {key:"grid_power",     label:"Netzleistung",             desc:"Aktuelle Netzleistung (W) — negativ = Einspeisung ins Netz"},
];

let _sensorFieldsBuilt = false;
function buildSensorFields() {
  if (_sensorFieldsBuilt) return;
  _sensorFieldsBuilt = true;
  document.getElementById("sensoren-grid").innerHTML = SENSOREN_DEF_JS.map(s =>
    '<div class="sensor-row">' +
    '<div class="slabel">' + s.label + '</div>' +
    '<div class="sdesc">'  + s.desc  + '</div>' +
    '<div style="display:flex; gap:0.5rem;">' +
    '<input type="text" id="cfg-sensor-' + s.key + '" class="cfg-input mono" placeholder="sensor.entity_id">' +
    '<button class="cfg-test-btn" onclick="openEntitySearch(\'' + s.key + '\')" title="Sensor suchen" style="flex-shrink:0;">🔍</button>' +
    '<button class="cfg-test-btn" onclick="testSensor(\'' + s.key + '\')">Test</button>' +
    '</div>' +
    '<div id="cfg-sensor-result-' + s.key + '" style="font-size:0.78rem; margin-top:0.3rem; min-height:1rem;"></div>' +
    '</div>'
  ).join("");
}

async function loadConfig() {
  try {
    const c = await (await fetch(BASE + "/api/config")).json();
    document.getElementById("cfg-evcc-url").value  = c.evcc_url || "";
    document.getElementById("cfg-batt-kap").value  = c.batterie_kapazitaet_kwh || 9.0;
    document.getElementById("cfg-interval").value  = c.update_interval_min || 5;
    document.getElementById("cfg-haus-verbrauch").value = c.haus_verbrauch_kwh ?? 10.0;

    // Fahrzeug
    const autoSocEl = document.getElementById("cfg-auto-soc");
    if (autoSocEl) autoSocEl.value = c.sensor_auto_soc || "";
    const autoBattEl = document.getElementById("cfg-auto-batt-kwh");
    if (autoBattEl) autoBattEl.value = c.auto_batterie_kwh || 0;
    const autoZielEl = document.getElementById("cfg-auto-ziel-soc");
    if (autoZielEl) {
      autoZielEl.value = c.auto_ziel_soc || 80;
      document.getElementById("cfg-auto-ziel-soc-val").textContent = (c.auto_ziel_soc || 80) + "%";
    }

    const zs = c.batterie_ziel_soc || 100;
    document.getElementById("cfg-ziel-soc").value         = zs;
    document.getElementById("cfg-ziel-soc-val").textContent = zs + "%";

    const ms = c.batterie_min_soc || 15;
    document.getElementById("cfg-min-soc").value          = ms;
    document.getElementById("cfg-min-soc-val").textContent = ms + "%";

    // Loadpoint-Dropdown
    const lpId = c.loadpoint_id || 1;
    const sel  = document.getElementById("cfg-loadpoint-id");
    if (![...sel.options].find(o => parseInt(o.value) === lpId)) {
      sel.innerHTML = '<option value="' + lpId + '">Loadpoint ' + lpId + '</option>';
    }
    sel.value = lpId;

    // Sensoren
    const sens = c.sensoren || {};
    SENSOREN_DEF_JS.forEach(s => {
      const el = document.getElementById("cfg-sensor-" + s.key);
      if (el) el.value = sens[s.key] || "";
    });

    // Puffer + Ampel
    document.getElementById("cfg-budget-puffer").value = c.budget_puffer_kwh ?? 0;
    document.getElementById("cfg-ampel-gruen").value   = c.ampel_gruen_kwh   ?? 0.5;
    document.getElementById("cfg-ampel-gelb").value    = c.ampel_gelb_kwh    ?? -1.0;

    // Prognose-Anbieter
    const provSel = document.getElementById("cfg-forecast-provider");
    if (provSel) { provSel.value = c.forecast_provider || "forecast_solar"; onProviderChange(); }

    // Solcast Direkt
    const apiKeyEl = document.getElementById("cfg-solcast-api-key");
    const resIdEl  = document.getElementById("cfg-solcast-resource-id");
    if (apiKeyEl) apiKeyEl.value = c.solcast_api_key     || "";
    if (resIdEl)  resIdEl.value  = c.solcast_resource_id || "";

    // Sprache
    const langSel = document.getElementById("cfg-language");
    if (langSel) langSel.value = c.language || "auto";
    _activeLangFromConfig = c.language_active || "de";
    applyTranslations(_activeLangFromConfig);

    // Standort
    document.getElementById("cfg-latitude").value = c.latitude ?? 51.0;
    const blSel = document.getElementById("cfg-bundesland");
    if (blSel) blSel.value = c.bundesland || "";

    // Batterie-Toggle
    const hasBattEl = document.getElementById("cfg-has-battery");
    if (hasBattEl) { hasBattEl.checked = c.has_battery !== false; onHasBatteryChange(); }

    // Wallbox-Typ
    const wbTypeSel = document.getElementById("cfg-wallbox-type");
    if (wbTypeSel) { wbTypeSel.value = c.wallbox_type || "evcc"; onWallboxTypeChange(); }
    const wbFields = {
      "cfg-wb-connected": c.wallbox_connected || "",
      "cfg-wb-charging":  c.wallbox_charging  || "",
      "cfg-wb-energy":    c.wallbox_energy    || "",
      "cfg-wb-switch":    c.wallbox_switch    || "",
      "cfg-wb-current":   c.wallbox_current   || "",
    };
    for (const [id, val] of Object.entries(wbFields)) {
      const el = document.getElementById(id);
      if (el) el.value = val;
    }

    // Setup-Banner
    const banner = document.getElementById("setup-banner");
    if (banner) banner.style.display = c.setup_complete ? "none" : "flex";

    // Benachrichtigungen
    document.getElementById("cfg-notify-target").value          = c.notify_target        || "";
    document.getElementById("cfg-notify-budget-low").checked    = !!c.notify_budget_low;
    document.getElementById("cfg-notify-budget-kwh").value      = c.notify_budget_low_kwh ?? 0.5;
    document.getElementById("cfg-notify-deadline").checked      = !!c.notify_deadline_urgent;
    document.getElementById("cfg-notify-laden-fertig").checked  = !!c.notify_laden_fertig;
  } catch(e) { console.error("loadConfig:", e); }
}

// Hinweistext + Defaults je nach gewähltem Anbieter
function getProviderHints() {
  return {
    forecast_solar: t("hint_forecast_solar"),
    solcast:        t("hint_solcast_hacs"),
    solcast_direct: t("hint_solcast_direct"),
  };
}
const SOLCAST_DEFAULTS = {
  pv_remaining:   "sensor.solcast_pv_forecast_prognose_verbleibende_leistung_heute",
  pv_heute_total: "sensor.solcast_pv_forecast_prognose_heute",
  pv_morgen:      "sensor.solcast_pv_forecast_prognose_morgen",
};
const FORECAST_SOLAR_DEFAULTS = {
  pv_remaining:   "sensor.energy_production_today_remaining",
  pv_heute_total: "sensor.energy_production_today",
  pv_morgen:      "sensor.energy_production_tomorrow",
};

function onProviderChange() {
  const v          = document.getElementById("cfg-forecast-provider").value;
  const hint       = document.getElementById("provider-hint");
  const directFlds = document.getElementById("solcast-direct-fields");
  const sensorCard = document.getElementById("sensoren-card");
  const sensorBtn  = document.getElementById("provider-sensor-btn");
  const isDirect   = v === "solcast_direct";
  if (hint)       hint.textContent          = getProviderHints()[v] || "";
  if (directFlds) directFlds.style.display  = isDirect ? "" : "none";
  if (sensorCard) sensorCard.style.display  = isDirect ? "none" : "";
  if (sensorBtn)  sensorBtn.style.display   = isDirect ? "none" : "";
}

// WR-Hersteller Sensor-Defaults (WR-spezifische Sensoren: pv_real, batterie_soc, pv_leistung, haus_last, grid_power)
const WR_DEFAULTS = {
  growatt: {
    pv_real:      "sensor.growatt_today_s_solar_energy",
    batterie_soc: "sensor.growatt_battery_soc",
    pv_leistung:  "sensor.growatt_pv_power_total",
    haus_last:    "sensor.growatt_today_s_yield",
    grid_power:   "sensor.grid_power_evcc",
  },
  fronius: {
    pv_real:      "sensor.fronius_inverter_energy_day",
    batterie_soc: "sensor.fronius_battery_state_of_charge",
    pv_leistung:  "sensor.fronius_inverter_ac_power",
    haus_last:    "sensor.fronius_meter_energy_consumed_day",
    grid_power:   "sensor.fronius_meter_power",
  },
  sma: {
    pv_real:      "sensor.sma_pv_daily_yield",
    batterie_soc: "sensor.sma_battery_soc",
    pv_leistung:  "sensor.sma_pv_power",
    haus_last:    "sensor.sma_daily_consumption",
    grid_power:   "sensor.sma_grid_power",
  },
  huawei: {
    pv_real:      "sensor.inverter_daily_yield_energy",
    batterie_soc: "sensor.battery_state_of_capacity",
    pv_leistung:  "sensor.inverter_input_power",
    haus_last:    "sensor.power_meter_daily_imported_energy",
    grid_power:   "sensor.power_meter_active_power",
  },
  solaredge: {
    pv_real:      "sensor.solaredge_energy_today",
    batterie_soc: "sensor.solaredge_storage_level_of_energy",
    pv_leistung:  "sensor.solaredge_current_power",
    haus_last:    "sensor.solaredge_imported_today",
    grid_power:   "sensor.solaredge_grid_power",
  },
  kostal: {
    pv_real:      "sensor.kostal_plenticore_energy_pv_total_today",
    batterie_soc: "sensor.kostal_plenticore_battery_soc",
    pv_leistung:  "sensor.kostal_plenticore_pv_power",
    haus_last:    "sensor.kostal_plenticore_energy_home_total_today",
    grid_power:   "sensor.kostal_plenticore_grid_power_current",
  },
  e3dc: {
    pv_real:      "sensor.e3dc_solar_energy_day",
    batterie_soc: "sensor.e3dc_battery_soc",
    pv_leistung:  "sensor.e3dc_solar_power",
    haus_last:    "sensor.e3dc_home_energy_day",
    grid_power:   "sensor.e3dc_grid_power",
  },
  enphase: {
    pv_real:      "sensor.enphase_today_s_energy_production",
    batterie_soc: "sensor.enphase_battery_state_of_charge",
    pv_leistung:  "sensor.enphase_current_power_production",
    haus_last:    "sensor.enphase_today_s_energy_consumption",
    grid_power:   "sensor.enphase_grid_power",
  },
};

function fillWrDefaults() {
  const v    = document.getElementById("cfg-wr-provider").value;
  const defs = WR_DEFAULTS[v];
  if (!defs) { return; }
  for (const [key, val] of Object.entries(defs)) {
    const el = document.getElementById("cfg-sensor-" + key);
    if (el) el.value = val;
  }
  document.getElementById("cfg-save-result").innerHTML =
    '<span style="color:var(--accent)">' + t("wr_ids_filled") + '</span>';
  setTimeout(() => document.getElementById("cfg-save-result").innerHTML = "", 4000);
}

function fillProviderDefaults() {
  const v = document.getElementById("cfg-forecast-provider").value;
  const defs = v === "solcast" ? SOLCAST_DEFAULTS : FORECAST_SOLAR_DEFAULTS;
  for (const [key, val] of Object.entries(defs)) {
    const el = document.getElementById("cfg-sensor-" + key);
    if (el) el.value = val;
  }
  document.getElementById("cfg-save-result").innerHTML =
    '<span style="color:var(--accent)">' + t("sensor_ids_filled") + '</span>';
  setTimeout(() => document.getElementById("cfg-save-result").innerHTML = "", 4000);
}

// ─── Config Export / Import ───────────────────────────────────────────────────
function exportConfig() {
  window.location.href = BASE + "/api/config/export";
}

async function importConfig(input) {
  const file = input.files[0];
  if (!file) return;
  const resultEl = document.getElementById("backup-result");
  resultEl.innerHTML = '<span style="color:var(--muted)">Importiere…</span>';
  try {
    const text = await file.text();
    const json = JSON.parse(text);
    const r    = await fetch(BASE + "/api/config/import", {
      method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(json)
    });
    const d = await r.json();
    if (d.ok) {
      resultEl.innerHTML = '<span style="color:var(--green)">✓ Import erfolgreich — Seite wird neu geladen…</span>';
      setTimeout(() => location.reload(), 1500);
    } else {
      resultEl.innerHTML = '<span style="color:var(--red)">✗ ' + (d.error || "Fehler") + '</span>';
    }
  } catch(e) {
    resultEl.innerHTML = '<span style="color:var(--red)">✗ Ungültige Datei</span>';
  }
  input.value = "";
  setTimeout(() => resultEl.innerHTML = "", 8000);
}

// ─── Entity Search ────────────────────────────────────────────────────────────
let _entityCache   = null;
let _entityTarget  = null;   // welches sensor-input wird befüllt

async function openEntitySearch(key) {
  _entityTarget = key;
  const modal   = document.getElementById("entity-modal");
  const input   = document.getElementById("entity-search-input");
  modal.classList.add("open");
  input.value = "";
  input.focus();
  if (!_entityCache) {
    document.getElementById("entity-results").innerHTML =
      '<div id="entity-loading" style="padding:1.5rem;text-align:center;color:var(--muted);">Lade Entities…</div>';
    try {
      const r = await fetch(BASE + "/api/entities");
      _entityCache = await r.json();
    } catch(e) {
      _entityCache = [];
    }
  }
  filterEntities("");
}

function closeEntitySearch() {
  document.getElementById("entity-modal").classList.remove("open");
  _entityTarget = null;
}

function filterEntities(query) {
  if (!_entityCache) return;
  const q    = query.toLowerCase().trim();
  const list = q
    ? _entityCache.filter(e =>
        e.entity_id.toLowerCase().includes(q) ||
        e.name.toLowerCase().includes(q))
    : _entityCache;
  const top  = list.slice(0, 120);
  document.getElementById("entity-results").innerHTML = top.length
    ? top.map(e =>
        '<div class="entity-item" onclick="selectEntity(\'' + e.entity_id + '\')">' +
        '<span class="entity-id">' + e.entity_id + '</span>' +
        '<span class="entity-state">' + (e.state || "–") + (e.unit ? "\u00a0" + e.unit : "") + '</span>' +
        '<span class="entity-name">' + e.name + '</span>' +
        '</div>').join("")
    : '<div style="padding:1.5rem;text-align:center;color:var(--muted);">Keine Ergebnisse</div>';
}

function selectEntity(entityId) {
  if (_entityTarget) {
    const el = document.getElementById("cfg-sensor-" + _entityTarget);
    if (el) el.value = entityId;
  }
  closeEntitySearch();
}

// ESC schließt Modal
document.addEventListener("keydown", e => { if (e.key === "Escape") closeEntitySearch(); });

async function testNotify() {
  const target    = document.getElementById("cfg-notify-target").value.trim();
  const resultEl  = document.getElementById("notify-test-result");
  if (!target) { resultEl.innerHTML = '<span style="color:var(--yellow)">⚠ Bitte zuerst Target eingeben</span>'; return; }
  resultEl.innerHTML = '<span style="color:var(--muted)">Sende Test…</span>';
  try {
    const d = await (await fetch(BASE + "/api/test/notify", {
      method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify({target})
    })).json();
    resultEl.innerHTML = d.ok
      ? '<span style="color:var(--green)">✓ Benachrichtigung gesendet!</span>'
      : '<span style="color:var(--red)">✗ ' + (d.error || "Fehler") + '</span>';
  } catch(e) { resultEl.innerHTML = '<span style="color:var(--red)">✗ Verbindungsfehler</span>'; }
  setTimeout(() => resultEl.innerHTML = "", 6000);
}

async function testEvcc() {
  const url      = document.getElementById("cfg-evcc-url").value.trim();
  const resultEl = document.getElementById("evcc-test-result");
  resultEl.innerHTML = '<span style="color:var(--muted)">' + t("evcc_testing") + '</span>';
  try {
    const d = await (await fetch(BASE + "/api/test/evcc?url=" + encodeURIComponent(url))).json();
    if (d.ok) {
      resultEl.innerHTML = '<span style="color:var(--green)">✓ Verbunden — ' + d.loadpoints.length + ' Loadpoint(s) gefunden</span>';
      const sel = document.getElementById("cfg-loadpoint-id");
      const cur = parseInt(sel.value) || 1;
      sel.innerHTML = d.loadpoints.map(lp =>
        '<option value="' + lp.id + '"' + (lp.id === cur ? " selected" : "") + '>' + lp.title + '</option>'
      ).join("");
    } else {
      resultEl.innerHTML = '<span style="color:var(--red)">✗ ' + d.error + '</span>';
    }
  } catch(e) {
    resultEl.innerHTML = '<span style="color:var(--red)">✗ ' + t("evcc_connection_error") + ' ' + e.message + '</span>';
  }
}

async function testSensor(key) {
  const el       = document.getElementById("cfg-sensor-" + key);
  const resultEl = document.getElementById("cfg-sensor-result-" + key);
  const entityId = el ? el.value.trim() : "";
  if (!entityId) { resultEl.textContent = ""; return; }
  resultEl.innerHTML = '<span style="color:var(--muted)">…</span>';
  try {
    const d = await (await fetch(BASE + "/api/test/sensor?entity_id=" + encodeURIComponent(entityId))).json();
    if (d.ok) {
      resultEl.innerHTML = '<span style="color:var(--green)">✓ ' + d.value + (d.unit ? " " + d.unit : "") + '</span>';
    } else {
      resultEl.innerHTML = '<span style="color:var(--red)">✗ ' + d.error + '</span>';
    }
  } catch { resultEl.innerHTML = '<span style="color:var(--red)">✗ Fehler</span>'; }
}

async function testAllSensors() {
  for (const s of SENSOREN_DEF_JS) await testSensor(s.key);
}

async function saveConfig() {
  const sensoren = {};
  SENSOREN_DEF_JS.forEach(s => {
    const el = document.getElementById("cfg-sensor-" + s.key);
    if (el && el.value.trim()) sensoren[s.key] = el.value.trim();
  });
  const cfg = {
    evcc_url:                document.getElementById("cfg-evcc-url").value.trim(),
    loadpoint_id:            parseInt(document.getElementById("cfg-loadpoint-id").value) || 1,
    wallbox_type:            document.getElementById("cfg-wallbox-type")?.value || "evcc",
    wallbox_connected:       (document.getElementById("cfg-wb-connected") || {}).value?.trim() || "",
    wallbox_charging:        (document.getElementById("cfg-wb-charging")  || {}).value?.trim() || "",
    wallbox_energy:          (document.getElementById("cfg-wb-energy")    || {}).value?.trim() || "",
    wallbox_switch:          (document.getElementById("cfg-wb-switch")    || {}).value?.trim() || "",
    wallbox_current:         (document.getElementById("cfg-wb-current")   || {}).value?.trim() || "",
    batterie_kapazitaet_kwh: parseFloat(document.getElementById("cfg-batt-kap").value) || 9.0,
    batterie_ziel_soc:       parseInt(document.getElementById("cfg-ziel-soc").value) || 100,
    batterie_min_soc:        parseInt(document.getElementById("cfg-min-soc").value) || 15,
    update_interval_min:     parseInt(document.getElementById("cfg-interval").value) || 5,
    haus_verbrauch_kwh:      parseFloat(document.getElementById("cfg-haus-verbrauch").value) || 10.0,
    sensor_auto_soc:         (document.getElementById("cfg-auto-soc")       || {}).value?.trim() || "",
    auto_batterie_kwh:       parseFloat((document.getElementById("cfg-auto-batt-kwh") || {}).value) || 0,
    auto_ziel_soc:           parseInt((document.getElementById("cfg-auto-ziel-soc")  || {}).value) || 80,
    budget_puffer_kwh:       parseFloat(document.getElementById("cfg-budget-puffer").value) || 0,
    ampel_gruen_kwh:         parseFloat(document.getElementById("cfg-ampel-gruen").value) ?? 0.5,
    ampel_gelb_kwh:          parseFloat(document.getElementById("cfg-ampel-gelb").value) ?? -1.0,
    forecast_provider:       document.getElementById("cfg-forecast-provider").value || "forecast_solar",
    solcast_api_key:         (document.getElementById("cfg-solcast-api-key")     || {}).value?.trim() || "",
    solcast_resource_id:     (document.getElementById("cfg-solcast-resource-id") || {}).value?.trim() || "",
    language:                document.getElementById("cfg-language")?.value || "auto",
    latitude:                parseFloat(document.getElementById("cfg-latitude").value) || 51.0,
    bundesland:              document.getElementById("cfg-bundesland")?.value || "",
    has_battery:             document.getElementById("cfg-has-battery")?.checked ?? true,
    notify_target:           document.getElementById("cfg-notify-target").value.trim(),
    notify_budget_low:       document.getElementById("cfg-notify-budget-low").checked,
    notify_budget_low_kwh:   parseFloat(document.getElementById("cfg-notify-budget-kwh").value) || 0.5,
    notify_deadline_urgent:  document.getElementById("cfg-notify-deadline").checked,
    notify_laden_fertig:     document.getElementById("cfg-notify-laden-fertig").checked,
    sensoren,
  };
  const resultEl = document.getElementById("cfg-save-result");
  resultEl.innerHTML = '<span style="color:var(--muted)">' + t("config_saving") + '</span>';
  try {
    const d = await (await fetch(BASE + "/api/config", {
      method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify(cfg)
    })).json();
    if (d.ok) {
      resultEl.innerHTML = '<span style="color:var(--green)">' + t("config_save_success") + '</span>';
    } else {
      resultEl.innerHTML = '<span style="color:var(--red)">✗ ' + (d.error || "Unbekannter Fehler") + '</span>';
    }
  } catch { resultEl.innerHTML = '<span style="color:var(--red)">' + t("config_connection_error") + '</span>'; }
  setTimeout(() => resultEl.innerHTML = "", 5000);
}

// ─── Debug ────────────────────────────────────────────────────────────────────
let _debugMode = false;
let _debugInterval = null;

const CAT_COLORS = {
  delta:    "var(--yellow)",
  freeze:   "var(--blue, #60a5fa)",
  decision: "var(--text)",
  action:   "var(--green)",
  info:     "var(--muted)",
};

function loadDebugState() {
  fetch(BASE + "/api/state").then(r => r.json()).then(s => {
    _debugMode = s.debug_mode || false;
    applyDebugToggle();
    if (_debugMode) {
      refreshDebugLog();
      if (!_debugInterval) {
        _debugInterval = setInterval(refreshDebugLog, 10000);
      }
    }
  });
}

function applyDebugToggle() {
  const toggle = document.getElementById("debug-toggle");
  const knob   = document.getElementById("debug-knob");
  const label  = document.getElementById("debug-mode-label");
  if (!toggle) return;
  toggle.style.background = _debugMode ? "var(--green)" : "var(--border)";
  knob.style.left          = _debugMode ? "25px" : "3px";
  label.textContent        = _debugMode ? t("debug_on") : t("debug_off");
  label.style.color        = _debugMode ? "var(--green)" : "var(--muted)";
}

function toggleDebugMode() {
  _debugMode = !_debugMode;
  applyDebugToggle();
  fetch(BASE + "/api/settings", {method:"POST", headers:{"Content-Type":"application/json"},
    body: JSON.stringify({debug_mode: _debugMode})});
  if (_debugMode) {
    refreshDebugLog();
    if (!_debugInterval) {
      _debugInterval = setInterval(refreshDebugLog, 10000);
    }
  } else {
    clearInterval(_debugInterval);
    _debugInterval = null;
  }
}

function clearDebugLog() {
  document.getElementById("debug-log").innerHTML =
    '<span style="color:var(--border);">' + t("debug_log_cleared") + '</span>';
}

function refreshDebugLog() {
  if (!_debugMode) return;
  fetch(BASE + "/api/debug").then(r => r.json()).then(entries => {
    const el = document.getElementById("debug-log");
    if (!entries.length) {
      el.innerHTML = '<span style="color:var(--border);">' + t("debug_no_entries") + '</span>';
      return;
    }
    el.innerHTML = entries.slice().reverse().map(e => {
      const color = CAT_COLORS[e.cat] || "var(--muted)";
      const ts    = `<span style="color:var(--border);user-select:none;">${e.ts} </span>`;
      const msg   = e.msg.replace(/(-?\d+\.?\d*) kWh/g, '<span style="color:var(--text);">$1 kWh</span>')
                         .replace(/(-?\d+\.?\d*)%/g,    '<span style="color:var(--text);">$1%</span>')
                         .replace(/(-?\d+\.?\d*) W/g,   '<span style="color:var(--text);">$1 W</span>');
      return `<div style="color:${color};border-bottom:1px solid var(--border);padding:2px 0;">${ts}${msg}</div>`;
    }).join("");
    el.scrollTop = 0;
  });
}

// ─── Init ─────────────────────────────────────────────────────────────────────
async function initLanguage() {
  try {
    const c = await (await fetch(BASE + "/api/config")).json();
    _activeLangFromConfig = c.language_active || "de";
    applyTranslations(_activeLangFromConfig);
  } catch(e) {}
}

async function refresh() { await Promise.all([loadState(), loadLog()]); }

// ─── Collapsible Cards ────────────────────────────────────────────────────────
function initCollapsibles() {
  document.querySelectorAll(".card-title.collapsible").forEach(title => {
    const id = title.dataset.body;
    if (!id) return;
    const body = document.getElementById(id);
    if (!body) return;
    // Gespeicherten Zustand wiederherstellen
    if (localStorage.getItem("collapsed_" + id) === "1") {
      body.classList.add("collapsed");
      title.classList.add("collapsed");
    }
    title.addEventListener("click", () => {
      const nowCollapsed = body.classList.toggle("collapsed");
      title.classList.toggle("collapsed", nowCollapsed);
      localStorage.setItem("collapsed_" + id, nowCollapsed ? "1" : "0");
      // Chart.js nach Aufklappen neu rendern
      if (!nowCollapsed && body.querySelector("canvas")) {
        setTimeout(() => window.dispatchEvent(new Event("resize")), 50);
      }
    });
  });
}

initLanguage();
initCollapsibles();
loadHistory();
refresh();
setInterval(refresh, 60000);
setInterval(loadHistory, 300000);
</script>
</body>
</html>"""

# ---------------------------------------------------------------------------
# Flask App & Routen
# ---------------------------------------------------------------------------

app = Flask(__name__)


@app.route("/")
def index():
    return render_template_string(TEMPLATE)


@app.route("/health")
def api_health():
    """Liveness-Check: gibt 200 OK zurück solange Flask läuft."""
    last = state.get("last_update", "–")
    return jsonify({"ok": True, "last_update": last})


@app.route("/api/state")
def api_state():
    return jsonify(state)


@app.route("/api/history")
def api_history():
    return jsonify(db_history_days(14))


@app.route("/api/log")
def api_log():
    return jsonify(db_control_log(100))


@app.route("/api/debug")
def api_debug():
    return jsonify(_debug_buffer[-200:])


@app.route("/api/settings", methods=["POST"])
def api_settings():
    data = request.get_json(force=True)
    if "min_strom_a" in data:
        val = max(6, min(16, int(data["min_strom_a"])))
        user_settings["min_strom_a"] = val
        save_settings(user_settings)
        log.info(f"Mindeststrom → {val}A")
    if "debug_mode" in data:
        user_settings["debug_mode"] = bool(data["debug_mode"])
        save_settings(user_settings)
        log.info(f"Debug-Modus → {'AN' if user_settings['debug_mode'] else 'AUS'}")
        if user_settings["debug_mode"]:
            _debug_buffer.clear()
            _debug_prev.clear()
    return jsonify({"ok": True})



@app.route("/api/battery_needs_reset", methods=["POST"])
def api_battery_needs_reset():
    global _daily_budget
    batt_soc  = state.get("batterie_soc")
    ziel_soc  = user_settings.get("batterie_ziel_soc", 100)
    batt_kap  = get_batt_kap()
    if batt_soc is None:
        return jsonify({"ok": False, "error": "Kein Batterie-SOC verfügbar"})
    new_batt_needs = round(max((ziel_soc - batt_soc) / 100 * batt_kap, 0), 3)
    _daily_budget["battery_needs_initial"] = new_batt_needs
    # Tages-Budget neu berechnen (analog Modul 1)
    pv_faktor      = float(user_settings.get("pv_faktor", 1.0))
    pv_prognose    = state.get("pv_prognose_heute_kwh") or 0.0
    haus_ema_val   = state.get("haus_ema_kwh") or 0.0
    daylight_h, _  = _daylight_params()
    haus_pv_anteil = round(haus_ema_val * (daylight_h / 24), 3)
    new_budget     = round(max(pv_prognose * pv_faktor - haus_pv_anteil - new_batt_needs, 0), 2)
    _daily_budget["initial_daily_budget"] = new_budget
    _daily_budget["pv_prognose_kwh"]      = round(pv_prognose, 2)
    _save_daily_budget(_daily_budget)
    log.info(f"Speicher-Bedarf manuell neu gesetzt: {new_batt_needs:.2f} kWh → Budget neu: {new_budget:.2f} kWh")
    # State sofort aktualisieren damit UI beim nächsten Poll neue Werte sieht
    charged = state.get("charged_today_kwh") or 0.0
    new_avail = round(max(new_budget - charged, 0), 2)
    state["battery_needs_kwh"]         = new_batt_needs
    state["initial_daily_budget_kwh"]  = new_budget
    state["daily_budget_kwh"]          = new_budget
    state["budget_verfuegbar_kwh"]     = new_avail
    state["available_for_car_kwh"]     = new_avail
    state["budget_kwh"]                = new_avail
    return jsonify({"ok": True, "battery_needs_kwh": new_batt_needs, "initial_daily_budget_kwh": new_budget, "soc": batt_soc, "ziel_soc": ziel_soc})


@app.route("/api/aktiv", methods=["POST"])
def api_aktiv():
    data  = request.get_json(force=True)
    aktiv = bool(data.get("aktiv", True))
    user_settings["addon_aktiv"] = aktiv
    save_settings(user_settings)
    log.info(f"Add-on: {'aktiviert' if aktiv else 'Schlaf-Modus'}")
    return jsonify({"ok": True, "addon_aktiv": aktiv})


@app.route("/api/pause", methods=["POST"])
def api_pause():
    data    = request.get_json(force=True)
    pausiert = bool(data.get("pausiert", False))
    state["laden_pausiert"] = pausiert
    # Pause-State auf Disk persistieren — überlebt Neustarts
    _daily_budget["laden_pausiert"] = pausiert
    _save_daily_budget(_daily_budget)
    log.info(f"Laden: {'pausiert' if pausiert else 'fortgesetzt'}")
    return jsonify({"ok": True, "laden_pausiert": pausiert})


@app.route("/api/schnell", methods=["POST"])
def api_schnell():
    """Modul 5: Budget-schnell umschalten — now-Modus + Schnell-Regler-Thread."""
    data  = request.get_json(force=True)
    aktiv = bool(data.get("aktiv", False))
    state["laden_schnell"] = aktiv
    log.info(f"Budget-schnell: {'aktiviert' if aktiv else 'deaktiviert'}")
    if aktiv:
        if state.get("car_connected"):
            evcc_set_mode("now")   # Sofort umschalten, nicht auf Main-Loop warten
        start_schnell_regler()
    else:
        evcc_set_maxcurrent(16)    # maxcurrent zurücksetzen
    return jsonify({"ok": True, "laden_schnell": aktiv})


@app.route("/api/config")
def api_config_get():
    return jsonify({
        "evcc_url":                user_settings.get("evcc_url", ""),
        "loadpoint_id":            user_settings.get("loadpoint_id", 1),
        "wallbox_type":      user_settings.get("wallbox_type",      "evcc"),
        "wallbox_connected": user_settings.get("wallbox_connected", ""),
        "wallbox_charging":  user_settings.get("wallbox_charging",  ""),
        "wallbox_energy":    user_settings.get("wallbox_energy",    ""),
        "wallbox_switch":    user_settings.get("wallbox_switch",    ""),
        "wallbox_current":   user_settings.get("wallbox_current",   ""),
        "has_battery":             user_settings.get("has_battery", True),
        "batterie_kapazitaet_kwh": user_settings.get("batterie_kapazitaet_kwh", 9.0),
        "batterie_min_soc":        user_settings.get("batterie_min_soc", 15),
        "batterie_ziel_soc":       user_settings.get("batterie_ziel_soc", 100),
        "update_interval_min":     user_settings.get("update_interval_min", 5),
        "haus_verbrauch_kwh":      user_settings.get("haus_verbrauch_kwh", 10.0),
        "sensor_auto_soc":         user_settings.get("sensor_auto_soc",   ""),
        "auto_batterie_kwh":       user_settings.get("auto_batterie_kwh", 0.0),
        "auto_ziel_soc":           user_settings.get("auto_ziel_soc",     80),
        "ampel_gruen_kwh":         user_settings.get("ampel_gruen_kwh", 0.5),
        "ampel_gelb_kwh":          user_settings.get("ampel_gelb_kwh", -1.0),
        "forecast_provider":       user_settings.get("forecast_provider", "forecast_solar"),
        "solcast_api_key":         user_settings.get("solcast_api_key",     ""),
        "solcast_resource_id":     user_settings.get("solcast_resource_id", ""),
        "budget_puffer_kwh":       user_settings.get("budget_puffer_kwh",   0.0),
        "latitude":                user_settings.get("latitude",   LATITUDE_DEG),
        "bundesland":              user_settings.get("bundesland", ""),
        "language":                user_settings.get("language",   "auto"),
        "setup_complete":          get_evcc_url() != "http://localhost:7070" and bool(user_settings.get("sensoren")),
        "language_active":         get_ha_language() if user_settings.get("language","auto") == "auto" else user_settings.get("language","de"),
        "sensoren":                user_settings.get("sensoren", {}),
        # Benachrichtigungen
        "notify_target":           user_settings.get("notify_target",          ""),
        "notify_budget_low":       user_settings.get("notify_budget_low",      False),
        "notify_budget_low_kwh":   user_settings.get("notify_budget_low_kwh",  0.5),
        "notify_deadline_urgent":  user_settings.get("notify_deadline_urgent", False),
        "notify_laden_fertig":     user_settings.get("notify_laden_fertig",    False),
    })


@app.route("/api/config/export")
def api_config_export():
    """Liefert die vollständige user_settings.json als Download."""
    data = json.dumps(user_settings, indent=2, ensure_ascii=False)
    return Response(
        data,
        mimetype="application/json",
        headers={"Content-Disposition": 'attachment; filename="smart_ev_charger_config.json"'}
    )


@app.route("/api/config/import", methods=["POST"])
def api_config_import():
    """Importiert eine user_settings.json — überschreibt alle Felder außer internen EMA-Daten."""
    try:
        imported = request.get_json(force=True)
        if not isinstance(imported, dict):
            return jsonify({"ok": False, "error": "Ungültiges Format — JSON-Objekt erwartet"})
        # Interne Lernfelder schützen: werden aus aktuellen Settings übernommen wenn im Import fehlen
        protected = ["haus_ema_wochentag", "batt_fill_rate_wochentag", "abend_entnahme_wochentag", "pv_faktor"]
        for key in protected:
            if key not in imported and key in user_settings:
                imported[key] = user_settings[key]
        user_settings.clear()
        user_settings.update(imported)
        save_settings(user_settings)
        log.info("Config importiert via UI")
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)})


@app.route("/api/config", methods=["POST"])
def api_config_save():
    data = request.get_json(force=True)
    # Skalare Felder mit Typ-Koersion
    scalar_map = {
        "evcc_url":                str,
        "loadpoint_id":            int,
        "batterie_kapazitaet_kwh": float,
        "batterie_min_soc":        int,
        "batterie_ziel_soc":       int,
        "update_interval_min":     int,
        "ampel_gruen_kwh":         float,
        "ampel_gelb_kwh":          float,
        "forecast_provider":       str,
        "solcast_api_key":         str,
        "solcast_resource_id":     str,
        "budget_puffer_kwh":       float,
        "latitude":                float,
        "bundesland":              str,
        "language":                str,
        # Lernwerte
        "haus_verbrauch_kwh":      float,
        # Fahrzeug
        "sensor_auto_soc":         str,
        "auto_batterie_kwh":       float,
        "auto_ziel_soc":           int,
        # Benachrichtigungen
        "notify_target":           str,
        "notify_budget_low_kwh":   float,
        # Wallbox
        "wallbox_type":            str,
        "wallbox_connected":       str,
        "wallbox_charging":        str,
        "wallbox_energy":          str,
        "wallbox_switch":          str,
        "wallbox_current":         str,
    }
    bool_fields = ["has_battery", "notify_budget_low", "notify_deadline_urgent", "notify_laden_fertig"]
    for key in bool_fields:
        if key in data:
            user_settings[key] = bool(data[key])
    old_haus_verbrauch = user_settings.get("haus_verbrauch_kwh", 10.0)
    for key, cast in scalar_map.items():
        if key in data:
            try:
                user_settings[key] = cast(data[key])
            except (ValueError, TypeError):
                pass
    # EMA zurücksetzen wenn Startwert geändert wurde
    new_haus_verbrauch = user_settings.get("haus_verbrauch_kwh", 10.0)
    if abs(new_haus_verbrauch - old_haus_verbrauch) > 0.05:
        user_settings["haus_ema_wochentag"] = {str(i): new_haus_verbrauch for i in range(7)}
        log.info(f"Haus-EMA zurückgesetzt auf {new_haus_verbrauch} kWh (Startwert geändert)")
    # Sensoren
    if "sensoren" in data and isinstance(data["sensoren"], dict):
        if "sensoren" not in user_settings:
            user_settings["sensoren"] = {}
        for k, v in data["sensoren"].items():
            if k in SENSOREN_DEFAULTS and isinstance(v, str):
                user_settings["sensoren"][k] = v.strip()
    save_settings(user_settings)
    log.info("Konfiguration gespeichert via UI")
    return jsonify({"ok": True})


@app.route("/api/test/notify", methods=["POST"])
def api_test_notify():
    """Sendet eine Test-Benachrichtigung an den konfigurierten Target."""
    data   = request.get_json(force=True)
    target = data.get("target", "").strip()
    if not target:
        return jsonify({"ok": False, "error": "Kein Target angegeben"})
    old_target = user_settings.get("notify_target", "")
    user_settings["notify_target"] = target
    ok = ha_notify("🔔 Smart EV Charger", "Test-Benachrichtigung erfolgreich!")
    user_settings["notify_target"] = old_target
    return jsonify({"ok": ok, "error": "" if ok else "Benachrichtigung fehlgeschlagen — Target korrekt?"})


@app.route("/api/test/evcc")
def api_test_evcc():
    url = request.args.get("url", get_evcc_url()).strip()
    try:
        r   = requests.get(f"{url}/api/state", timeout=8)
        lps = r.json().get("loadpoints", [])
        return jsonify({
            "ok": True,
            "loadpoints": [
                {"id": i + 1, "title": lp.get("title") or f"Loadpoint {i + 1}"}
                for i, lp in enumerate(lps)
            ],
        })
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)})


_entities_cache: dict = {"ts": 0, "data": []}

@app.route("/api/entities")
def api_entities():
    """Gibt alle HA-Entities zurück (sensor.*, number.*, input_number.*) — gecacht 60s."""
    now = time.time()
    if now - _entities_cache["ts"] < 60 and _entities_cache["data"]:
        return jsonify(_entities_cache["data"])
    try:
        r = requests.get(get_ha_api_url().rstrip("/") + "/states",
                         headers=get_ha_headers(), timeout=10)
        if r.status_code != 200:
            return jsonify([])
        allowed = ("sensor.", "number.", "input_number.")
        result = sorted([
            {
                "entity_id": e["entity_id"],
                "state":     e.get("state", ""),
                "name":      e.get("attributes", {}).get("friendly_name", e["entity_id"]),
                "unit":      e.get("attributes", {}).get("unit_of_measurement", ""),
            }
            for e in r.json()
            if e["entity_id"].startswith(allowed)
        ], key=lambda x: x["entity_id"])
        _entities_cache["data"] = result
        _entities_cache["ts"]   = now
        return jsonify(result)
    except Exception as e:
        log.warning(f"api_entities: {e}")
        return jsonify([])


@app.route("/api/test/sensor")
def api_test_sensor():
    entity_id = request.args.get("entity_id", "").strip()
    if not entity_id:
        return jsonify({"ok": False, "error": "Keine entity_id angegeben"})
    # Basis-Validierung: muss gültiges HA-Format haben (domain.name)
    if "." not in entity_id or "/" in entity_id or ".." in entity_id:
        return jsonify({"ok": False, "error": "Ungültige entity_id"})
    try:
        r         = requests.get(get_ha_api_url(entity_id), headers=get_ha_headers(), timeout=8)
        d         = r.json()
        state_val = d.get("state", "unavailable")
        if state_val in ("unavailable", "unknown"):
            return jsonify({"ok": False, "error": f"Sensor nicht verfügbar ({state_val})"})
        unit = d.get("attributes", {}).get("unit_of_measurement", "")
        return jsonify({"ok": True, "value": state_val, "unit": unit})
    except Exception as e:
        return jsonify({"ok": False, "error": str(e)})


def _worker_init():
    """Startet den Scheduler-Thread — muss im gunicorn Worker-Prozess laufen."""
    if _daily_budget.get("laden_pausiert"):
        state["laden_pausiert"] = True
        log.info("Pause-State wiederhergestellt (war vor Neustart aktiv)")
    log.info("=" * 55)
    log.info("Smart EV Charger gestartet")
    log.info(f"evcc: {get_evcc_url()} | HA: {'Supervisor' if SUPERVISOR_TOKEN else _DEV_CFG.get('ha_url','?')}")
    log.info(f"Batterie: {get_batt_kap()} kWh | Ziel-SOC: {get_batt_ziel_soc()}% | Min-SOC: {get_batt_min_soc()}%")
    log.info(f"Intervall: {get_update_interval()} min | Debug: {'AN' if is_debug_mode() else 'AUS'} | Forecast: {user_settings.get('forecast_provider','forecast_solar')}")
    log.info("=" * 55)
    t = threading.Thread(target=scheduler, daemon=True)
    t.start()


if __name__ == "__main__":
    init_db()
    port = int(os.environ.get("INGRESS_PORT", 8099))
    try:
        from gunicorn.app.base import BaseApplication
        class _GunicornApp(BaseApplication):
            def load_config(self):
                self.cfg.set("bind",     f"0.0.0.0:{port}")
                self.cfg.set("workers",  1)
                self.cfg.set("threads",  4)
                self.cfg.set("loglevel", "warning")
                self.cfg.set("accesslog", "-")
                # Thread im Worker starten, nicht im Master (sonst falscher Prozess)
                self.cfg.set("post_fork", lambda s, w: _worker_init())
            def load(self):
                return app
        log.info(f"Starte mit gunicorn auf Port {port}")
        _GunicornApp().run()
    except ImportError:
        log.warning("gunicorn nicht verfügbar — Fallback auf Flask Dev-Server")
        _worker_init()
        app.run(host="0.0.0.0", port=port, debug=False)
