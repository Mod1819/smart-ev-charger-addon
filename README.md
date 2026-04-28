# Smart EV Charger — Home Assistant Add-on

Intelligente PV-basierte Ladesteuerung für Elektroautos. Das Add-on berechnet täglich ein Ladebudget auf Basis der PV-Prognose, des Hausverbrauchs und des Batteriestands — vollautomatisch, mit Lernfunktion und direkter HA-Integration.

## Features

- **Budget-Ladesteuerung** — tägliches Ladebudget aus PV-Prognose minus Hausverbrauch und Speicherbedarf
- **Lernfunktion** — wochentags- und feiertagsabhängige EMA für Hausverbrauch und Batterieladerate
- **Prognose-Integration** — Forecast.Solar, Solcast (HACS) oder Solcast Direct
- **Wallbox-Steuerung** — evcc (empfohlen) oder direkt per Home Assistant Entity
- **Batterie optional** — funktioniert auch ohne Heimspeicher
- **Sensor-Suche** — HA-Entities per Suchfeld statt manuelle ID-Eingabe
- **Push-Benachrichtigungen** — Budget niedrig, Deadline urgent, Laden fertig
- **Config Backup/Restore** — Export und Import per JSON
- **Hell- & Dunkel-Modus** — automatisch oder manuell umschaltbar
- **Mehrsprachig** — Deutsch und Englisch
- **Feiertage** — bundeslandspezifisch (alle 16 Bundesländer)

## Installation als Custom Repository in HACS

1. HACS öffnen → **Einstellungen** → **Benutzerdefinierte Repositories**
2. URL eintragen: `https://github.com/DEIN_GITHUB_USER/smart-ev-charger-addon`
3. Kategorie: **Add-on**
4. Hinzufügen → Add-on erscheint in der HACS Add-on-Liste
5. Installieren und in Home Assistant aktivieren

## Manuelle Installation (ohne HACS)

```bash
# In der HA-Shell oder per SSH:
cd /mnt/data/supervisor/addons/local/
git clone https://github.com/DEIN_GITHUB_USER/smart-ev-charger-addon smart_ev_charger
ha addons rebuild local_smart_ev_charger
```

## Einrichtung

Nach der Installation:

1. Add-on starten
2. **Config-Tab** öffnen
3. **Wallbox-Typ** wählen (evcc oder HA-Direkt)
4. **Sensoren** per 🔍-Suche zuweisen (PV-Prognose, Batterie-SOC, PV-Leistung, Hausverbrauch)
5. **Prognose-Anbieter** wählen und ggf. API-Key eintragen
6. Speichern — das war's

## Voraussetzungen

- Home Assistant OS oder Supervised
- Eine Wallbox, die über evcc oder Home Assistant steuerbar ist
- PV-Anlage mit Prognose-Integration (Forecast.Solar kostenlos, Solcast optional)

## Wallbox-Steuerung

### evcc (empfohlen)
Vollständige Integration mit Modus, Strom, Energie-Tracking. evcc separat installieren und URL eintragen.

### HA-Direkt
Für Wallboxen die direkt über HA gesteuert werden (go-eCharger, Easee, Heidelberg, etc.). Folgende Entities werden benötigt:
- `binary_sensor` — Auto angesteckt
- `binary_sensor` — Lädt gerade
- `sensor` — Energie heute (kWh)
- `switch` / `input_boolean` — Laden ein/aus
- `number` — Ladestrom (Ampere)

## Changelog

### 2.0.0
- Sensor-Suche mit Live-Filter über alle HA-Entities
- Batterie optional (Schalter in Config)
- evcc optional — direkte HA-Wallbox-Steuerung
- Prognose-Provider-Auswahl (Forecast.Solar / Solcast HACS / Solcast Direct)
- Config Export & Import (JSON)
- Hell-/Dunkel-Modus mit System-Preference
- Push-Benachrichtigungen (Budget, Deadline, Fertig)
- Feiertage nach Bundesland (python-holidays)
- History-Charts (Budget, Energie, EMA) — kollabierbar
- Gunicorn-Server statt Flask Dev-Server
- Erster-Start-Banner wenn Config unvollständig

### 1.0.0
- Initiale Version mit Budget-Ladesteuerung und evcc-Integration
