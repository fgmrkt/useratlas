#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
UserAtlas - checks whether usernames are available on gaming platforms,
social networks, developer sites and as a domain name.

Ready-made Windows app (no Python needed):
    https://github.com/fgmrkt/useratlas/releases/latest
That app is a small launcher that fetches the latest version of this file
(the app/ folder of the repository) from GitHub every time it starts.

Running it yourself with Python? Install once:
    pip install requests

Window:
    python useratlas.py

Terminal:
    python useratlas.py names.txt                 all platforms, names from names.txt
    python useratlas.py pixelfox nightowl         single names work too
    python useratlas.py names.txt --group gaming,socials
    python useratlas.py names.txt --platform minecraft,discord,github
    python useratlas.py names.txt --tld com,nl,gg
    python useratlas.py names.txt --quiet         only show available names
    python useratlas.py --selftest                only test which platforms work right now
    python useratlas.py names.txt --rules         only check each site's name rules (offline)
    python useratlas.py --list                    show all platforms and their name rules

How it works:
  - All platforms run at the same time, but each platform waits between checks
    so sites don't block you.
  - First it runs a self-test: per platform a known name (must be 'taken') and a
    random name (must be 'available'). Platforms that get this wrong are skipped,
    so you never get a false 'available'.
  - Every result is saved to results.csv right away. Stop halfway (Ctrl+C) and the
    next run continues where it left off. Names with result 'unknown' are retried.
  - At the end you get overview.csv with one column per platform for each name.
"""

from __future__ import annotations

import argparse
import csv
import base64
import hashlib
import json
import zlib
import math
import os
import queue
import random
import re
import socket
import string
import subprocess
import sys
import threading
import time
import webbrowser
from dataclasses import dataclass, field
from datetime import datetime
from typing import Callable, Dict, List, Optional, Tuple

try:
    import requests
except ImportError:
    requests = None  # main() helps installing it

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
    from tkinter import font as tkfont
except ImportError:
    tk = None


AVAILABLE, TAKEN, INVALID, UNKNOWN = "available", "taken", "invalid", "unknown"
FINAL = {AVAILABLE, TAKEN, INVALID}
TIMEOUT = 15
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36")
STANDARD_TLDS = "com,net,org,nl,eu,io,gg,lol"
GROUPS = ["gaming", "socials", "other", "domains"]

GITHUB_REPO = "fgmrkt/useratlas"
LAUNCHER: Optional[dict] = None  # filled in by the launcher (UserAtlas.exe) before main()


def _read_info() -> dict:
    try:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "info.json"),
                  encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


VERSION = str(_read_info().get("version", "dev"))  # lives in app/info.json


def is_app() -> bool:
    """True when running inside the built .exe (PyInstaller), not as a plain script."""
    return bool(getattr(sys, "frozen", False))


def data_dir() -> str:
    """Where results are kept: next to the script, or a per-user folder for the app."""
    if not is_app():
        path = os.path.dirname(os.path.abspath(__file__))
    elif os.name == "nt":
        path = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "UserAtlas")
    elif sys.platform == "darwin":
        path = os.path.expanduser("~/Library/Application Support/UserAtlas")
    else:
        path = os.path.expanduser("~/.local/share/useratlas")
    os.makedirs(path, exist_ok=True)
    return path


def resource_path(name: str) -> str:
    """Path to a bundled file (like the icon): next to this script, or inside the .exe."""
    here = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    if os.path.exists(here):
        return here
    return os.path.join(getattr(sys, "_MEIPASS", ""), name)


Result = Tuple[str, str]  # (status, detail)


class RateLimited(Exception):
    """The site says: slow down. wait = number of seconds (or None)."""

    def __init__(self, wait: Optional[float] = None):
        super().__init__("rate limited")
        self.wait = wait


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def retry_after(r) -> Optional[float]:
    try:
        return float(r.headers.get("Retry-After"))
    except (TypeError, ValueError):
        return None


def unexpected(r) -> Result:
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    return UNKNOWN, f"unexpected response (HTTP {r.status_code})"


def by_status(r, taken=(200,), available=(404,), available_detail="") -> Result:
    """Common pattern: the HTTP status code says it all."""
    if r.status_code in taken:
        return TAKEN, ""
    if r.status_code in available:
        return AVAILABLE, available_detail
    return unexpected(r)


def json_or_none(r):
    try:
        return r.json()
    except ValueError:
        return None


def first_message(data) -> str:
    """Finds the first human-readable 'message' in an error response."""
    if isinstance(data, dict):
        if isinstance(data.get("message"), str) and data.get("code") not in (None, 50035):
            return data["message"]
        for value in data.values():
            found = first_message(value)
            if found:
                return found
    elif isinstance(data, list):
        for value in data:
            found = first_message(value)
            if found:
                return found
    return ""


def shorten(text: str, n: int = 80) -> str:
    text = " ".join(str(text).split())
    return text if len(text) <= n else text[: n - 1] + "…"


def new_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({
        "User-Agent": UA,
        "Accept-Language": "en-US,en;q=0.9",
    })
    return s


# ---------------------------------------------------------------------------
# Checks per platform. Each check gets (session, name) and returns
# (status, detail), or raises RateLimited.
# ---------------------------------------------------------------------------

NO_PROFILE = "no profile found"


def check_minecraft(s, n):
    r = s.get(f"https://api.mojang.com/users/profiles/minecraft/{n}", timeout=TIMEOUT)
    if r.status_code == 400:
        return INVALID, "Minecraft says this name isn't allowed"
    return by_status(r, available=(204, 404))


def check_roblox(s, n):
    r = s.get("https://auth.roblox.com/v1/usernames/validate",
              params={"username": n, "birthday": "2000-01-01T00:00:00.000Z",
                      "context": "Signup"},
              timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    d = json_or_none(r)
    if isinstance(d, dict) and "code" in d:
        code = d["code"]
        if code == 0:
            return AVAILABLE, ""
        if code == 1:
            return TAKEN, ""
        return INVALID, shorten(d.get("message") or f"Roblox says this name isn't allowed ({code})")
    return unexpected(r)


def check_steam(s, n):
    r = s.get(f"https://steamcommunity.com/id/{n}/", params={"xml": "1"}, timeout=TIMEOUT)
    if "<steamID64>" in r.text:
        return TAKEN, ""
    if "could not be found" in r.text:
        return AVAILABLE, ""
    return unexpected(r)


def check_discord(s, n):
    r = s.post("https://discord.com/api/v9/unique-username/username-attempt-unauthed",
               json={"username": n}, timeout=TIMEOUT)
    d = json_or_none(r)
    if r.status_code == 429:
        wait = d.get("retry_after") if isinstance(d, dict) else None
        raise RateLimited(float(wait) if wait else retry_after(r))
    if r.status_code == 200 and isinstance(d, dict) and "taken" in d:
        return (TAKEN, "") if d["taken"] else (AVAILABLE, "")
    if r.status_code == 400:
        return INVALID, shorten(first_message(d) or "Discord says this name isn't allowed")
    return unexpected(r)


def check_chesscom(s, n):
    r = s.get(f"https://api.chess.com/pub/player/{n.lower()}", timeout=TIMEOUT)
    return by_status(r, taken=(200, 410))


def check_lichess(s, n):
    r = s.get(f"https://lichess.org/api/user/{n}", timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r) or 60)  # Lichess asks for a full minute
    return by_status(r)


def check_instagram(s, n):
    r = s.get("https://www.instagram.com/api/v1/users/web_profile_info/",
              params={"username": n},
              headers={"X-IG-App-ID": "936619743392459",
                       "X-Requested-With": "XMLHttpRequest",
                       "Referer": f"https://www.instagram.com/{n}/",
                       "Accept": "*/*"},
              allow_redirects=False, timeout=TIMEOUT)
    if r.status_code == 404:
        return AVAILABLE, NO_PROFILE
    if r.status_code == 200:
        d = json_or_none(r)
        if isinstance(d, dict) and (d.get("data") or {}).get("user"):
            return TAKEN, ""
    if r.status_code in (301, 302, 401):
        return UNKNOWN, "Instagram wants you to log in (try later or slower)"
    return unexpected(r)


TIKTOK_DATA = re.compile(
    r'<script[^>]*id="__UNIVERSAL_DATA_FOR_REHYDRATION__"[^>]*>(.*?)</script>', re.S)


def check_tiktok(s, n):
    r = s.get(f"https://www.tiktok.com/@{n}", headers={"Accept": "text/html"},
              timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    m = TIKTOK_DATA.search(r.text)
    if m:
        try:
            info = json.loads(m.group(1))["__DEFAULT_SCOPE__"]["webapp.user-detail"]
        except (ValueError, KeyError, TypeError):
            info = None
        if isinstance(info, dict):
            code = info.get("statusCode")
            user = ((info.get("userInfo") or {}).get("user") or {})
            if code == 10221:
                return AVAILABLE, NO_PROFILE
            if code in (0, 10222) or user.get("uniqueId"):
                return TAKEN, ""
            return UNKNOWN, f"unknown TikTok code {code}"
    return UNKNOWN, "TikTok returned no usable page (bot check?)"


def check_x(s, n):
    r = s.get("https://api.x.com/i/users/username_available.json",
              params={"username": n}, timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    d = json_or_none(r)
    if isinstance(d, dict) and "valid" in d:
        if d["valid"] is True:
            return AVAILABLE, ""
        reason = d.get("reason", "")
        if reason == "taken":
            return TAKEN, ""
        return INVALID, shorten(d.get("desc") or reason or "X says this name isn't allowed")
    return unexpected(r)


def check_youtube(s, n):
    r = s.get(f"https://www.youtube.com/@{n}",
              cookies={"SOCS": "CAI", "CONSENT": "YES+cb"}, timeout=TIMEOUT)
    if "consent." in r.url:
        return UNKNOWN, "YouTube's cookie notice is in the way"
    return by_status(r, available_detail="no channel found")


def check_snapchat(s, n):
    r = s.get(f"https://www.snapchat.com/add/{n}", timeout=TIMEOUT)
    return by_status(r, available_detail=NO_PROFILE)


def check_telegram(s, n):
    r = s.get(f"https://t.me/{n}", timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    if "tgme_page_title" in r.text:
        return TAKEN, ""
    if r.status_code == 200 and "tgme_page" in r.text:
        return AVAILABLE, NO_PROFILE
    return unexpected(r)


def check_bluesky(s, n):
    r = s.get("https://public.api.bsky.app/xrpc/com.atproto.identity.resolveHandle",
              params={"handle": f"{n}.bsky.social"}, timeout=TIMEOUT)
    if r.status_code == 200:
        return TAKEN, ""
    if r.status_code == 400:
        return AVAILABLE, ""
    return unexpected(r)


def check_github(s, n):
    r = s.head(f"https://github.com/{n}", allow_redirects=False, timeout=TIMEOUT)
    return by_status(r, taken=(200, 301, 302))


def check_gitlab(s, n):
    r = s.get(f"https://gitlab.com/users/{n}/exists",
              headers={"Accept": "application/json"}, timeout=TIMEOUT)
    d = json_or_none(r)
    if isinstance(d, dict) and "exists" in d:
        return (TAKEN, "") if d["exists"] else (AVAILABLE, "")
    return unexpected(r)


def check_reddit(s, n):
    r = s.get("https://www.reddit.com/api/username_available.json",
              params={"user": n}, timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    if r.status_code == 200:
        d = json_or_none(r)
        if d is True:
            return AVAILABLE, ""
        if d is False:
            return TAKEN, ""
    # Fallback: does the profile exist?
    r = s.get(f"https://www.reddit.com/user/{n}/about.json", timeout=TIMEOUT)
    return by_status(r, available_detail="no profile found (deleted names can't be claimed again)")


TWITCH_CLIENT_ID = "kimne78kx3ncx6brgo4mv6wki5h1ko"  # twitch.tv's own public client id


def check_twitch(s, n):
    url = "https://gql.twitch.tv/gql"
    h = {"Client-Id": TWITCH_CLIENT_ID}
    r = s.post(url, headers=h, timeout=TIMEOUT, json={
        "query": "query($u:String!){isUsernameAvailable(username:$u)}",
        "variables": {"u": n}})
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    d = json_or_none(r)
    try:
        v = d["data"]["isUsernameAvailable"]
        if v is True:
            return AVAILABLE, ""
        if v is False:
            return TAKEN, ""
    except (KeyError, TypeError):
        pass
    # Fallback: is there an account with this name?
    r = s.post(url, headers=h, timeout=TIMEOUT, json={
        "query": "query($u:String!){user(login:$u,lookupType:ALL){id}}",
        "variables": {"u": n}})
    d = json_or_none(r)
    try:
        return (TAKEN, "") if d["data"]["user"] else (AVAILABLE, NO_PROFILE)
    except (KeyError, TypeError):
        return unexpected(r)


def check_soundcloud(s, n):
    r = s.get(f"https://soundcloud.com/{n}", timeout=TIMEOUT)
    return by_status(r, available_detail=NO_PROFILE)


# ---------------------------------------------------------------------------
# Domain names: RDAP first (the modern successor of WHOIS), WHOIS otherwise.
# ---------------------------------------------------------------------------

_rdap_lock = threading.Lock()
_rdap_servers: Optional[Dict[str, str]] = None
_whois_lock = threading.Lock()
_whois_servers: Dict[str, Optional[str]] = {}

WHOIS_FREE = ("no match", "not found", "no entries found", "no data found", "is free",
              "status: available", "status: free", "no object found",
              "available for registration", "nothing found", "does not exist")
WHOIS_TAKEN = ("creation date", "created:", "registered:", "registrar:", "registrant",
               "status: active", "status: connect", "name server", "nameservers",
               "nserver", "domain name:", "domain:")
WHOIS_LIMIT = ("limit exceeded", "too many", "exceeded the", "try again later")


def rdap_servers(s) -> Dict[str, str]:
    global _rdap_servers
    with _rdap_lock:
        if _rdap_servers is None:
            table = {}
            try:
                d = s.get("https://data.iana.org/rdap/dns.json", timeout=TIMEOUT).json()
                for tlds, urls in d["services"]:
                    url = next((u for u in urls if u.startswith("https")), urls[0])
                    for t in tlds:
                        table[t.lower()] = url if url.endswith("/") else url + "/"
            except Exception:
                pass  # fall back to WHOIS
            _rdap_servers = table
        return _rdap_servers


def whois_query(server: str, query: str) -> str:
    with socket.create_connection((server, 43), timeout=TIMEOUT) as sock:
        sock.sendall((query + "\r\n").encode())
        parts = []
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                break
            parts.append(chunk)
    return b"".join(parts).decode("utf-8", "replace")


def whois_server(tld: str) -> Optional[str]:
    with _whois_lock:
        if tld not in _whois_servers:
            m = re.search(r"^whois:\s*(\S+)", whois_query("whois.iana.org", tld), re.M | re.I)
            _whois_servers[tld] = m.group(1) if m else None
        return _whois_servers[tld]


def whois_check(tld: str, domain: str) -> Result:
    server = whois_server(tld)
    if not server:
        return UNKNOWN, f"no WHOIS server known for .{tld}"
    text = whois_query(server, domain).lower()
    if any(t in text for t in WHOIS_LIMIT):
        raise RateLimited(60)
    if "quarantine" in text:
        return TAKEN, "in quarantine (just cancelled)"
    if any(t in text for t in WHOIS_FREE):
        return AVAILABLE, "via WHOIS"
    if any(t in text for t in WHOIS_TAKEN):
        return TAKEN, ""
    return UNKNOWN, "could not read the WHOIS answer"


def make_domain_check(tld: str) -> Callable:
    def check(s, n):
        domain = f"{n}.{tld}"
        base = rdap_servers(s).get(tld)
        if base:
            r = s.get(f"{base}domain/{domain}",
                      headers={"Accept": "application/rdap+json"}, timeout=TIMEOUT)
            if r.status_code == 200:
                return TAKEN, ""
            if r.status_code == 404:
                return AVAILABLE, ""
            if r.status_code == 429:
                raise RateLimited(retry_after(r))
            # any other answer: try WHOIS
        return whois_check(tld, domain)
    return check


# ---------------------------------------------------------------------------
# The platform list
# ---------------------------------------------------------------------------

# Naming rules. Each platform has its own: length, allowed characters and a few
# extra rules. problem() says in plain words why a name isn't allowed. Only rules
# we're sure about are listed; anything else the site itself reports while checking.

@dataclass
class Rules:
    min_len: int
    max_len: int
    chars: str                   # regex character class, e.g. "A-Za-z0-9_"
    chars_text: str              # the same in words, e.g. "letters, numbers and _"
    extra: tuple = ()            # (test(name) -> True when broken, rule in words)

    def problem(self, name: str) -> Optional[str]:
        if len(name) < self.min_len:
            return f"too short (at least {self.min_len} characters)"
        if len(name) > self.max_len:
            return f"too long (at most {self.max_len} characters)"
        bad = sorted({c for c in name if not re.fullmatch(f"[{self.chars}]", c)})
        if bad:
            shown = ", ".join("space" if c == " " else f"'{c}'" for c in bad[:4])
            return f"{shown} not allowed (only {self.chars_text})"
        for broken, rule in self.extra:
            if broken(name):
                return rule
        return None

    def describe(self) -> str:
        length = (f"{self.min_len}–{self.max_len} characters" if self.max_len < 100
                  else f"at least {self.min_len} characters")
        return "; ".join([length, self.chars_text] + [rule for _, rule in self.extra])


def must_start(chars: str, text: str):
    return (lambda n: not re.match(f"[{chars}]", n), f"must start with {text}")


def must_end(chars: str, text: str):
    return (lambda n: not re.search(f"[{chars}]$", n), f"must end with {text}")


def cant_start(prefix: str, text: str):
    return (lambda n: n.startswith(prefix), f"can't start with {text}")


def cant_end(*endings: str, text: str = ""):
    words = text or " or ".join(f"'{e}'" for e in endings)
    return (lambda n: n.lower().endswith(endings), f"can't end with {words}")


def no_repeat(char: str, text: str):
    return (lambda n: char * 2 in n, f"no two {text} in a row")


def at_most(char: str, count: int, text: str):
    return (lambda n: n.count(char) > count, f"at most {'one' if count == 1 else count} {text}")


def no_word(*words: str):
    return (lambda n: any(w in n.lower() for w in words),
            "can't contain " + " or ".join(f"'{w}'" for w in words))


def not_exactly(*words: str):
    return (lambda n: n.lower() in words, "can't be " + " or ".join(f"'{w}'" for w in words))


LETTER_OR_NUMBER = ("A-Za-z0-9", "a letter or number")


# ---------------------------------------------------------------------------
# Blocked words: slurs and strong profanity that most sites reject at sign-up.
# The word list (app/blocklist.json) comes from the MIT-licensed
# dsojevic/profanity-list and is used only to FLAG such usernames as not
# allowed. We never show which word matched, only that one did.
# ---------------------------------------------------------------------------

# Map look-alike characters back to letters so "n1gga" or "f4g" is still caught.
_LEET_I = str.maketrans({"0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "6": "g",
                         "7": "t", "8": "b", "9": "g", "@": "a", "$": "s", "!": "i"})
_LEET_L = str.maketrans({"0": "o", "1": "l", "3": "e", "4": "a", "5": "s", "6": "g",
                         "7": "t", "8": "b", "9": "g", "@": "a", "$": "s", "!": "i"})


def _compile_term(alt: str):
    """Turn one blocklist pattern into a regex; 'x*' means one or more x."""
    alt = re.sub(r"[\s.\-]", "", alt.lower())
    out, core = [], []
    i = 0
    while i < len(alt):
        c = alt[i]
        if i + 1 < len(alt) and alt[i + 1] == "*":
            out.append(re.escape(c) + "+")
            core.append(c)
            i += 2
        else:
            out.append(re.escape(c))
            core.append(c)
            i += 1
    return re.compile("".join(out)), len("".join(core))


class Blocklist:
    """Flags usernames that contain a slur or strong profanity.

    - the whole name, or a word inside it, is a blocked term  -> always flagged;
    - a high-risk term (slur or severity 4) appears inside the name -> flagged,
      unless the name (or that word) is a known safe English word."""

    def __init__(self, terms=(), safe_words=()):
        self.safe = set(safe_words)
        self.terms = []
        for e in terms:
            sev = e.get("severity", 3)
            tags = set(e.get("tags", []))
            slur = bool(tags & {"racial", "lgbtq"})
            high_risk = sev >= 3
            core_min = 4 if (slur or sev >= 4) else 5
            exc = [x.replace(" ", "").split("*") for x in e.get("exceptions", [])]
            for a in e.get("match", "").split("|"):
                if a.strip():
                    rx, core = _compile_term(a)
                    self.terms.append((rx, core, high_risk, core_min, exc))

    @staticmethod
    def _forms(name: str) -> List[str]:
        low = name.lower()
        plain = re.sub(r"[^a-z0-9]", "", low)
        a = re.sub(r"[^a-z]", "", low.translate(_LEET_I))
        b = re.sub(r"[^a-z]", "", low.translate(_LEET_L))
        return list(dict.fromkeys([plain, a, b]))

    @staticmethod
    def _tokens(name: str) -> set:
        out = set()
        for part in re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+", name):
            low = part.lower()
            out.update([low, low.translate(_LEET_I), low.translate(_LEET_L)])
        return out

    @staticmethod
    def _excepted(form, start, end, matched, exceptions) -> bool:
        for parts in exceptions:
            rx = re.compile(re.escape(matched).join(re.escape(p) for p in parts))
            for m in rx.finditer(form):
                if m.start() <= start and m.end() >= end:
                    return True
        return False

    def blocked(self, name: str) -> bool:
        if not self.terms:
            return False
        forms = self._forms(name)
        tokens = self._tokens(name)
        safe_token = bool(tokens & self.safe)
        for rx, core, high_risk, core_min, exc in self.terms:
            for f in forms:
                if rx.fullmatch(f):
                    return True
            for t in tokens:
                if rx.fullmatch(t):
                    return True
            if high_risk and core >= core_min and not safe_token:
                for f in forms:
                    m = rx.search(f)
                    if m and not self._excepted(f, m.start(), m.end(), m.group(), exc):
                        return True
        return False


# The word list is embedded here (zlib+base64 of the data in app/blocklist.json),
# so the filter ALWAYS works and can never silently fall back to "no filtering"
# just because a separate file didn't download. To change the list, edit
# app/blocklist.json and regenerate this blob with tools/embed_blocklist.py.
_BLOCKLIST_BLOB = (
    "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"
)


def load_blocklist() -> Blocklist:
    try:
        d = json.loads(zlib.decompress(base64.b64decode(_BLOCKLIST_BLOB)))
        return Blocklist(d.get("terms", ()), d.get("safe_words", ()))
    except Exception:
        return Blocklist()  # should never happen; filter off is better than a crash


BLOCKLIST = load_blocklist()
BLOCKED_REASON = "contains a blocked word (slur or strong profanity)"


@dataclass
class Platform:
    key: str                     # short name for --platform, e.g. "minecraft"
    title: str                   # as shown in the overview
    group: str
    check: Callable
    rules: Rules                 # which names the platform allows
    delay: float                 # seconds between checks
    known_names: List[str]       # for the self-test: these must be 'taken'
    lowercase: bool = False      # lowercase the name first
    link: str = ""               # page to view/claim, {n} = name
    filters_words: bool = True    # does this site reject slurs/profanity in handles?

    def prepare(self, name: str) -> str:
        return name.lower() if self.lowercase else name

    def problem(self, name: str) -> Optional[str]:
        """Why this platform doesn't allow the name, or None if it fits the rules."""
        prepared = self.prepare(name)
        if self.filters_words and BLOCKLIST.blocked(prepared):
            return BLOCKED_REASON
        return self.rules.problem(prepared)

    def valid(self, name: str) -> bool:
        return self.problem(name) is None

    @property
    def short_title(self) -> str:
        return self.title.split(" (")[0]

    def link_for(self, name: str) -> str:
        return self.link.replace("{n}", self.prepare(name)) if self.link else ""


LINKS = {
    "minecraft": "https://namemc.com/search?q={n}",
    "roblox": "https://www.roblox.com/search/users?keyword={n}",
    "steam": "https://steamcommunity.com/id/{n}",
    "discord": "https://discord.com/login",
    "chesscom": "https://www.chess.com/member/{n}",
    "lichess": "https://lichess.org/@/{n}",
    "instagram": "https://www.instagram.com/{n}/",
    "tiktok": "https://www.tiktok.com/@{n}",
    "x": "https://x.com/{n}",
    "youtube": "https://www.youtube.com/@{n}",
    "snapchat": "https://www.snapchat.com/add/{n}",
    "telegram": "https://t.me/{n}",
    "bluesky": "https://bsky.app/profile/{n}.bsky.social",
    "github": "https://github.com/{n}",
    "gitlab": "https://gitlab.com/{n}",
    "reddit": "https://www.reddit.com/user/{n}",
    "twitch": "https://www.twitch.tv/{n}",
    "soundcloud": "https://soundcloud.com/{n}",
}


def all_platforms(tlds: List[str]) -> List[Platform]:
    P, R = Platform, Rules
    LN = LETTER_OR_NUMBER
    words = "letters, numbers and _"
    platforms = [
        # gaming
        P("minecraft", "Minecraft", "gaming", check_minecraft,
          R(3, 16, "A-Za-z0-9_", words), 1.2, ["Notch", "jeb_"]),
        P("roblox", "Roblox", "gaming", check_roblox,
          R(3, 20, "A-Za-z0-9_", words, (must_start(*LN), must_end(*LN), at_most("_", 1, "_"))),
          1.5, ["builderman", "Shedletsky"]),
        P("steam", "Steam (profile URL)", "gaming", check_steam,
          R(3, 32, "A-Za-z0-9_-", "letters, numbers, _ and -"),
          1.5, ["gabelogannewell", "robinwalker"]),
        P("discord", "Discord", "gaming", check_discord,
          R(2, 32, "a-z0-9_.", "letters, numbers, _ and .",
            (no_repeat(".", "periods"), no_word("discord"), not_exactly("everyone", "here"))),
          4.0, ["wumpus", "discord"], lowercase=True),
        P("chesscom", "Chess.com", "gaming", check_chesscom,
          R(3, 25, "A-Za-z0-9_-", "letters, numbers, _ and -"),
          1.0, ["hikaru", "magnuscarlsen"]),
        P("lichess", "Lichess", "gaming", check_lichess,
          R(2, 30, "A-Za-z0-9_-", "letters, numbers, _ and -", (must_start(*LN), must_end(*LN))),
          1.5, ["thibault", "DrNykterstein"]),
        # socials
        P("instagram", "Instagram", "socials", check_instagram,
          R(1, 30, "A-Za-z0-9._", "letters, numbers, . and _",
            (cant_start(".", "a period"), cant_end(".", text="a period"),
             no_repeat(".", "periods"))),
          5.0, ["instagram", "natgeo"]),
        P("tiktok", "TikTok", "socials", check_tiktok,
          R(2, 24, "A-Za-z0-9._", "letters, numbers, . and _", (cant_end(".", text="a period"),)),
          3.0, ["tiktok", "khaby.lame"]),
        P("x", "X / Twitter", "socials", check_x,
          R(4, 15, "A-Za-z0-9_", words, (no_word("twitter", "admin"),)),
          3.0, ["elonmusk", "nasa"]),
        P("youtube", "YouTube (@handle)", "socials", check_youtube,
          R(3, 30, "A-Za-z0-9._-", "letters, numbers, ., _ and -"),
          1.5, ["youtube", "mrbeast"]),
        P("snapchat", "Snapchat", "socials", check_snapchat,
          R(3, 15, "A-Za-z0-9._-", "letters, numbers, ., _ and -",
            (must_start("A-Za-z", "a letter"), must_end(*LN))),
          2.0, ["teamsnapchat", "snapchat"]),
        P("telegram", "Telegram", "socials", check_telegram,
          R(5, 32, "A-Za-z0-9_", words,
            (must_start("A-Za-z", "a letter"), cant_end("_", text="_"))),
          2.0, ["durov", "telegram"]),
        P("bluesky", "Bluesky (.bsky.social)", "socials", check_bluesky,
          R(3, 18, "a-z0-9-", "letters, numbers and -", (must_start(*LN), must_end(*LN))),
          0.5, ["jay", "pfrazee"], lowercase=True),
        # other
        P("github", "GitHub", "other", check_github,
          R(1, 39, "A-Za-z0-9-", "letters, numbers and -",
            (must_start(*LN), must_end(*LN), no_repeat("-", "hyphens"))),
          1.5, ["torvalds", "github"], filters_words=False),
        P("gitlab", "GitLab", "other", check_gitlab,
          R(2, 255, "A-Za-z0-9_.-", "letters, numbers, _, . and -",
            (cant_start("-", "-"), cant_end(".", text="a period"), cant_end(".git", ".atom"))),
          1.5, ["sytses", "dzaporozhets"], filters_words=False),
        P("reddit", "Reddit", "other", check_reddit,
          R(3, 20, "A-Za-z0-9_-", "letters, numbers, _ and -"),
          3.0, ["spez", "kn0thing"]),
        P("twitch", "Twitch", "other", check_twitch,
          R(4, 25, "A-Za-z0-9_", words, (cant_start("_", "_"),)),
          1.5, ["ninja", "shroud"]),
        P("soundcloud", "SoundCloud", "other", check_soundcloud,
          R(3, 25, "A-Za-z0-9_-", "letters, numbers, _ and -"),
          1.5, ["skrillex", "soundcloud"]),
    ]
    for p in platforms:
        p.link = LINKS.get(p.key, "")
    for tld in tlds:
        platforms.append(P(f"domain.{tld}", f".{tld}", "domains", make_domain_check(tld),
                           R(1, 63, "a-z0-9-", "letters, numbers and -",
                             (must_start(*LN), must_end(*LN))), 1.0,
                           ["google", "amazon", "hello"], lowercase=True,
                           filters_words=False,
                           link="https://www.namecheap.com/domains/registration/results/"
                                f"?domain={{n}}.{tld}"))
    return platforms


# ---------------------------------------------------------------------------
# Output: colors and storage
# ---------------------------------------------------------------------------

COLOR = {AVAILABLE: "\033[92m", TAKEN: "\033[91m", INVALID: "\033[90m", UNKNOWN: "\033[93m"}
SHOWN = {AVAILABLE: "available", TAKEN: "taken", INVALID: "not allowed", UNKNOWN: "unknown"}
RESET = "\033[0m"
_print_lock = threading.Lock()
_output: Optional[Callable[[str], None]] = None  # the window catches messages here
ANSI = re.compile(r"\033\[[0-9;]*m")


def say(text: str = ""):
    if _output is not None:
        _output(ANSI.sub("", text))
        return
    with _print_lock:
        print(text, flush=True)


def colored(status: str, width: int = 11) -> str:
    return f"{COLOR.get(status, '')}{SHOWN.get(status, status):<{width}}{RESET}"


class Store:
    """Writes every result to a CSV right away and remembers earlier runs."""

    FIELDS = ["time", "name", "platform", "status", "detail"]

    def __init__(self, path: str, fresh: bool, quiet: bool,
                 on_result: Optional[Callable] = None):
        self.path = path
        self.quiet = quiet
        self.on_result = on_result  # window: receives every result instead of printing
        self.lock = threading.Lock()
        self.results: Dict[Tuple[str, str], Tuple[str, str]] = {}
        self.new = 0
        if os.path.exists(path) and (fresh or os.path.getsize(path) == 0):
            os.remove(path)
        if os.path.exists(path):
            with open(path, newline="", encoding="utf-8-sig") as f:
                for row in csv.DictReader(f, delimiter=";"):
                    try:
                        self.results[(row["name"].lower(), row["platform"])] = (
                            row["status"], row["detail"])
                    except KeyError:
                        continue
            self.f = open(path, "a", newline="", encoding="utf-8")
            self.writer = csv.writer(self.f, delimiter=";")
        else:
            # utf-8-sig so Excel shows characters correctly; ';' opens straight into columns
            self.f = open(path, "w", newline="", encoding="utf-8-sig")
            self.writer = csv.writer(self.f, delimiter=";")
            self.writer.writerow(self.FIELDS)
            self.f.flush()

    def done(self, name: str, p: Platform) -> bool:
        r = self.results.get((name.lower(), p.key))
        return r is not None and r[0] in FINAL

    def save(self, name: str, p: Platform, status: str, detail: str):
        with self.lock:
            if self.f.closed:  # just stopped; the next run redoes this one
                return
            self.results[(name.lower(), p.key)] = (status, detail)
            self.new += 1
            self.writer.writerow([datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                                  name, p.key, status, detail])
            self.f.flush()
        if self.on_result is not None:
            self.on_result(name, p.key, status, detail)
        elif status == AVAILABLE or not self.quiet:
            extra = f"  – {detail}" if detail and status != TAKEN else ""
            say(f"  {colored(status)} {name:<20} {p.title}{extra}")

    def close(self):
        with self.lock:
            self.f.close()


# ---------------------------------------------------------------------------
# Checking, with waiting when a site says 'slow down'
# ---------------------------------------------------------------------------

def safe_check(p: Platform, s, name: str, stop: threading.Event,
               max_tries: int = 5, max_wait: float = 600) -> Result:
    wait = 15.0
    for attempt in range(max_tries):
        try:
            return p.check(s, name)
        except RateLimited as e:
            w = min(e.wait or wait, max_wait)
            if attempt < max_tries - 1:
                if not stop.is_set():
                    say(f"  {p.title} says 'slow down', waiting {max(1, round(w))} sec…")
                if stop.wait(w):
                    return UNKNOWN, "stopped"
            wait *= 2
        except (requests.RequestException, OSError) as e:
            if attempt >= 1:
                return UNKNOWN, f"connection error ({type(e).__name__})"
            if stop.wait(5):
                return UNKNOWN, "stopped"
        except Exception as e:  # unexpected error in a check: don't crash everything
            return UNKNOWN, f"error: {shorten(e)}"
    return UNKNOWN, "refused too often (rate limit)"


def worker(p: Platform, names: List[str], store: Store, stop: threading.Event,
           factor: float, reuse: bool = True):
    s = new_session()
    for name in names:
        if stop.is_set():
            return
        if reuse and store.done(name, p):
            continue
        version = p.prepare(name)
        problem = p.problem(name)  # naming rules + blocked-word filter
        if problem:
            store.save(name, p, INVALID, problem)
            continue
        status, detail = safe_check(p, s, version, stop)
        if status == UNKNOWN and stop.is_set():
            return  # don't save; the next run tries again
        store.save(name, p, status, detail)
        if stop.wait(p.delay * factor):
            return


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def random_name() -> str:
    return "zq" + "".join(random.choices(string.ascii_lowercase + string.digits, k=10))


def test_platform(p: Platform, stop: threading.Event) -> Tuple[bool, str]:
    s = new_session()
    free = safe_check(p, s, p.prepare(random_name()), stop, max_tries=2, max_wait=20)
    if free[0] == UNKNOWN:  # site unreachable or blocking: don't try further
        return False, free[1] or "no usable answer"
    if stop.wait(p.delay):
        return False, "stopped"
    taken = (UNKNOWN, "")
    for known in p.known_names:
        taken = safe_check(p, s, p.prepare(known), stop, max_tries=2, max_wait=20)
        # only try the next known name if this one came back 'available' or 'invalid'
        if taken[0] in (TAKEN, UNKNOWN) or stop.wait(p.delay):
            break
    if free[0] == AVAILABLE and taken[0] == TAKEN:
        return True, ""
    for status, detail in (free, taken):
        if status == UNKNOWN:
            return False, detail or "no usable answer"
    return False, (f"unreliable: known name gave '{taken[0]}', "
                   f"random name gave '{free[0]}'")


def self_test(platforms: List[Platform], stop: threading.Event) -> Dict[str, Tuple[bool, str]]:
    say("Self-test: per platform one known name (must be taken) and one random name "
        "(must be available)…")
    outcome: Dict[str, Tuple[bool, str]] = {}

    def run(p):
        outcome[p.key] = test_platform(p, stop)

    threads = [threading.Thread(target=run, args=(p,), daemon=True) for p in platforms]
    for t in threads:
        t.start()
    wait_for(threads, stop)
    for p in platforms:
        ok, why = outcome.get(p.key, (False, "not tested"))
        label = "\033[92mworks      \033[0m" if ok else "\033[93mnot working\033[0m"
        say(f"  {label} {p.title}" + (f"  – {why}" if why else ""))
    say()
    return outcome


def wait_for(threads: List[threading.Thread], stop: threading.Event,
             on_tick: Optional[Callable] = None):
    """Wait until all threads finish; Ctrl+C sets the stop flag cleanly."""
    try:
        while any(t.is_alive() for t in threads):
            for t in threads:
                t.join(timeout=0.5)
            if on_tick:
                on_tick()
    except KeyboardInterrupt:
        if not stop.is_set():
            say("\nStopping… (everything checked so far is saved)")
            stop.set()
        for t in threads:
            t.join(timeout=3)
        raise


# ---------------------------------------------------------------------------
# Input, selection and overview
# ---------------------------------------------------------------------------

def names_from_text(text: str) -> List[str]:
    """One name per line (commas/spaces are fine too); anything after # is ignored."""
    raw: List[str] = []
    for line in text.splitlines():
        raw.extend(re.split(r"[\s,;]+", line.split("#", 1)[0]))
    return unique(raw)


def unique(raw: List[str]) -> List[str]:
    names, seen = [], set()
    for n in raw:
        n = n.strip().lstrip("@")
        if n and n.lower() not in seen:
            seen.add(n.lower())
            names.append(n)
    return names


def read_names(sources: List[str]) -> List[str]:
    raw: List[str] = []
    for source in sources:
        if os.path.isfile(source):
            with open(source, encoding="utf-8-sig") as f:
                raw.extend(names_from_text(f.read()))
        else:
            raw.append(source)
    return unique(raw)


def split_list(text: Optional[str]) -> List[str]:
    return [t.strip().lower().lstrip(".") for t in (text or "").split(",") if t.strip()]


def choose_platforms(args) -> List[Platform]:
    tlds = split_list(args.tld or STANDARD_TLDS)
    everything = all_platforms(tlds)
    if args.platform:
        chosen = split_list(args.platform)
        known = {p.key for p in everything if p.group != "domains"} | {"domains"}
        wrong = [c for c in chosen if c not in known]
        if wrong:
            sys.exit(f"Unknown platform: {', '.join(wrong)}. See: python useratlas.py --list")
        platforms = [p for p in everything if p.key in chosen]
        if args.tld or "domains" in chosen:
            platforms += [p for p in everything if p.group == "domains"]
        return platforms
    groups = split_list(args.group) or GROUPS
    groups = ["other" if g == "dev" else g for g in groups]
    wrong = [g for g in groups if g not in GROUPS]
    if wrong:
        sys.exit(f"Unknown group: {', '.join(wrong)}. Choose from: {', '.join(GROUPS)}")
    return [p for p in everything if p.group in groups]


def show_list():
    everything = all_platforms(split_list(STANDARD_TLDS))
    for g in GROUPS:
        say(f"\n{g}:")
        for p in everything:
            if p.group == g:
                say(f"  {p.key:<14} {p.title:<24} {p.rules.describe()}")
    say(f"\nChoose domain extensions with --tld (default: {STANDARD_TLDS}).")


def rules_report(names: List[str], platforms: List[Platform]):
    """Checks every name against every platform's naming rules, without going online."""
    for name in names:
        broken = [(p, p.problem(name)) for p in platforms]
        broken = [(p, why) for p, why in broken if why]
        if not broken:
            say(f"  \033[92mallowed everywhere\033[0m  {name}")
            continue
        say(f"  {name}: not allowed on {len(broken)} of {len(platforms)}")
        for p, why in broken:
            say(f"      {p.title:<24} {why}")


def write_overview(path: str, names: List[str], platforms: List[Platform],
                   results: Dict[Tuple[str, str], Tuple[str, str]]):
    rows = []
    for i, name in enumerate(names):
        statuses = [results.get((name.lower(), p.key), ("", ""))[0] for p in platforms]
        rows.append((statuses.count(AVAILABLE), -i, name, statuses))
    rows.sort(reverse=True)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["name", "available on"] + [p.title for p in platforms])
        for count, _, name, statuses in rows:
            w.writerow([name, count] + [SHOWN.get(st, st) for st in statuses])
    return rows


def summary(rows, platforms: List[Platform]):
    say("\nPer platform:")
    for i, p in enumerate(platforms):
        statuses = [st[i] for _, _, _, st in rows]
        parts = [f"{colored(s, 0)} {statuses.count(s)}"
                 for s in (AVAILABLE, TAKEN, INVALID, UNKNOWN) if statuses.count(s)]
        say(f"  {p.title:<24} " + ("  ".join(parts) if parts else "not checked"))

    everywhere, best = [], []
    for count, _, name, st in rows:
        checked = [s for s in st if s in FINAL]
        if checked and all(s == AVAILABLE for s in checked):
            everywhere.append(name)
        if count:
            best.append(f"  {name:<20} available on {count} of {len(checked)}")
    if everywhere:
        text = ", ".join(everywhere[:30])
        if len(everywhere) > 30:
            text += f" … and {len(everywhere) - 30} more (see the overview)"
        say(f"\n\033[92mAvailable everywhere\033[0m (on every platform that answered): {text}")
    if best:
        say("\nMost available:")
        for line in best[:15]:
            say(line)


def estimate_duration(names, platforms, store, factor) -> str:
    longest = 0.0
    for p in platforms:
        todo = sum(1 for n in names if not store.done(n, p))
        longest = max(longest, todo * (p.delay * factor + 0.6))
    return duration_text(longest)


def duration_text(seconds: float) -> str:
    if seconds < 60:
        return "less than a minute"
    if seconds < 5400:
        return f"about {round(seconds / 60)} minutes"
    return f"about {seconds / 3600:.1f} hours"


# ---------------------------------------------------------------------------
# New versions
# ---------------------------------------------------------------------------
# Through UserAtlas.exe the launcher handles updating: it fetches the latest
# app/ from GitHub on every start. When you run this script directly with
# Python, find_update() only checks whether app/info.json on GitHub has a
# higher version number.

def version_tuple(text: str) -> Tuple[int, ...]:
    """'v1.2.10' -> (1, 2, 10). Unreadable parts count as 0."""
    parts = []
    for piece in str(text).strip().lstrip("vV").split("."):
        digits = re.match(r"\d+", piece)
        parts.append(int(digits.group()) if digits else 0)
    while len(parts) < 3:
        parts.append(0)
    return tuple(parts)


def find_update(s, current: str = VERSION) -> Optional[dict]:
    """Returns {"version", "page"} if GitHub has a newer version, otherwise None."""
    r = s.get(f"https://raw.githubusercontent.com/{GITHUB_REPO}/main/app/info.json",
              timeout=TIMEOUT)
    if r.status_code == 404:
        return None
    r.raise_for_status()
    newer = str(r.json().get("version", ""))
    if version_tuple(newer) <= version_tuple(current):
        return None
    return {"version": newer, "page": f"https://github.com/{GITHUB_REPO}"}


# ---------------------------------------------------------------------------
# Window (tkinter ships with Python)
# ---------------------------------------------------------------------------

SPEEDS = [
    ("Normal", 1.0, "Recommended. Every platform gets its own safe pause."),
    ("Calm", 2.0, "Twice as slow. Useful when sites start saying 'slow down'."),
    ("Very calm", 4.0, "For very long lists, or when platforms keep refusing."),
]
GROUP_TITLES = {"gaming": "Gaming", "socials": "Socials", "other": "Other",
                "domains": "Domains"}
GROUP_HINTS = {
    "gaming": "Games and gaming chat",
    "socials": "Social networks",
    "other": "Code, streaming and music",
    "domains": "Websites, via the domain registry",
}

# Colors: black and purple
C = {
    "bg": "#09090D", "surface": "#101016", "card": "#14141C", "field": "#0D0D13",
    "border": "#23232F", "line": "#1C1C26", "hover": "#1B1B25",
    "text": "#ECECF3", "muted": "#9A9AB2", "faint": "#5F5F75",
    "accent": "#8B5CF6", "accent_dark": "#7C3AED", "accent_soft": "#211A38",
    "accent_text": "#C4B5FD", "accent_off": "#3A305C",
    "red": "#F87171", "red_soft": "#2A1418", "red_border": "#4A1D25",
    "green": "#4ADE80", "amber": "#FBBF24", "amber_soft": "#33270C",
    "row_free": "#0F2419", "selected": "#2A2145",
}
# Labels per platform in the detail panel: (background, text, symbol)
CHIP = {
    AVAILABLE: ("#0F2A1C", "#4ADE80", "✓"),
    TAKEN: ("#2C1418", "#F87171", "✗"),
    INVALID: ("#1E1A26", "#A1A1B5", "⊘"),
    UNKNOWN: ("#2E240C", "#FBBF24", "?"),
    "waiting": ("#211A38", "#A78BFA", "…"),
    "skipped": ("#17171F", "#5F5F75", "–"),
    "": ("#15151D", "#5F5F75", "·"),
}
CHIP_TEXT = {
    AVAILABLE: "available", TAKEN: "taken", INVALID: "not allowed",
    UNKNOWN: "unknown", "waiting": "still checking",
    "skipped": "skipped (failed the self-test)", "": "not checked yet",
}
SELFTEST_TEXT = {"works": "✓  works", "not working": "⚠  not working right now",
                 "busy": "…  testing", "": "not tested"}


def ensure_requests() -> bool:
    """Offers to install 'requests' in the window if it's missing."""
    global requests
    if requests is not None:
        return True
    if not messagebox.askyesno(
            "UserAtlas",
            "The 'requests' package is missing. Install it now?\n\n"
            "(This runs: python -m pip install requests)"):
        return False
    r = subprocess.run([sys.executable, "-m", "pip", "install", "requests"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        messagebox.showerror("UserAtlas", "Installing failed:\n\n"
                             + shorten(r.stderr or r.stdout, 600)
                             + "\n\nTry in a terminal: pip install requests")
        return False
    import importlib
    importlib.invalidate_caches()
    requests = importlib.import_module("requests")
    return True


def dark_title_bar(window):
    """Windows 10/11: make the window's title bar dark to match the app."""
    if os.name != "nt":
        return
    try:
        import ctypes
        window.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(window.winfo_id())
        value = ctypes.c_int(1)
        for attribute in (20, 19):  # DWMWA_USE_IMMERSIVE_DARK_MODE (new, old)
            if ctypes.windll.dwmapi.DwmSetWindowAttribute(
                    hwnd, attribute, ctypes.byref(value), ctypes.sizeof(value)) == 0:
                break
    except Exception:
        pass


def start_window() -> int:
    if tk is None:
        message = ("Tkinter is missing from this Python installation, so the window can't open.\n"
                   "Use the terminal version (python useratlas.py --help) or install Tkinter.")
        if is_app() and os.name == "nt":  # an .exe without a terminal: show a Windows message
            import ctypes
            ctypes.windll.user32.MessageBoxW(None, message, "UserAtlas", 0x10)
        else:
            print(message)
        return 1
    if os.name == "nt":
        try:  # sharp text on scaled displays
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    root = tk.Tk()
    root.withdraw()
    icon = resource_path("useratlas.ico")
    if os.name == "nt" and os.path.exists(icon):
        try:
            root.iconbitmap(default=icon)
        except tk.TclError:
            pass
    if not ensure_requests():
        root.destroy()
        return 1
    UserAtlasWindow(root)
    root.deiconify()
    dark_title_bar(root)
    root.mainloop()
    return 0


# Drawn checkboxes and radio buttons (anti-aliased with 4x4 subpixels)

def _rgb(color: str) -> Tuple[int, int, int]:
    return tuple(int(color[i:i + 2], 16) for i in (1, 3, 5))


def _segment_distance(px, py, ax, ay, bx, by) -> float:
    dx, dy = bx - ax, by - ay
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
    return math.hypot(px - ax - t * dx, py - ay - t * dy)


def _rounded_square_distance(px, py, n, r) -> float:
    """Negative inside a rounded n×n square (with half a pixel margin)."""
    middle, half = n / 2, n / 2 - 0.5 - r
    qx, qy = abs(px - middle) - half, abs(py - middle) - half
    return math.hypot(max(qx, 0), max(qy, 0)) + min(max(qx, qy), 0) - r


def _paint(master, n: int, paint) -> "tk.PhotoImage":
    image = tk.PhotoImage(master=master, width=n, height=n)
    rows = []
    for y in range(n):
        row = []
        for x in range(n):
            total = [0, 0, 0]
            for sy in range(4):
                for sx in range(4):
                    c = paint(x + (sx + 0.5) / 4, y + (sy + 0.5) / 4)
                    total[0] += c[0]
                    total[1] += c[1]
                    total[2] += c[2]
            row.append("#%02x%02x%02x" % (total[0] // 16, total[1] // 16, total[2] // 16))
        rows.append("{" + " ".join(row) + "}")
    image.put(" ".join(rows))
    return image


def draw_checkbox(master, n: int, background: str, fill: str, border: str,
                  checked: bool) -> "tk.PhotoImage":
    bg, fillc, borderc, white = _rgb(background), _rgb(fill), _rgb(border), (255, 255, 255)
    r, border_width = n * 0.26, max(1.0, n / 15)
    p = [(0.28 * n, 0.52 * n), (0.44 * n, 0.68 * n), (0.73 * n, 0.36 * n)]
    half_stroke = max(1.5, n * 0.13) / 2

    def paint(px, py):
        d = _rounded_square_distance(px, py, n, r)
        if d > 0:
            return bg
        if checked and min(_segment_distance(px, py, *p[0], *p[1]),
                           _segment_distance(px, py, *p[1], *p[2])) <= half_stroke:
            return white
        return borderc if d > -border_width else fillc

    return _paint(master, n, paint)


def draw_radio(master, n: int, background: str, fill: str, border: str, dot: Optional[str]):
    bg, fillc, borderc = _rgb(background), _rgb(fill), _rgb(border)
    dotc = _rgb(dot) if dot else None
    middle, radius, border_width = n / 2, n / 2 - 0.5, max(1.0, n / 14)

    def paint(px, py):
        d = math.hypot(px - middle, py - middle)
        if d > radius:
            return bg
        if dotc and d <= radius * 0.42:
            return dotc
        return borderc if d > radius - border_width else fillc

    return _paint(master, n, paint)


class Card:
    """Dark card with a thin border, optional title and hint."""

    def __init__(self, parent, title=None, hint=None, wrap=520, padding=(20, 16)):
        self.outer = tk.Frame(parent, bg=C["card"], highlightthickness=1,
                              highlightbackground=C["border"], highlightcolor=C["border"])
        inner = ttk.Frame(self.outer, style="Card.TFrame", padding=padding)
        inner.pack(fill="both", expand=True)
        self.head = ttk.Frame(inner, style="Card.TFrame")
        if title:
            self.head.pack(fill="x")
            ttk.Label(self.head, text=title, style="Heading.TLabel").pack(side="left")
        if hint:
            ttk.Label(inner, text=hint, style="Card.Muted.TLabel", wraplength=wrap,
                      justify="left").pack(anchor="w", pady=(3, 0))
        self.body = ttk.Frame(inner, style="Card.TFrame")
        self.body.pack(fill="both", expand=True, pady=(14 if (title or hint) else 0, 0))


class UserAtlasWindow:
    TABS = [("names", "Names"), ("platforms", "Platforms"), ("results", "Results"),
            ("selftest", "Self-test & log"), ("settings", "Settings")]

    def __init__(self, root):
        self.root = root
        self.folder = data_dir()
        self.log_path = os.path.join(self.folder, "results.csv")
        self.update_info: Optional[dict] = None
        self.events: "queue.Queue[tuple]" = queue.Queue()
        self.stop = threading.Event()
        self.busy = False
        self.phase = ""                # "selftest", "checking" or "stopping"
        self.mode = ""                 # "checking" or "selftest"
        self.store: Optional[Store] = None
        self.results: Dict[Tuple[str, str], Tuple[str, str]] = {}
        self.names: List[str] = []
        self.platforms: List[Platform] = []
        self.groups: List[str] = []    # groups in the current run
        self.headings: Dict[str, str] = {}
        self.skipped: set = set()
        self.remaining: Dict[str, int] = {}
        self.factor = 1.0
        self.done_count = 0
        self.total = 0
        self.last_status = 0.0
        self.sorting = ("available", False)
        self.selected: Optional[str] = None
        self.refresh_detail = False
        self.selftest_state: Dict[str, Tuple[str, str]] = {}
        self.current_tab = ""
        self.hidden: set = set()
        self.everything = all_platforms([])

        global _output
        _output = lambda t: self.events.put(("log", t))

        self.style()
        self.build()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.bind("<Control-Return>", lambda e: self.start())
        for i, (key, _) in enumerate(self.TABS, 1):
            self.root.bind(f"<Control-Key-{i}>", lambda e, k=key: self.show_tab(k))
        self.show_tab("names")
        self.update_summary()
        self.root.after(100, self.process)
        self.log(f"UserAtlas {VERSION}. Results are saved in {self.log_path}")
        if LAUNCHER and LAUNCHER.get("message"):
            self.log(LAUNCHER["message"])
            self.status.set(LAUNCHER["message"])
        # Through the launcher the app was just updated; after that, check every hour.
        first = 3_600_000 if (LAUNCHER and LAUNCHER.get("source") == "github") else 1500
        self.root.after(first, self.check_periodically)

    # ----- style ------------------------------------------------------------

    def style(self):
        base = tkfont.nametofont("TkDefaultFont")
        family = base.actual()["family"]
        size = max(10, abs(int(base.actual()["size"])) or 10)
        for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont"):
            try:
                tkfont.nametofont(name).configure(family=family, size=size)
            except tk.TclError:
                pass
        self.f = {
            "normal": (family, size), "bold": (family, size, "bold"), "small": (family, size - 1),
            "small_bold": (family, size - 1, "bold"), "heading": (family, size + 2, "bold"),
            "title": (family, size + 6, "bold"), "big": (family, size + 8, "bold"),
            "small_strike": (family, size - 1, "overstrike"),
        }
        s = ttk.Style(self.root)
        try:
            s.theme_use("clam")
        except tk.TclError:
            pass
        self.root.configure(background=C["bg"])
        self.root.option_add("*TCombobox*Listbox.background", C["field"])
        s.configure(".", background=C["bg"], foreground=C["text"], font=self.f["normal"],
                    bordercolor=C["border"], lightcolor=C["card"], darkcolor=C["card"],
                    troughcolor=C["line"], focuscolor=C["accent"],
                    selectbackground=C["selected"], selectforeground=C["text"],
                    insertcolor=C["text"], fieldbackground=C["field"])
        for prefix, bg in (("", C["bg"]), ("Card.", C["card"]), ("Bar.", C["surface"])):
            s.configure(f"{prefix}TFrame", background=bg)
            s.configure(f"{prefix}TLabel", background=bg, foreground=C["text"])
            s.configure(f"{prefix}Muted.TLabel", background=bg, foreground=C["muted"],
                        font=self.f["small"])
        s.configure("Heading.TLabel", background=C["card"], font=self.f["heading"])
        s.configure("Page.TLabel", background=C["bg"], font=self.f["heading"])
        s.configure("Title.TLabel", background=C["surface"], font=self.f["title"])
        s.configure("Big.TLabel", background=C["card"], font=self.f["big"])
        s.configure("Counter.TLabel", background=C["card"], foreground=C["accent_text"],
                    font=self.f["small_bold"])
        s.configure("Section.TLabel", background=C["card"], foreground=C["faint"],
                    font=self.f["small_bold"])

        # Buttons
        s.configure("TButton", background=C["card"], foreground=C["text"],
                    bordercolor="#2E2E3D", lightcolor=C["card"], darkcolor=C["card"],
                    padding=(14, 7), relief="solid", borderwidth=1, focusthickness=0,
                    focuscolor=C["card"])
        s.map("TButton",
              background=[("disabled", C["card"]), ("pressed", C["line"]), ("active", C["hover"])],
              bordercolor=[("disabled", C["border"]), ("active", "#3F3F52")],
              lightcolor=[("disabled", C["card"]), ("pressed", C["line"]), ("active", C["hover"])],
              darkcolor=[("disabled", C["card"]), ("pressed", C["line"]), ("active", C["hover"])],
              foreground=[("disabled", C["faint"])])
        s.configure("Accent.TButton", background=C["accent"], foreground="#FFFFFF",
                    bordercolor=C["accent"], lightcolor=C["accent"], darkcolor=C["accent"],
                    font=self.f["bold"], padding=(20, 8))
        s.map("Accent.TButton",
              background=[("disabled", C["accent_off"]), ("pressed", C["accent_dark"]),
                          ("active", C["accent_dark"])],
              bordercolor=[("disabled", C["accent_off"]), ("active", C["accent_dark"])],
              lightcolor=[("disabled", C["accent_off"]), ("active", C["accent_dark"])],
              darkcolor=[("disabled", C["accent_off"]), ("active", C["accent_dark"])],
              foreground=[("disabled", "#9C93BD")])
        s.configure("Stop.TButton", foreground=C["red"], background=C["red_soft"],
                    bordercolor=C["red_border"], lightcolor=C["red_soft"],
                    darkcolor=C["red_soft"], font=self.f["bold"], padding=(18, 8))
        s.map("Stop.TButton",
              foreground=[("disabled", C["faint"])],
              background=[("disabled", C["surface"]), ("active", "#3A1A20")],
              bordercolor=[("disabled", C["border"]), ("active", "#6B2632")],
              lightcolor=[("disabled", C["surface"]), ("active", "#3A1A20")],
              darkcolor=[("disabled", C["surface"]), ("active", "#3A1A20")])
        s.configure("Link.TButton", background=C["card"], foreground=C["accent_text"],
                    bordercolor=C["card"], lightcolor=C["card"], darkcolor=C["card"],
                    relief="flat", padding=(2, 1), width=0, font=self.f["small_bold"])
        s.map("Link.TButton",
              foreground=[("disabled", C["faint"]), ("active", "#DDD6FE")],
              background=[("active", C["card"]), ("pressed", C["card"])],
              bordercolor=[("active", C["card"])], lightcolor=[("active", C["card"])],
              darkcolor=[("active", C["card"])])

        # Checkboxes and radio buttons
        for kind in ("TCheckbutton", "TRadiobutton"):
            for prefix, bg in (("", C["bg"]), ("Card.", C["card"])):
                st = prefix + kind
                s.configure(st, background=bg, foreground=C["text"], padding=(0, 3),
                            focusthickness=0, indicatorbackground=C["field"],
                            indicatorforeground="#FFFFFF")
                s.map(st, background=[("active", bg)], foreground=[("disabled", C["faint"])])
        self.make_indicators(s)

        # Entry fields
        s.configure("TEntry", fieldbackground=C["field"], foreground=C["text"],
                    bordercolor=C["border"], lightcolor=C["field"], darkcolor=C["field"],
                    insertcolor=C["text"], padding=(8, 6))
        s.map("TEntry", bordercolor=[("focus", C["accent"])],
              lightcolor=[("focus", C["accent"])],
              fieldbackground=[("readonly", C["surface"])],
              foreground=[("readonly", C["muted"])])

        # Progress
        s.configure("Accent.Horizontal.TProgressbar", troughcolor=C["line"],
                    background=C["accent"], bordercolor=C["line"], lightcolor=C["accent"],
                    darkcolor=C["accent"], thickness=6)

        # Tables
        line = tkfont.Font(font=self.f["normal"]).metrics("linespace")
        s.configure("Treeview", background=C["card"], fieldbackground=C["card"],
                    foreground=C["text"], bordercolor=C["card"], lightcolor=C["card"],
                    darkcolor=C["card"], borderwidth=0, rowheight=int(line * 2.1))
        s.map("Treeview", background=[("selected", C["selected"])],
              foreground=[("selected", "#FFFFFF")])
        s.configure("Treeview.Heading", background=C["card"], foreground=C["faint"],
                    font=self.f["small_bold"], relief="flat", bordercolor=C["line"],
                    lightcolor=C["card"], darkcolor=C["line"], padding=(10, 8))
        s.map("Treeview.Heading", background=[("active", C["hover"])],
              foreground=[("active", C["muted"])])
        s.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])

        # Scrollbars
        for direction in ("Vertical", "Horizontal"):
            s.configure(f"{direction}.TScrollbar", background="#2A2A38", troughcolor=C["card"],
                        bordercolor=C["card"], lightcolor="#2A2A38", darkcolor="#2A2A38",
                        arrowcolor=C["muted"], gripcount=0, arrowsize=12)
            s.map(f"{direction}.TScrollbar", background=[("active", "#3A3A4C")],
                  lightcolor=[("active", "#3A3A4C")], darkcolor=[("active", "#3A3A4C")])

    def make_indicators(self, s):
        """Own rounded checkboxes and radio buttons in the accent color."""
        try:
            scale = float(self.root.tk.call("tk", "scaling"))  # pixels per point
        except (tk.TclError, ValueError):
            scale = 1.33
        n = max(14, round(12 * scale))
        gap = round(6 * scale)
        self.images = []
        for name, bg, check_style, radio_style in (
                ("Page", C["bg"], "TCheckbutton", "TRadiobutton"),
                ("Card", C["card"], "Card.TCheckbutton", "Card.TRadiobutton")):
            off = draw_checkbox(self.root, n, bg, C["field"], "#3A3A4C", False)
            on = draw_checkbox(self.root, n, bg, C["accent"], C["accent"], True)
            off_dim = draw_checkbox(self.root, n, bg, C["surface"], C["border"], False)
            on_dim = draw_checkbox(self.root, n, bg, C["accent_off"], C["accent_off"], True)
            r_off = draw_radio(self.root, n, bg, C["field"], "#3A3A4C", None)
            r_on = draw_radio(self.root, n, bg, C["field"], C["accent"], C["accent"])
            self.images += [off, on, off_dim, on_dim, r_off, r_on]
            for element, images, style, layout_name in (
                    (f"{name}Check.indicator", (off, on, off_dim, on_dim), check_style, "Checkbutton"),
                    (f"{name}Radio.indicator", (r_off, r_on, r_off, r_on), radio_style, "Radiobutton")):
                try:
                    s.element_create(element, "image", images[0],
                                     ("disabled", "selected", images[3]),
                                     ("disabled", images[2]), ("selected", images[1]),
                                     width=n + gap, sticky="w")
                except tk.TclError:
                    continue  # already exists (second window in the same session)
                s.layout(style, [(f"{layout_name}.padding", {"sticky": "nswe", "children": [
                    (element, {"side": "left", "sticky": ""}),
                    (f"{layout_name}.focus", {"side": "left", "sticky": "w", "children": [
                        (f"{layout_name}.label", {"sticky": "nswe"})]})]})])

    # ----- layout -----------------------------------------------------------

    def build(self):
        r = self.root
        r.title("UserAtlas")
        r.geometry("1240x820")
        r.minsize(1000, 660)
        r.columnconfigure(0, weight=1)
        r.rowconfigure(1, weight=1)

        # Header: logo, title, summary, Start/Stop and the tabs
        head = tk.Frame(r, bg=C["surface"])
        head.grid(row=0, column=0, sticky="ew")
        head.columnconfigure(0, weight=1)
        top = tk.Frame(head, bg=C["surface"])
        top.grid(row=0, column=0, sticky="ew", padx=24, pady=(16, 4))
        top.columnconfigure(1, weight=1)
        tk.Label(top, text="@", bg=C["accent"], fg="#FFFFFF", font=self.f["heading"],
                 width=2, pady=3).grid(row=0, column=0, sticky="w", padx=(0, 12))
        titles = tk.Frame(top, bg=C["surface"])
        titles.grid(row=0, column=1, sticky="w")
        ttk.Label(titles, text="UserAtlas", style="Title.TLabel").pack(anchor="w")
        ttk.Label(titles, text="Find out where your usernames are still available",
                  style="Bar.Muted.TLabel").pack(anchor="w")

        # "New version" notice (hidden until there is an update)
        self.update_pill = tk.Frame(top, bg=C["accent_soft"], cursor="hand2")
        self.update_text = tk.Label(self.update_pill, text="", bg=C["accent_soft"],
                                    fg=C["accent_text"], font=self.f["small"], cursor="hand2")
        self.update_text.pack(side="left", padx=(12, 6), pady=6)
        self.update_button = tk.Label(self.update_pill, text="Update", bg=C["accent_soft"],
                                      fg="#FFFFFF", font=self.f["small_bold"], cursor="hand2")
        self.update_button.pack(side="left", padx=(0, 12), pady=6)
        for w in (self.update_pill, self.update_text, self.update_button):
            w.bind("<Button-1>", lambda e: self.click_update())
        self.update_pill.grid(row=0, column=2, padx=(0, 16))
        self.update_pill.grid_remove()
        self.summary_text = tk.StringVar()
        ttk.Label(top, textvariable=self.summary_text,
                  style="Bar.Muted.TLabel").grid(row=0, column=3, padx=(0, 16))
        self.stop_button = ttk.Button(top, text="Stop", style="Stop.TButton",
                                      command=self.stopping, state="disabled")
        self.stop_button.grid(row=0, column=4, padx=(0, 8))
        self.start_button = ttk.Button(top, text="Start checking", style="Accent.TButton",
                                       command=self.start)
        self.start_button.grid(row=0, column=5)

        tab_row = tk.Frame(head, bg=C["surface"])
        tab_row.grid(row=1, column=0, sticky="ew", padx=14)
        self.tab_widgets = {}
        for key, title in self.TABS:
            t = tk.Frame(tab_row, bg=C["surface"], cursor="hand2")
            t.pack(side="left")
            row = tk.Frame(t, bg=C["surface"], cursor="hand2")
            row.pack(padx=12, pady=(8, 9))
            label = tk.Label(row, text=title, bg=C["surface"], fg=C["muted"],
                             font=self.f["bold"], cursor="hand2")
            label.pack(side="left")
            badge = tk.Label(row, text="", font=self.f["small_bold"], padx=6)
            underline = tk.Frame(t, bg=C["surface"], height=3)
            underline.pack(fill="x", side="bottom")
            for w in (t, row, label, badge):
                w.bind("<Button-1>", lambda e, k=key: self.show_tab(k))
                w.bind("<Enter>", lambda e, k=key: self.tab_hover(k, True))
                w.bind("<Leave>", lambda e, k=key: self.tab_hover(k, False))
            self.tab_widgets[key] = (label, underline, badge)
        tk.Frame(head, bg=C["border"], height=1).grid(row=2, column=0, sticky="ew")

        # Pages
        holder = ttk.Frame(r)
        holder.grid(row=1, column=0, sticky="nsew")
        holder.columnconfigure(0, weight=1)
        holder.rowconfigure(0, weight=1)
        self.pages = {}
        for key, _ in self.TABS:
            p = ttk.Frame(holder, padding=(24, 20))
            p.grid(row=0, column=0, sticky="nsew")
            self.pages[key] = p
        self.build_names(self.pages["names"])
        self.build_platforms(self.pages["platforms"])
        self.build_results(self.pages["results"])
        self.build_selftest(self.pages["selftest"])
        self.build_settings(self.pages["settings"])

        # Status bar
        tk.Frame(r, bg=C["border"], height=1).grid(row=2, column=0, sticky="ew")
        foot = tk.Frame(r, bg=C["surface"])
        foot.grid(row=3, column=0, sticky="ew")
        foot.columnconfigure(0, weight=1)
        self.status = tk.StringVar(value="Ready when you are.")
        ttk.Label(foot, textvariable=self.status, style="Bar.TLabel").grid(
            row=0, column=0, sticky="w", padx=24, pady=11)
        self.progress = ttk.Progressbar(foot, style="Accent.Horizontal.TProgressbar",
                                        mode="determinate", length=280)
        self.progress.grid(row=0, column=1, sticky="e", padx=24)

    def text_box(self, parent, height=None, font=None):
        """A dark multi-line text field with a border that lights up on focus."""
        border = tk.Frame(parent, bg=C["field"], highlightthickness=1,
                          highlightbackground=C["border"], highlightcolor=C["border"])
        box = tk.Text(border, wrap="none", undo=True, relief="flat", borderwidth=0,
                      highlightthickness=0, padx=14, pady=10, font=font or self.f["normal"],
                      bg=C["field"], fg=C["text"], insertbackground=C["text"],
                      selectbackground=C["selected"], selectforeground="#FFFFFF",
                      spacing1=3, spacing3=3)
        if height:
            box.configure(height=height)
        scroll = ttk.Scrollbar(border, orient="vertical", command=box.yview)
        box.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        box.pack(side="left", fill="both", expand=True)
        box.bind("<FocusIn>", lambda e: border.configure(highlightbackground=C["accent"]))
        box.bind("<FocusOut>", lambda e: border.configure(highlightbackground=C["border"]))
        return border, box

    # -- tab: Names

    def build_names(self, p):
        p.columnconfigure(0, weight=1)
        p.columnconfigure(1, weight=1)
        p.rowconfigure(0, weight=1)
        k = Card(p, "Names", "Type or paste the names you want to check, one per line.")
        k.outer.grid(row=0, column=0, sticky="nsew", padx=(0, 16))
        self.name_count = tk.StringVar(value="0 names")
        ttk.Label(k.head, textvariable=self.name_count, style="Counter.TLabel").pack(side="right")
        border, self.names_box = self.text_box(k.body)
        border.pack(fill="both", expand=True)
        self.names_box.bind("<<Modified>>", self.names_changed)

        buttons = ttk.Frame(k.body, style="Card.TFrame")
        buttons.pack(fill="x", pady=(12, 0))
        ttk.Button(buttons, text="Load file…", command=self.load_file).pack(side="left")
        ttk.Button(buttons, text="Paste", command=self.paste_names).pack(side="left", padx=(8, 0))
        ttk.Button(buttons, text="Clear", command=self.clear_names).pack(side="left", padx=(8, 0))
        ttk.Button(buttons, text="Next: platforms  →", style="Link.TButton",
                   command=lambda: self.show_tab("platforms")).pack(side="right")
        ttk.Label(k.body, style="Card.Muted.TLabel", wraplength=520, justify="left",
                  text="Tip: commas and spaces work too · an @ in front is removed · anything "
                       "after # is a note · Ctrl+Enter starts checking").pack(anchor="w", pady=(10, 0))

        # Live check against each site's naming rules (no internet needed)
        r = Card(p, "Name rules", "Is each name allowed by the sites you picked? Checked "
                                  "right away, before you start.", wrap=420)
        r.outer.grid(row=0, column=1, sticky="nsew")
        self.rules_count = tk.StringVar(value="")
        ttk.Label(r.head, textvariable=self.rules_count, style="Counter.TLabel").pack(side="right")
        box = ttk.Frame(r.body, style="Card.TFrame")
        box.pack(fill="both", expand=True)
        self.rules_table = ttk.Treeview(box, columns=("name", "allowed", "problem"),
                                        show="headings", selectmode="browse", height=8)
        for col, title, width, stretch, anchor in (("name", "NAME", 140, False, "w"),
                                                   ("allowed", "ALLOWED", 100, False, "center"),
                                                   ("problem", "WHY NOT", 220, True, "w")):
            self.rules_table.heading(col, text=title, anchor=anchor)
            self.rules_table.column(col, width=width, minwidth=60, stretch=stretch, anchor=anchor)
        self.rules_table.tag_configure("fits", foreground=C["green"])
        self.rules_table.tag_configure("issue", foreground=C["amber"])
        self.rules_table.tag_configure("blocked", foreground=C["red"])
        rs = ttk.Scrollbar(box, orient="vertical", command=self.rules_table.yview)
        self.rules_table.configure(yscrollcommand=rs.set)
        rs.pack(side="right", fill="y")
        self.rules_table.pack(side="left", fill="both", expand=True)
        self.rules_table.bind("<<TreeviewSelect>>", lambda e: self.show_rule_detail())
        self.rules_empty = ttk.Label(box, style="Card.Muted.TLabel", justify="center",
                                     text="Your names show up here as you type.")
        self.rules_empty.place(relx=0.5, rely=0.45, anchor="center")

        detail_border = tk.Frame(r.body, bg=C["field"], highlightthickness=1,
                                 highlightbackground=C["border"])
        detail_border.pack(fill="x", pady=(12, 0))
        self.rules_detail = tk.Text(detail_border, height=7, wrap="word", state="disabled",
                                    relief="flat", borderwidth=0, highlightthickness=0,
                                    padx=12, pady=8, font=self.f["small"], bg=C["field"],
                                    fg=C["text"], spacing1=2, spacing3=2,
                                    selectbackground=C["selected"])
        self.rules_detail.tag_configure("head", font=self.f["small_bold"], foreground="#FFFFFF")
        self.rules_detail.tag_configure("site", foreground=C["accent_text"])
        self.rules_detail.tag_configure("ok", foreground=C["green"])
        self.rules_detail.tag_configure("muted", foreground=C["muted"])
        self.rules_detail.tag_configure("blocked", foreground=C["red"])
        self.rules_detail.pack(fill="both", expand=True)
        self.rules_after = None
        self.show_rule_detail()

    # -- tab: Platforms

    def build_platforms(self, p):
        self.platform_hint_default = ("Hover a platform to see its name rules. Instagram, TikTok "
                                      "and X don't like automated checks and sometimes drop out; "
                                      "the self-test notices this and skips them.")
        self.platform_hint = tk.StringVar(value=self.platform_hint_default)
        top = ttk.Frame(p)
        top.pack(fill="x", pady=(0, 14))
        self.platform_count = tk.StringVar()
        ttk.Label(top, textvariable=self.platform_count, style="Page.TLabel").pack(side="left")
        ttk.Button(top, text="None", command=lambda: self.set_all(False)).pack(side="right")
        ttk.Button(top, text="All", command=lambda: self.set_all(True)).pack(
            side="right", padx=(0, 8))

        grid = ttk.Frame(p)
        grid.pack(fill="x")
        self.checks: Dict[str, tk.BooleanVar] = {}
        self.group_counts: Dict[str, tk.StringVar] = {}
        for col, group in enumerate(GROUPS):
            grid.columnconfigure(col, weight=1, uniform="group")
            k = Card(grid, GROUP_TITLES[group], GROUP_HINTS[group], wrap=200)
            k.outer.grid(row=0, column=col, sticky="nsew", padx=(0 if col == 0 else 14, 0))
            counter = tk.StringVar()
            self.group_counts[group] = counter
            ttk.Label(k.head, textvariable=counter, style="Counter.TLabel").pack(side="right")
            if group == "domains":
                domain_rules = all_platforms(["com"])[-1].rules.describe()
                items = [(f"domain.{t}", f".{t}", f".{t} domains: {domain_rules}")
                         for t in split_list(STANDARD_TLDS)]
            else:
                items = [(q.key, q.short_title, f"{q.short_title} names: {q.rules.describe()}")
                         for q in self.everything if q.group == group]
            for key, text, rule_text in items:
                v = tk.BooleanVar(value=True)
                v.trace_add("write", lambda *_: self.update_summary())
                self.checks[key] = v
                box = ttk.Checkbutton(k.body, text=text, variable=v, style="Card.TCheckbutton")
                box.pack(anchor="w")
                box.bind("<Enter>", lambda e, t=rule_text: self.platform_hint.set(t))
                box.bind("<Leave>", lambda e: self.platform_hint.set(self.platform_hint_default))
            if group == "domains":
                ttk.Label(k.body, text="Other extensions", style="Card.TLabel").pack(
                    anchor="w", pady=(12, 4))
                self.extra_tlds = tk.StringVar()
                self.extra_tlds.trace_add("write", lambda *_: self.update_summary())
                ttk.Entry(k.body, textvariable=self.extra_tlds).pack(fill="x")
                ttk.Label(k.body, text="For example: de, be, app",
                          style="Card.Muted.TLabel").pack(anchor="w", pady=(4, 0))
            foot = ttk.Frame(k.body, style="Card.TFrame")
            foot.pack(fill="x", side="bottom", pady=(14, 0))
            ttk.Button(foot, text="All", style="Link.TButton",
                       command=lambda g=group: self.set_group(g, True)).pack(side="left")
            ttk.Label(foot, text="·", style="Card.Muted.TLabel").pack(side="left", padx=2)
            ttk.Button(foot, text="None", style="Link.TButton",
                       command=lambda g=group: self.set_group(g, False)).pack(side="left")

        ttk.Label(p, textvariable=self.platform_hint, style="Muted.TLabel", wraplength=1100,
                  justify="left").pack(anchor="w", pady=(14, 0))

    # -- tab: Results

    def build_results(self, p):
        p.columnconfigure(0, weight=1)
        p.columnconfigure(1, minsize=370)
        p.rowconfigure(1, weight=1)

        bar = ttk.Frame(p)
        bar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 14))
        ttk.Label(bar, text="Search").pack(side="left", padx=(0, 8))
        self.search = tk.StringVar()
        self.search.trace_add("write", lambda *_: self.show())
        ttk.Entry(bar, textvariable=self.search, width=24).pack(side="left")
        self.only_available = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar, text="Only names that are available somewhere",
                        variable=self.only_available, command=self.show).pack(side="left", padx=(20, 0))
        ttk.Button(bar, text="Save overview…", command=self.export).pack(side="right")

        left = Card(p, padding=(2, 2))
        left.outer.grid(row=1, column=0, sticky="nsew", padx=(0, 16))
        self.table = ttk.Treeview(left.body, show="headings", selectmode="browse")
        ys = ttk.Scrollbar(left.body, orient="vertical", command=self.table.yview)
        self.table.configure(yscrollcommand=ys.set)
        ys.pack(side="right", fill="y")
        self.table.pack(side="left", fill="both", expand=True)
        self.table.tag_configure("allavailable", background=C["row_free"])
        self.table.tag_configure("noneavailable", foreground=C["faint"])
        self.table.bind("<<TreeviewSelect>>", self.selection)
        self.empty = ttk.Label(left.body, style="Card.Muted.TLabel", justify="center",
                               text="No results yet.\n"
                                    "Enter names and press 'Start checking'.")
        self.empty.place(relx=0.5, rely=0.42, anchor="center")

        right = Card(p)
        right.outer.grid(row=1, column=1, sticky="nsew")
        self.detail = right.body
        self.build_table([], [])
        self.show_detail(None)

    # -- tab: Self-test & log

    def build_selftest(self, p):
        p.columnconfigure(0, weight=1)
        p.rowconfigure(0, weight=3)
        p.rowconfigure(1, weight=2)
        k = Card(p, "Self-test",
                 "Per platform we check a known name (which must be taken) and a random name "
                 "(which must be available). If that doesn't add up, the platform is skipped, "
                 "so you never get a false 'available'.", wrap=820)
        k.outer.grid(row=0, column=0, sticky="nsew", pady=(0, 16))
        self.test_button = ttk.Button(k.head, text="Run self-test now",
                                      command=lambda: self.start(only_selftest=True))
        self.test_button.pack(side="right")
        box = ttk.Frame(k.body, style="Card.TFrame")
        box.pack(fill="both", expand=True)
        self.test_table = ttk.Treeview(box, columns=("platform", "group", "state", "why"),
                                       show="headings", selectmode="none", height=6)
        for col, title, width, stretch in (("platform", "PLATFORM", 200, False),
                                           ("group", "GROUP", 120, False),
                                           ("state", "STATUS", 190, False),
                                           ("why", "DETAILS", 300, True)):
            self.test_table.heading(col, text=title, anchor="w")
            self.test_table.column(col, width=width, stretch=stretch, anchor="w")
        self.test_table.tag_configure("works", foreground=C["text"])
        self.test_table.tag_configure("not working", foreground=C["amber"])
        self.test_table.tag_configure("busy", foreground=C["accent_text"])
        self.test_table.tag_configure("", foreground=C["faint"])
        ts = ttk.Scrollbar(box, orient="vertical", command=self.test_table.yview)
        self.test_table.configure(yscrollcommand=ts.set)
        ts.pack(side="right", fill="y")
        self.test_table.pack(side="left", fill="both", expand=True)

        m = Card(p, "Log")
        m.outer.grid(row=1, column=0, sticky="nsew")
        ttk.Button(m.head, text="Clear", style="Link.TButton", command=self.clear_log).pack(side="right")
        self.log_box = tk.Text(m.body, height=5, wrap="word", state="disabled", relief="flat",
                               borderwidth=0, highlightthickness=0, font=self.f["small"],
                               bg=C["card"], fg=C["text"], spacing1=2, spacing3=2,
                               selectbackground=C["selected"])
        self.log_box.tag_configure("time", foreground=C["faint"])
        ls = ttk.Scrollbar(m.body, orient="vertical", command=self.log_box.yview)
        self.log_box.configure(yscrollcommand=ls.set)
        ls.pack(side="right", fill="y")
        self.log_box.pack(side="left", fill="both", expand=True)

    # -- tab: Settings

    def build_settings(self, p):
        p.columnconfigure(0, weight=1, uniform="settings")
        p.columnconfigure(1, weight=1, uniform="settings")
        t = Card(p, "Speed", "The calmer, the smaller the chance a site temporarily "
                             "blocks you.", wrap=440)
        t.outer.grid(row=0, column=0, sticky="nsew", padx=(0, 16), pady=(0, 16))
        self.speed = tk.DoubleVar(value=1.0)
        for title, factor, hint in SPEEDS:
            ttk.Radiobutton(t.body, text=title, value=factor, variable=self.speed,
                            style="Card.TRadiobutton").pack(anchor="w")
            ttk.Label(t.body, text=hint, style="Card.Muted.TLabel", wraplength=420,
                      justify="left").pack(anchor="w", padx=(27, 0), pady=(0, 8))

        s = Card(p, "When starting")
        s.outer.grid(row=0, column=1, sticky="nsew", pady=(0, 16))
        self.selftest_on = tk.BooleanVar(value=True)
        self.recheck = tk.BooleanVar(value=False)
        for var, title, hint in (
                (self.selftest_on, "Run a self-test first",
                 "Recommended. Platforms that don't answer properly right now are skipped."),
                (self.recheck, "Check earlier results again",
                 "By default, names that were already checked are not checked again.")):
            ttk.Checkbutton(s.body, text=title, variable=var,
                            style="Card.TCheckbutton").pack(anchor="w")
            ttk.Label(s.body, text=hint, style="Card.Muted.TLabel", wraplength=420,
                      justify="left").pack(anchor="w", padx=(27, 0), pady=(0, 8))

        o = Card(p, "Storage", "Every result is saved right away. Stop halfway and the next "
                               "run continues where you left off.", wrap=900)
        o.outer.grid(row=1, column=0, columnspan=2, sticky="nsew", pady=(0, 16))
        row = ttk.Frame(o.body, style="Card.TFrame")
        row.pack(fill="x")
        field_ = ttk.Entry(row)
        field_.insert(0, self.log_path)
        field_.configure(state="readonly")
        field_.pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Open folder", command=self.open_folder).pack(side="left", padx=(8, 0))

        v = Card(p, "Version")
        v.outer.grid(row=2, column=0, columnspan=2, sticky="nsew", pady=(0, 16))
        row = ttk.Frame(v.body, style="Card.TFrame")
        row.pack(fill="x")
        ttk.Label(row, text=f"UserAtlas {VERSION}", style="Card.TLabel",
                  font=self.f["bold"]).pack(side="left")
        if LAUNCHER:
            origin = ("just fetched from GitHub" if LAUNCHER.get("source") == "github"
                      else "offline copy")
            below = f"app {str(LAUNCHER.get('commit', ''))[:7]} · {origin}"
        else:
            below = "plain script"
        ttk.Label(row, text=below, style="Card.Muted.TLabel").pack(side="left", padx=(12, 0))
        self.update_status = tk.StringVar(value="")
        ttk.Label(row, textvariable=self.update_status,
                  style="Card.Muted.TLabel").pack(side="left", padx=(12, 0))
        ttk.Button(row, text="View on GitHub", style="Link.TButton",
                   command=lambda: webbrowser.open(f"https://github.com/{GITHUB_REPO}")
                   ).pack(side="right")
        self.check_button = ttk.Button(row, text="Check for updates",
                                       command=lambda: self.check_updates(manual=True))
        self.check_button.pack(side="right", padx=(0, 12))

        w = Card(p, "Good to know")
        w.outer.grid(row=3, column=0, columnspan=2, sticky="nsew")
        ttk.Label(w.body, style="Card.TLabel", wraplength=900, justify="left",
                  text="'Available' means no account or registration was found. Some names "
                       "are still blocked or reserved; you'll only find out when claiming. "
                       "Click a platform in the Results tab to go straight to the right page."
                  ).pack(anchor="w")

    # ----- tabs -------------------------------------------------------------

    def show_tab(self, key):
        self.current_tab = key
        self.pages[key].tkraise()
        for k, (label, underline, _) in self.tab_widgets.items():
            active = k == key
            label.configure(fg="#FFFFFF" if active else C["muted"])
            underline.configure(bg=C["accent"] if active else C["surface"])
        if key == "selftest" and not self.busy:
            self.fill_test_table(self.chosen_platforms(quiet=True))

    def tab_hover(self, key, inside):
        if key != self.current_tab:
            self.tab_widgets[key][0].configure(fg=C["text"] if inside else C["muted"])

    def set_badge(self, key, text, warning=False):
        badge = self.tab_widgets[key][2]
        if text:
            badge.configure(text=text, bg=C["amber_soft"] if warning else C["accent_soft"],
                            fg=C["amber"] if warning else C["accent_text"])
            badge.pack(side="left", padx=(8, 0))
        else:
            badge.pack_forget()

    # ----- names and platforms ----------------------------------------------

    def load_file(self):
        path = filedialog.askopenfilename(
            title="Choose a list of names",
            filetypes=[("Text or CSV", "*.txt *.csv"), ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8-sig") as fh:
                text = fh.read()
        except UnicodeDecodeError:
            with open(path, encoding="latin-1") as fh:
                text = fh.read()
        self.add_names(names_from_text(text), os.path.basename(path))

    def paste_names(self):
        try:
            text = self.root.clipboard_get()
        except tk.TclError:
            return
        self.add_names(names_from_text(text), "the clipboard")

    def add_names(self, names, source):
        existing = self.names_box.get("1.0", "end").strip()
        self.names_box.insert("end", ("\n" if existing else "") + "\n".join(names))
        self.update_summary()
        self.log(f"Added {len(names)} names from {source}")

    def clear_names(self):
        self.names_box.delete("1.0", "end")
        self.update_summary()

    def names_changed(self, _=None):
        if self.names_box.edit_modified():
            self.update_summary()
            self.names_box.edit_modified(False)

    def group_keys(self, group):
        if group == "domains":
            return [k for k in self.checks if k.startswith("domain.")]
        return [q.key for q in self.everything if q.group == group]

    def set_group(self, group, on):
        for k in self.group_keys(group):
            self.checks[k].set(on)

    def set_all(self, on):
        for v in self.checks.values():
            v.set(on)

    def extra_extensions(self, quiet=False) -> List[str]:
        extra = split_list(self.extra_tlds.get().replace(" ", ","))
        good = [t for t in extra if re.fullmatch(r"[a-z0-9-]{2,63}", t)]
        if not quiet and len(good) < len(extra):
            wrong = [t for t in extra if t not in good]
            self.log(f"Ignored (not a valid extension): {', '.join(wrong)}")
        return good

    def chosen_platforms(self, quiet=False) -> List[Platform]:
        tlds = [k.split(".", 1)[1] for k, v in self.checks.items()
                if k.startswith("domain.") and v.get()]
        tlds = list(dict.fromkeys(tlds + self.extra_extensions(quiet)))
        return [q for q in all_platforms(tlds)
                if q.group == "domains" or self.checks[q.key].get()]

    def update_summary(self):
        n = len(names_from_text(self.names_box.get("1.0", "end")))
        self.name_count.set(f"{n} {'name' if n == 1 else 'names'}")
        extra = self.extra_extensions(quiet=True)
        total = 0
        for group in GROUPS:
            keys = self.group_keys(group)
            on = sum(1 for k in keys if self.checks[k].get())
            if group == "domains":
                new_extra = [t for t in extra if f"domain.{t}" not in self.checks
                             or not self.checks[f"domain.{t}"].get()]
                on += len(dict.fromkeys(new_extra))
                self.group_counts[group].set(f"{on} selected")
            else:
                self.group_counts[group].set(f"{on} / {len(keys)}")
            total += on
        self.platform_count.set(f"{total} {'platform' if total == 1 else 'platforms'} selected")
        self.summary_text.set(f"{n} {'name' if n == 1 else 'names'}   ·   "
                              f"{total} {'platform' if total == 1 else 'platforms'}")
        if getattr(self, "rules_table", None) is not None:
            if self.rules_after:
                self.root.after_cancel(self.rules_after)
            self.rules_after = self.root.after(250, self.refresh_rules)

    # ----- name rules -------------------------------------------------------

    def refresh_rules(self):
        """Checks every name against the chosen platforms' naming rules."""
        self.rules_after = None
        names = names_from_text(self.names_box.get("1.0", "end"))[:1000]
        platforms = self.chosen_platforms(quiet=True)
        selected = self.rules_table.selection()
        self.rules_table.delete(*self.rules_table.get_children())
        self.rules_cache = {}
        rows = []
        blocked_total = 0
        for i, name in enumerate(names):
            broken = [(q, q.problem(name)) for q in platforms]
            broken = [(q, why) for q, why in broken if why]
            bad_word = BLOCKLIST.blocked(name.lower()) or BLOCKLIST.blocked(name)
            if bad_word:
                blocked_total += 1
            self.rules_cache[name.lower()] = (name, broken, len(platforms), bad_word)
            rows.append((-len(broken), i, name, broken, bad_word))
        rows.sort(key=lambda r: (r[0] == 0, r[0], r[1]))  # names with problems first
        for _, _, name, broken, bad_word in rows:
            if bad_word:
                first = "blocked word — rejected by most sites"
                tag = "blocked"
            elif broken:
                q, why = broken[0]
                first = f"{q.short_title}: {why}"
                if len(broken) > 1:
                    first += f"  (+{len(broken) - 1} more)"
                tag = "issue"
            else:
                first = "allowed everywhere"
                tag = "fits"
            self.rules_table.insert("", "end", iid=name.lower(), tags=(tag,),
                                    values=(name, f"{len(platforms) - len(broken)} / {len(platforms)}",
                                            first))
        with_issues = sum(1 for r in rows if r[3])
        if not names:
            self.rules_count.set("")
            self.rules_empty.place(relx=0.5, rely=0.45, anchor="center")
        else:
            self.rules_empty.place_forget()
            if blocked_total:
                self.rules_count.set(f"{blocked_total} blocked word"
                                     + ("s" if blocked_total != 1 else ""))
            else:
                self.rules_count.set(f"{with_issues} with problems" if with_issues else "all allowed")
        if selected and self.rules_table.exists(selected[0]):
            self.rules_table.selection_set(selected[0])
        self.show_rule_detail()

    def show_rule_detail(self):
        box = self.rules_detail
        box.configure(state="normal")
        box.delete("1.0", "end")
        sel = self.rules_table.selection()
        entry = getattr(self, "rules_cache", {}).get(sel[0]) if sel else None
        if not entry:
            box.insert("end", "Pick a name above to see which sites don't allow it, and why. "
                              "Names that break a site's rules are marked 'not allowed' there "
                              "and aren't sent to that site.", ("muted",))
        else:
            name, broken, total, bad_word = entry
            box.insert("end", f"{name}", ("head",))
            if bad_word:
                box.insert("end", "  contains a blocked word (a slur or strong profanity). "
                                  "Most gaming and social sites reject names like this at sign-up, "
                                  "so it's marked not allowed there. Domains and code sites "
                                  "(GitHub, GitLab) don't filter words.", ("blocked",))
            elif not broken:
                box.insert("end", f"  fits the rules of all {total} chosen sites.", ("ok",))
            else:
                box.insert("end", f"  isn't allowed on {len(broken)} of {total} sites:\n", ("muted",))
                for q, why in broken:
                    box.insert("end", f"{q.title}", ("site",))
                    box.insert("end", f"   {why}\n")
        box.configure(state="disabled")

    # ----- start and stop ---------------------------------------------------

    def start(self, only_selftest: bool = False):
        if self.busy:
            return
        platforms = self.chosen_platforms()
        if not platforms:
            messagebox.showinfo("UserAtlas", "Select at least one platform under Platforms.")
            self.show_tab("platforms")
            return
        names = names_from_text(self.names_box.get("1.0", "end"))
        if not only_selftest and not names:
            messagebox.showinfo("UserAtlas", "Enter one or more names first.")
            self.show_tab("names")
            return

        self.stop = threading.Event()
        self.factor = float(self.speed.get() or 1.0)

        if only_selftest:
            self.mode = "selftest"
            self.set_busy(True, "selftest")
            self.status.set("Running self-test…")
            self.fill_test_table(platforms, busy=True)
            self.show_tab("selftest")
            threading.Thread(target=self.director_selftest, args=(platforms, self.stop),
                             daemon=True).start()
            return

        try:
            store = Store(self.log_path, fresh=False, quiet=True,
                          on_result=lambda *r: self.events.put(("result",) + r))
        except OSError as e:
            messagebox.showerror("UserAtlas", f"Can't open {self.log_path}:\n{e}")
            return
        self.store = store
        self.mode = "checking"
        recheck = self.recheck.get()
        self.names, self.platforms = names, platforms
        self.skipped = set()
        self.results = {}
        if not recheck:
            for name in names:
                for q in platforms:
                    r = store.results.get((name.lower(), q.key))
                    if r and r[0] in FINAL:
                        self.results[(name.lower(), q.key)] = r
        self.remaining = {q.key: sum(1 for n in names if (n.lower(), q.key) not in self.results)
                          for q in platforms}
        self.done_count = 0
        self.total = sum(self.remaining.values())
        selftest = self.selftest_on.get()
        self.set_busy(True, "selftest" if selftest else "checking")
        self.build_table(names, platforms)
        self.show()
        self.show_detail(None)
        self.show_tab("results")
        if self.results:
            self.log(f"Reused {len(self.results)} earlier results (turn on 'Check earlier "
                     f"results again' in Settings to redo them).")
        if self.total == 0:
            self.log("Everything has been checked already.")
            self.finished("done")
            return
        todo = [q for q in platforms if self.remaining[q.key] > 0]
        if selftest:
            self.fill_test_table(todo, busy=True)
        self.status.set("Running self-test…" if selftest else "Working…")
        threading.Thread(target=self.director, daemon=True,
                         args=(names, todo, store, self.stop, self.factor,
                               selftest, not recheck)).start()

    def set_busy(self, busy: bool, phase: str = ""):
        self.busy, self.phase = busy, phase
        self.start_button.configure(state="disabled" if busy else "normal",
                                    text="Working…" if busy else "Start checking")
        self.test_button.configure(state="disabled" if busy else "normal")
        self.stop_button.configure(state="normal" if busy else "disabled")
        if busy and phase == "selftest":
            self.progress.configure(mode="indeterminate")
            self.progress.start(12)
        else:
            self.progress.stop()
            self.progress.configure(mode="determinate")

    def stopping(self):
        if not self.busy:
            return
        self.stop.set()
        self.phase = "stopping"
        self.stop_button.configure(state="disabled")
        self.status.set("Stopping… running checks are finishing up.")

    def close(self):
        if self.busy and not messagebox.askyesno(
                "UserAtlas", "Still checking. Stop and close?\n\n"
                             "Everything checked so far is saved."):
            return
        self.stop.set()
        if self.store:
            self.store.close()
        global _output
        _output = None
        self.root.destroy()

    # ----- background (does not run in the window thread) -------------------

    def run_selftest(self, platforms, stop):
        self.events.put(("log", "Self-test started…"))
        outcome = {}

        def run(q):
            ok, why = test_platform(q, stop)
            outcome[q.key] = (ok, why)
            self.events.put(("selftest", q.key, q.title, ok, why))

        threads = [threading.Thread(target=run, args=(q,), daemon=True) for q in platforms]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        return outcome

    def director_selftest(self, platforms, stop):
        try:
            outcome = self.run_selftest(platforms, stop)
            works = sum(1 for ok, _ in outcome.values() if ok)
            self.events.put(("log", f"Self-test done: {works} of {len(platforms)} "
                                    f"platforms work."))
        except Exception as e:
            self.events.put(("log", f"Error in self-test: {type(e).__name__}: {e}"))
        self.events.put(("finished", "selftest"))

    def director(self, names, platforms, store, stop, factor, selftest, reuse):
        try:
            if selftest:
                outcome = self.run_selftest(platforms, stop)
                platforms = [q for q in platforms if outcome.get(q.key, (False, ""))[0]]
            if stop.is_set():
                self.events.put(("finished", "stopped"))
                return
            self.events.put(("checks_started", len(platforms)))
            threads = [threading.Thread(target=worker, daemon=True,
                                        args=(q, names, store, stop, factor, reuse))
                       for q in platforms]
            for t in threads:
                t.start()
            for t in threads:
                t.join()
            self.events.put(("finished", "stopped" if stop.is_set() else "done"))
        except Exception as e:
            self.events.put(("log", f"Something went wrong: {type(e).__name__}: {e}"))
            self.events.put(("finished", "error"))

    # ----- handling messages from the background ----------------------------

    def process(self):
        try:
            for _ in range(500):
                message = self.events.get_nowait()
                getattr(self, "on_" + message[0])(*message[1:])
        except queue.Empty:
            pass
        if self.refresh_detail:
            self.refresh_detail = False
            self.show_detail(self.selected)
        if self.busy and self.phase == "checking" and time.time() - self.last_status > 0.5:
            self.last_status = time.time()
            rest = max((self.remaining.get(q.key, 0) * (q.delay * self.factor + 0.6)
                        for q in self.platforms if q.key not in self.skipped), default=0)
            self.status.set(f"{self.done_count} of {self.total} checks done   ·   "
                            f"{duration_text(rest)} to go")
        self.root.after(100, self.process)

    def on_log(self, text):
        if text.strip():
            self.log(text.strip())

    def on_result(self, name, key, status, detail):
        if self.mode != "checking":
            return
        self.results[(name.lower(), key)] = (status, detail)
        if self.remaining.get(key, 0) > 0:
            self.remaining[key] -= 1
        self.done_count += 1
        self.progress["value"] = self.done_count
        self.update_row(name)
        if self.selected and name.lower() == self.selected.lower():
            self.refresh_detail = True

    def on_selftest(self, key, title, ok, why):
        if why == "stopped":
            self.selftest_state[key] = ("", "")
        else:
            self.selftest_state[key] = ("works", "") if ok else ("not working", why)
        self.update_test_row(key)
        failing = sum(1 for st, _ in self.selftest_state.values() if st == "not working")
        self.set_badge("selftest", f"⚠ {failing}" if failing else "", warning=True)
        if ok or why == "stopped":
            return
        self.log(f"{title} is not working right now ({why}), skipping it.")
        if self.mode == "checking" and key in self.remaining:
            self.skipped.add(key)
            self.total -= self.remaining[key]
            self.remaining[key] = 0
            for name in self.names:
                self.update_row(name)
            self.refresh_detail = True

    def on_checks_started(self, platform_count):
        self.set_busy(True, "checking")
        self.progress.configure(maximum=max(1, self.total), value=self.done_count)
        if platform_count == 0:
            self.log("No platform is working right now. Try again later.")
        else:
            self.log(f"Checking started on {platform_count} platforms.")
        self.refresh_rows()

    def on_finished(self, reason):
        self.finished(reason)

    def finished(self, reason):
        if self.store:
            self.store.close()
            self.store = None
        self.set_busy(False)
        if self.mode == "selftest":
            self.status.set("Self-test done. See the Self-test & log tab.")
            return
        self.refresh_rows()
        self.show()
        self.show_detail(self.selected)
        everywhere = [n for n in self.names if self.available_everywhere(n)]
        somewhere = sum(1 for n in self.names if self.available_count(n))
        if reason == "stopped":
            text = "Stopped. Press Start to continue; everything checked so far is saved."
        elif reason == "error":
            text = "Stopped because of an error, see the Self-test & log tab."
        else:
            self.progress["value"] = self.progress["maximum"]
            text = (f"Done. {len(everywhere)} of {len(self.names)} names "
                    f"{'is' if len(everywhere) == 1 else 'are'} available everywhere, "
                    f"{somewhere} {'is' if somewhere == 1 else 'are'} available somewhere.")
        self.status.set(text)
        self.log(text)
        if everywhere:
            self.log("Available everywhere: " + ", ".join(everywhere[:40])
                     + (" …" if len(everywhere) > 40 else ""))

    # ----- results ----------------------------------------------------------

    def active_platforms(self, group: Optional[str] = None) -> List[Platform]:
        return [q for q in self.platforms if q.key not in self.skipped
                and (group is None or q.group == group)]

    def status_of(self, name, q) -> str:
        return self.results.get((name.lower(), q.key), ("", ""))[0]

    def available_count(self, name, group: Optional[str] = None) -> int:
        return sum(1 for q in self.active_platforms(group) if self.status_of(name, q) == AVAILABLE)

    def available_everywhere(self, name) -> bool:
        """Available on every platform that answered, and every platform has been checked."""
        st = [self.status_of(name, q) for q in self.active_platforms()]
        checked = [s for s in st if s in FINAL]
        return bool(checked) and all(st) and all(s == AVAILABLE for s in checked)

    def build_table(self, names, platforms):
        self.groups = [g for g in GROUPS if any(q.group == g for q in platforms)]
        cols = ["name", "available", "allowed"] + self.groups
        self.table.delete(*self.table.get_children())
        self.hidden = set()
        self.table.configure(columns=cols, displaycolumns=cols)
        self.headings = {"name": "NAME", "available": "AVAILABLE", "allowed": "ALLOWED"}
        self.table.column("name", width=180, minwidth=110, stretch=True, anchor="w")
        self.table.column("available", width=100, minwidth=80, stretch=True, anchor="center")
        self.table.column("allowed", width=90, minwidth=74, stretch=True, anchor="center")
        for g in self.groups:
            self.headings[g] = GROUP_TITLES[g].upper()
            self.table.column(g, width=90, minwidth=74, stretch=True, anchor="center")
        for col in cols:
            self.table.heading(col, anchor="w" if col == "name" else "center",
                               command=lambda c=col: self.sort_by(c))
        self.update_headings()
        for name in names:
            self.table.insert("", "end", iid=name.lower(), values=self.row_values(name),
                              tags=self.row_tags(name))
        if names:
            self.empty.place_forget()
        else:
            self.empty.place(relx=0.5, rely=0.42, anchor="center")

    def update_headings(self):
        col_s, reverse = self.sorting
        for col, text in self.headings.items():
            if col == col_s:
                text += "  ▴" if reverse else "  ▾"
            self.table.heading(col, text=text)

    def count_text(self, name, platforms) -> str:
        """'3 / 6' = available on 3 of 6; a trailing … means: not everything checked yet."""
        if not platforms:
            return "–"
        st = [self.status_of(name, q) for q in platforms]
        if not any(st):
            return "…" if self.busy else "–"
        return f"{st.count(AVAILABLE)} / {len(platforms)}" + ("" if all(st) else "  …")

    def allowed_count(self, name) -> int:
        """Platforms whose rules (and own answer) allow this name."""
        return sum(1 for q in self.active_platforms()
                   if self.status_of(name, q) != INVALID and not q.problem(name))

    def row_values(self, name):
        active = self.active_platforms()
        return ([name, self.count_text(name, active), f"{self.allowed_count(name)} / {len(active)}"]
                + [self.count_text(name, self.active_platforms(g)) for g in self.groups])

    def row_tags(self, name):
        st = [self.status_of(name, q) for q in self.active_platforms()]
        if not st or not all(st):
            return ()
        if self.available_everywhere(name):
            return ("allavailable",)
        if AVAILABLE not in st:
            return ("noneavailable",)
        return ()

    def update_row(self, name):
        iid = name.lower()
        if not self.table.exists(iid):
            return
        self.table.item(iid, values=self.row_values(name), tags=self.row_tags(name))
        if iid in self.hidden and self.visible(name):
            self.table.move(iid, "", "end")
            self.hidden.discard(iid)

    def refresh_rows(self):
        for name in self.names:
            self.update_row(name)

    def visible(self, name) -> bool:
        term = self.search.get().strip().lower()
        if term and term not in name.lower():
            return False
        return not (self.only_available.get() and self.available_count(name) == 0)

    def sort_by(self, col):
        col_s, reverse = self.sorting
        self.sorting = (col, not reverse if col == col_s else False)
        self.update_headings()
        self.show()

    def show(self):
        if not hasattr(self, "table"):
            return
        col, reverse = self.sorting

        def key(name):
            if col == "name":
                return name.lower()
            if col == "allowed":
                return -self.allowed_count(name)
            return -self.available_count(name, None if col == "available" else col)

        self.hidden = set()
        position = 0
        for name in sorted(self.names, key=key, reverse=reverse):
            iid = name.lower()
            if not self.table.exists(iid):
                continue
            if self.visible(name):
                self.table.move(iid, "", position)
                position += 1
            else:
                self.table.detach(iid)
                self.hidden.add(iid)

    def selection(self, _=None):
        sel = self.table.selection()
        if sel:
            self.show_detail(self.table.set(sel[0], "name"))

    def show_detail(self, name):
        # keep the scroll position when the same name is redrawn
        position = 0.0
        canvas = getattr(self, "detail_canvas", None)
        if canvas is not None and name and name == self.selected:
            try:
                position = canvas.yview()[0]
            except tk.TclError:
                pass
        self.detail_canvas = None
        for w in self.detail.winfo_children():
            w.destroy()
        self.selected = name
        if not name:
            ttk.Label(self.detail, text="Pick a name on the left", style="Heading.TLabel").pack(anchor="w")
            ttk.Label(self.detail, style="Card.Muted.TLabel", wraplength=330, justify="left",
                      text="You'll see per platform whether it's available. Click a platform "
                           "to open its page.").pack(anchor="w", pady=(4, 16))
            ttk.Label(self.detail, text="LEGEND", style="Section.TLabel").pack(anchor="w", pady=(0, 6))
            grid = ttk.Frame(self.detail, style="Card.TFrame")
            grid.pack(anchor="w")
            for i, (kind, text) in enumerate(((AVAILABLE, "available"), (TAKEN, "taken"),
                                              (INVALID, "not allowed"), (UNKNOWN, "unknown"),
                                              ("waiting", "checking"), ("skipped", "skipped"))):
                bg, fg, symbol = CHIP[kind]
                tk.Label(grid, text=f"{symbol}  {text}", bg=bg, fg=fg,
                         font=self.f["small_strike" if kind == INVALID else "small"],
                         padx=10, pady=5, anchor="w").grid(row=i // 3, column=i % 3, sticky="ew",
                                                          padx=(0, 6), pady=(0, 6))
            return

        head = ttk.Frame(self.detail, style="Card.TFrame")
        head.pack(fill="x")
        ttk.Label(head, text=name, style="Big.TLabel").pack(side="left")
        ttk.Button(head, text="Copy", style="Link.TButton",
                   command=lambda: self.copy(name)).pack(side="right")
        active = self.active_platforms()
        waiting = sum(1 for q in active if not self.status_of(name, q))
        sub = f"Available on {self.available_count(name)} of {len(active)} platforms"
        if waiting and self.busy:
            sub += f"   ·   {waiting} still checking"
        ttk.Label(self.detail, text=sub, style="Card.Muted.TLabel").pack(anchor="w", pady=(2, 4))

        # The hint sits at the bottom and is placed first, so it's always visible.
        default = "Hover a platform for details, click it to open its page."
        self.hint = tk.StringVar(value=default)
        ttk.Label(self.detail, textvariable=self.hint, style="Card.Muted.TLabel",
                  wraplength=340, justify="left").pack(side="bottom", anchor="w", pady=(10, 0))

        # The platforms sit in a scrollable area, for small windows or many extensions.
        holder = ttk.Frame(self.detail, style="Card.TFrame")
        holder.pack(fill="both", expand=True)
        canvas = tk.Canvas(holder, bg=C["card"], highlightthickness=0, borderwidth=0)
        scroll = ttk.Scrollbar(holder, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True)
        inner = ttk.Frame(canvas, style="Card.TFrame")
        window_id = canvas.create_window(0, 0, window=inner, anchor="nw")
        self.detail_canvas = canvas

        def arrange(_=None):
            canvas.configure(scrollregion=canvas.bbox("all"))
            if inner.winfo_reqheight() > canvas.winfo_height() > 1:
                scroll.pack(side="right", fill="y")
            else:
                scroll.pack_forget()

        inner.bind("<Configure>", arrange)
        canvas.bind("<Configure>", lambda e: (canvas.itemconfigure(window_id, width=e.width), arrange()))
        for button in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            canvas.bind(button, self.wheel)
        if position:
            self.root.after_idle(lambda: canvas.yview_moveto(position))

        for group in GROUPS:
            ps = [q for q in self.platforms if q.group == group]
            if not ps:
                continue
            ttk.Label(inner, text=GROUP_TITLES[group].upper(),
                      style="Section.TLabel").pack(anchor="w", pady=(10, 5))
            grid = ttk.Frame(inner, style="Card.TFrame")
            grid.pack(fill="x")
            for c in range(3):
                grid.columnconfigure(c, weight=1, uniform="chip")
            for i, q in enumerate(ps):
                self.chip(grid, name, q, default).grid(row=i // 3, column=i % 3, sticky="ew",
                                                       padx=(0, 5), pady=(0, 5))

    def chip(self, parent, name, q, default):
        status, detail = self.results.get((name.lower(), q.key), ("", ""))
        if not status and q.problem(name):
            status, detail = INVALID, q.problem(name)
        kind = status or ("skipped" if q.key in self.skipped
                          else "waiting" if self.busy else "")
        bg, fg, symbol = CHIP.get(kind, CHIP[""])
        label = tk.Label(parent, text=f"{symbol}  {q.short_title}", bg=bg, fg=fg,
                         font=self.f["small_strike" if kind == INVALID else "small"],
                         anchor="w", padx=10, pady=5,
                         cursor="hand2" if q.link else "")
        if kind == INVALID and detail:
            hint = f"{q.title} doesn't allow this name: {detail}"
        else:
            hint = f"{q.title}: {CHIP_TEXT.get(kind, kind)}" + (f" – {detail}" if detail else "")
        if q.link:
            hint += "   ·   click to open"
            label.bind("<Button-1>", lambda e: webbrowser.open(q.link_for(name)))
        label.bind("<Enter>", lambda e: self.hint.set(hint))
        label.bind("<Leave>", lambda e: self.hint.set(default))
        for button in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            label.bind(button, self.wheel)
        return label

    def wheel(self, event):
        canvas = getattr(self, "detail_canvas", None)
        if canvas is None or canvas.yview() == (0.0, 1.0):
            return
        if getattr(event, "num", None) == 4:
            step = -1
        elif getattr(event, "num", None) == 5:
            step = 1
        else:
            step = -1 if event.delta > 0 else 1
        canvas.yview_scroll(step * 2, "units")

    def copy(self, name):
        self.root.clipboard_clear()
        self.root.clipboard_append(name)
        self.status.set(f"Copied '{name}'.")

    # ----- new versions -----------------------------------------------------

    def check_periodically(self):
        self.check_updates(manual=False)
        self.root.after(3_600_000, self.check_periodically)

    def check_updates(self, manual: bool):
        if manual:
            self.update_status.set("Checking…")
            self.check_button.configure(state="disabled")

        def background():
            try:
                if LAUNCHER and callable(LAUNCHER.get("newer")):
                    commit = LAUNCHER["newer"]()
                    info = {"kind": "restart", "commit": commit} if commit else None
                else:
                    info = find_update(new_session())
                    if info:
                        info["kind"] = "page"
                self.events.put(("update_info", info, "", manual))
            except Exception as e:
                self.events.put(("update_info", None, f"{type(e).__name__}", manual))

        threading.Thread(target=background, daemon=True).start()

    def on_update_info(self, info, error, manual):
        self.check_button.configure(state="normal")
        if error:
            self.update_status.set(f"Couldn't check ({error}).")
            if manual:
                self.log(f"Checking for updates failed ({error}).")
            return
        if not info:
            self.update_status.set("You have the latest version.")
            if manual:
                self.status.set("You have the latest version.")
            return
        self.update_info = info
        if info["kind"] == "restart":
            self.update_status.set("A new version is ready on GitHub.")
            self.update_text.configure(text="New version ready")
            self.update_button.configure(text="Restart")
        else:
            self.update_status.set(f"Version {info['version']} is on GitHub.")
            self.update_text.configure(text=f"New version {info['version']}")
            self.update_button.configure(text="View")
        self.update_pill.grid()
        self.log("A new version is available.")

    def click_update(self):
        info = self.update_info
        if not info:
            return
        if info["kind"] != "restart":
            webbrowser.open(info["page"])
            return
        if self.busy and not messagebox.askyesno(
                "UserAtlas", "Still checking. Stop and restart?\n\n"
                             "Everything checked so far is saved and continues afterwards."):
            return
        self.stop.set()
        if self.store:
            self.store.close()
        LAUNCHER["restart"]()
        global _output
        _output = None
        self.root.destroy()

    # ----- self-test table --------------------------------------------------

    def fill_test_table(self, platforms, busy=False):
        self.test_table.delete(*self.test_table.get_children())
        for q in platforms:
            if busy:
                self.selftest_state[q.key] = ("busy", "")
            self.test_table.insert("", "end", iid=q.key, values=(
                q.title, GROUP_TITLES[q.group], "", ""))
            self.update_test_row(q.key)
        failing = sum(1 for st, _ in self.selftest_state.values() if st == "not working")
        self.set_badge("selftest", f"⚠ {failing}" if failing else "", warning=True)

    def update_test_row(self, key):
        if not self.test_table.exists(key):
            return
        state, why = self.selftest_state.get(key, ("", ""))
        self.test_table.set(key, "state", SELFTEST_TEXT.get(state, state))
        self.test_table.set(key, "why", why)
        self.test_table.item(key, tags=(state,))

    # ----- other ------------------------------------------------------------

    def export(self):
        if not self.names:
            messagebox.showinfo("UserAtlas", "There's nothing to save yet.")
            return
        path = filedialog.asksaveasfilename(
            title="Save overview", defaultextension=".csv", initialfile="overview.csv",
            filetypes=[("CSV (opens in Excel)", "*.csv")])
        if not path:
            return
        try:
            write_overview(path, self.names, self.platforms, self.results)
        except OSError as e:
            messagebox.showerror("UserAtlas", f"Saving failed:\n{e}")
            return
        self.log(f"Overview saved: {path}")
        self.status.set("Overview saved.")

    def open_folder(self):
        try:
            if os.name == "nt":
                os.startfile(self.folder)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", self.folder])
            else:
                subprocess.Popen(["xdg-open", self.folder])
        except Exception as e:
            messagebox.showerror("UserAtlas", f"Couldn't open the folder:\n{e}")

    def log(self, text):
        self.log_box.configure(state="normal")
        self.log_box.insert("end", f"{datetime.now():%H:%M:%S}   ", ("time",))
        self.log_box.insert("end", f"{text}\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    def clear_log(self):
        self.log_box.configure(state="normal")
        self.log_box.delete("1.0", "end")
        self.log_box.configure(state="disabled")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv=None):
    if argv is None:
        argv = sys.argv[1:]
    if not argv or argv == ["--window"]:
        return start_window()
    if requests is None:
        print("This script needs the 'requests' package. Install it with:\n"
              "    pip install requests")
        return 1
    if os.name == "nt":
        os.system("")  # turn on colors in the Windows terminal
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass

    ap = argparse.ArgumentParser(
        description="Check whether usernames are available on gaming platforms, social "
                    "networks, developer sites and as a domain name.")
    ap.add_argument("sources", nargs="*", help="text file(s) with names, or single names")
    ap.add_argument("--group", help=f"comma list from: {', '.join(GROUPS)} (default: all)")
    ap.add_argument("--platform", help="comma list of platforms, see --list")
    ap.add_argument("--tld", help=f"domain extensions (default: {STANDARD_TLDS})")
    ap.add_argument("--out", default="results.csv", help="log file with every result")
    ap.add_argument("--overview", default="overview.csv", help="overview per name")
    ap.add_argument("--fresh", action="store_true",
                    help="throw away earlier results and check everything again")
    ap.add_argument("--quiet", action="store_true", help="only show available names")
    ap.add_argument("--slower", type=float, default=1.0,
                    help="multiply the pauses, e.g. 2 = twice as calm")
    ap.add_argument("--selftest", action="store_true",
                    help="only test which platforms work right now")
    ap.add_argument("--no-selftest", action="store_true",
                    help="skip the self-test and use every chosen platform")
    ap.add_argument("--list", action="store_true", help="show all platforms and their name rules")
    ap.add_argument("--rules", action="store_true",
                    help="only check the names against each platform's rules (no internet)")
    ap.add_argument("--window", action="store_true",
                    help="open the window (also happens without arguments)")
    args = ap.parse_args(argv)
    if args.window:
        return start_window()

    if args.list:
        show_list()
        return 0

    platforms = choose_platforms(args)
    if not platforms:
        sys.exit("No platforms chosen.")
    stop = threading.Event()

    try:
        if args.selftest:
            self_test(platforms, stop)
            return 0

        names = read_names(args.sources)
        if not names:
            ap.print_usage()
            sys.exit("Give a file with names (one per line) or single names.")
        if args.rules:
            rules_report(names, platforms)
            return 0

        store = Store(args.out, args.fresh, args.quiet)
        try:
            # Self-test only for platforms that still have work to do
            todo = [p for p in platforms if any(not store.done(n, p) for n in names)]
            if todo and not args.no_selftest:
                outcome = self_test(todo, stop)
                skipped = [p for p in todo if not outcome[p.key][0]]
                todo = [p for p in todo if outcome[p.key][0]]
                if skipped:
                    say("Skipped: " + ", ".join(p.title for p in skipped)
                        + "  (run again later and they're tested again)\n")

            if todo:
                say(f"{len(names)} names × {len(todo)} "
                    f"{'platform' if len(todo) == 1 else 'platforms'}. "
                    f"Estimated time: {estimate_duration(names, todo, store, args.slower)}. "
                    f"You can stop any time with Ctrl+C.\n")
                threads = [threading.Thread(target=worker, daemon=True,
                                            args=(p, names, store, stop, args.slower))
                           for p in todo]
                for t in threads:
                    t.start()

                last = [time.time()]

                def progress():
                    if args.quiet and time.time() - last[0] > 30:
                        last[0] = time.time()
                        say(f"  … {store.new} checks done")

                wait_for(threads, stop, progress)
            else:
                say("Nothing left to check.")
        finally:
            store.close()
            rows = write_overview(args.overview, names, platforms, store.results)

        summary(rows, platforms)
        say(f"\nEverything is in {args.overview} (overview) and {args.out} (all details).")
        say("Note: 'available' means no account or registration was found. Some names "
            "are still blocked or reserved; you'll only find out when claiming.")
        return 0
    except KeyboardInterrupt:
        say("Stopped. Run the same command again to continue.")
        return 130


if __name__ == "__main__":
    sys.exit(main())
