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
import concurrent.futures
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
from urllib.parse import quote

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
# "Probably free": no account was found, but the site has no public way to
# confirm a name can be claimed (it may be held by a banned, deleted or private
# account). Only "available" means the site itself confirmed it.
LIKELY = "probably free"
FINAL = {AVAILABLE, LIKELY, TAKEN, INVALID}
FREE = {AVAILABLE, LIKELY}
# Bump when checks change in a way that makes earlier 'available' results
# untrustworthy; those are then checked again instead of reused.
CHECKS_VERSION = "3"
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


def by_status(r, taken=(200,), available=(404,), available_detail="",
              free=AVAILABLE) -> Result:
    """Common pattern: the HTTP status code says it all."""
    if r.status_code in taken:
        return TAKEN, ""
    if r.status_code in available:
        return free, available_detail
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


# Optional proxies, set by the user. Empty = use the computer's normal
# connection. Several may be given (one per line); checks rotate through them.
_PROXY_URLS: List[str] = []
_proxy_i = 0
_PROXY_TEST_URL = "https://api.github.com/zen"


def parse_proxy_line(line: str) -> str:
    """Turn one proxy into a requests proxy URL, or '' if it can't be read.

    Accepts the format most providers hand out — IP:PORT:USER:PASS — as well as
    IP:PORT without a login, and a full URL (http://, https://, socks5h://, …).
    """
    line = (line or "").strip()
    if not line or line.startswith("#"):
        return ""
    if re.match(r"^[a-z][a-z0-9+.\-]*://", line, re.I):
        return line  # already a full proxy URL; use it as given
    parts = line.split(":")
    if len(parts) == 2:
        host, port, user, pwd = parts[0], parts[1], "", ""
    elif len(parts) == 4:
        host, port, user, pwd = parts
    else:
        return ""
    host, port = host.strip(), port.strip()
    if not host or not port.isdigit():
        return ""
    auth = f"{quote(user, safe='')}:{quote(pwd, safe='')}@" if user else ""
    return f"http://{auth}{host}:{port}"


def parse_proxies(text: str) -> Tuple[List[str], List[str]]:
    """Read the user's proxy text (one per line) into (valid URLs, bad lines)."""
    valid: List[str] = []
    invalid: List[str] = []
    seen = set()
    for raw in re.split(r"[\r\n,]+", text or ""):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        url = parse_proxy_line(line)
        if not url:
            invalid.append(line)
        elif url not in seen:
            seen.add(url)
            valid.append(url)
    return valid, invalid


def set_proxies(urls: List[str]) -> None:
    global _PROXY_URLS, _proxy_i
    _PROXY_URLS = list(urls)
    _proxy_i = 0


def apply_proxy_text(text: str) -> Tuple[List[str], List[str]]:
    """Parse the user's proxy text and activate it; returns (valid, invalid)."""
    valid, invalid = parse_proxies(text)
    set_proxies(valid)
    return valid, invalid


# Kept so older callers (--proxy, a previously saved single proxy) still work.
def set_proxy(text: str) -> bool:
    apply_proxy_text(text)
    return True


def proxy_count() -> int:
    return len(_PROXY_URLS)


def proxy_url() -> str:
    """The first proxy — for logging and backward compatibility."""
    return _PROXY_URLS[0] if _PROXY_URLS else ""


def next_proxy() -> str:
    """The next proxy in the rotation, so load spreads evenly across them."""
    global _proxy_i
    if not _PROXY_URLS:
        return ""
    url = _PROXY_URLS[_proxy_i % len(_PROXY_URLS)]
    _proxy_i += 1
    return url


def mask_proxy(url: str) -> str:
    """Hide the password when a proxy URL is shown or logged."""
    return re.sub(r"(://[^:@/]+:)[^@/]+@", r"\1***@", url or "")


def new_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({
        "User-Agent": UA,
        "Accept-Language": "en-US,en;q=0.9",
    })
    url = next_proxy()
    if url:
        s.proxies.update({"http": url, "https": url})
    return s


def switch_session_proxy(s: requests.Session) -> str:
    """Point this session at a different proxy than it uses now, so a
    rate-limited check can retry from a fresh IP. Returns the new proxy URL,
    or '' when there isn't another one to switch to."""
    if proxy_count() < 2:
        return ""
    current = s.proxies.get("https", "")
    for _ in range(proxy_count()):
        url = next_proxy()
        if url and url != current:
            s.proxies.update({"http": url, "https": url})
            return url
    return ""


def test_one_proxy(url: str, timeout: int = 12) -> Tuple[str, bool, str]:
    """Reach the internet through one proxy. Returns (url, ok, short reason)."""
    try:
        s = requests.Session()
        s.headers.update({"User-Agent": UA})
        s.proxies.update({"http": url, "https": url})
        r = s.get(_PROXY_TEST_URL, timeout=timeout)
        return (url, r.status_code == 200,
                "ok" if r.status_code == 200 else f"HTTP {r.status_code}")
    except Exception as e:
        return (url, False, f"{type(e).__name__}: {shorten(e, 80)}")


def test_proxies(urls: List[str], workers: int = 8) -> List[Tuple[str, bool, str]]:
    """Test every proxy at once so a pool of them doesn't take minutes."""
    if not urls:
        return []
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(workers, len(urls))) as ex:
        return list(ex.map(test_one_proxy, urls))


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
        return LIKELY, NO_PROFILE
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
                # TikTok keeps the names of banned and deleted accounts, which
                # look exactly like this; only its edit-profile screen knows.
                return LIKELY, "no profile found (banned or deleted accounts can still hold it)"
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
            # This public check misses names held by suspended or deactivated
            # accounts, which X's sign-up screen still refuses.
            return LIKELY, "X's public check says free; its sign-up screen can still refuse it"
        reason = d.get("reason", "")
        if reason == "taken":
            return TAKEN, ""
        if "unavailable" in f"{d.get('msg', '')} {d.get('desc', '')}".lower():
            return TAKEN, "X keeps this name unavailable"
        return INVALID, shorten(d.get("desc") or reason or "X says this name isn't allowed")
    if isinstance(d, dict) and d.get("errors"):
        # X answers 'internal error' for some names its sign-up screen calls taken
        return UNKNOWN, "X wouldn't say (often a name held by a suspended account)"
    return unexpected(r)


def check_youtube(s, n):
    consent = {"SOCS": "CAI", "CONSENT": "YES+cb"}
    r = s.get(f"https://www.youtube.com/@{n}", cookies=consent, timeout=TIMEOUT)
    if "consent." in r.url:
        return UNKNOWN, "YouTube's cookie notice is in the way"
    if r.status_code != 404:
        return by_status(r)
    # No channel uses this @handle, but YouTube also keeps a handle for every
    # channel whose old custom URL (/c/name) or username (/user/name) it is.
    for path in (f"c/{n}", f"user/{n}"):
        r = s.get(f"https://www.youtube.com/{path}", cookies=consent, timeout=TIMEOUT)
        if r.status_code == 200:
            return TAKEN, f"reserved by a channel's old URL (youtube.com/{path})"
        if r.status_code not in (404, 410):
            return unexpected(r)
    return LIKELY, "no channel found (closed channels can still hold a handle)"


def check_snapchat(s, n):
    # Snapchat's sign-up form only answers a real browser that passes its bot
    # check, so all we can see is whether a public profile exists.
    r = s.get(f"https://www.snapchat.com/add/{n}", timeout=TIMEOUT)
    return by_status(r, available_detail="no public profile (private and deleted "
                                          "accounts can still hold it)", free=LIKELY)


# t.me alone can't tell a free name from one in use: accounts without a public
# page (and unused collectibles) show the same "you can contact @name" page as a
# free name. Fragment (fragment.com, Telegram's official username marketplace)
# reports a status for every name: "Unavailable" means nobody has it and it isn't
# sold, so it can be claimed; "Taken" means an account uses it; "Available",
# "On auction", "For sale" and "Sold" mean it's a collectible that must be bought.
FRAGMENT_STATUS = re.compile(
    r'class="([^"]*\btm-status-(\w+)\b[^"]*)"[^>]*>\s*([^<]*?)\s*<')
FRAGMENT_ROW = re.compile(r'<tr[^>]*tm-row-selectable[^>]*>(.*?)</tr>', re.S)
FRAGMENT_CSS = {"avail": "available", "unavail": "unavailable", "taken": "taken"}


def _fragment_html(r) -> Optional[str]:
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    if r.status_code != 200:
        return None
    d = json_or_none(r)
    if isinstance(d, dict):
        return d.get("h") or ""
    return r.text


def _fragment_status(css_class: str, css: str, text: str) -> str:
    text = " ".join(text.split()).lower()
    return text or FRAGMENT_CSS.get(css.lower(), css.lower())


def fragment_status(s, n) -> Optional[str]:
    """Fragment's status for this name, lowercased ('taken', 'available',
    'on auction', 'for sale', 'sold', 'unavailable'); '' when Fragment has no
    page for it (nobody uses it and it isn't sold); None when Fragment couldn't
    be read."""
    name = n.lower()
    # 1) The name's own page. Its header shows the status; a name nobody has
    #    gets no page and is sent to the search page instead.
    try:
        r = s.get(f"https://fragment.com/username/{name}",
                  headers={"X-Requested-With": "XMLHttpRequest",
                           "X-Aj-Referer": f"https://fragment.com/?query={name}",
                           "Accept": "application/json, text/javascript, */*; q=0.01"},
                  allow_redirects=False, timeout=TIMEOUT)
        if r.status_code in (301, 302, 303, 307, 308):
            if "query=" in r.headers.get("Location", ""):
                return ""
        else:
            d = json_or_none(r)
            if r.status_code == 200 and isinstance(d, dict) and not d.get("h") \
                    and "query=" in str(d.get("r", "")):
                return ""
            html = _fragment_html(r)
            for m in FRAGMENT_STATUS.finditer(html or ""):
                if "tm-section-header-status" in m.group(1):
                    return _fragment_status(*m.groups())
    except requests.RequestException:
        pass
    # 2) The search page: a row per name that Fragment knows, with its status.
    try:
        r = s.get("https://fragment.com/", params={"query": name}, timeout=TIMEOUT)
        html = _fragment_html(r)
    except requests.RequestException:
        return None
    if not html or "tm-" not in html:
        return None
    for row in FRAGMENT_ROW.findall(html):
        names = re.findall(r'/username/([A-Za-z0-9_]+)|>\s*@([A-Za-z0-9_]+)\s*<', row)
        if any(name == (a or b).lower() for a, b in names):
            m = FRAGMENT_STATUS.search(row)
            return _fragment_status(*m.groups()) if m else None
    return ""  # a real search page without this name: Fragment doesn't know it


def ton_collectible(s, n) -> Optional[bool]:
    """Is this name a minted collectible (an NFT on the TON blockchain)? None if unknown."""
    try:
        r = s.get(f"https://tonapi.io/v2/dns/{n.lower()}.t.me", timeout=TIMEOUT)
    except requests.RequestException:
        return None
    if r.status_code == 404:
        return False
    d = json_or_none(r)
    if r.status_code == 200 and isinstance(d, dict):
        return bool(d.get("item") or d.get("name"))
    return None


FRAGMENT_TAKEN = {"taken": "used by an account without a public page",
                  "available": "collectible username, only sold through Fragment",
                  "on auction": "collectible username, on auction on Fragment",
                  "for sale": "collectible username, for sale on Fragment",
                  "sold": "collectible username, owned by someone"}


def check_telegram(s, n):
    r = s.get(f"https://t.me/{n}", timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    if "tgme_page_title" in r.text:
        return TAKEN, ""
    if not (r.status_code == 200 and "tgme_page" in r.text):
        return unexpected(r)
    # No public page. That doesn't mean free: ask Fragment.
    status = fragment_status(s, n)
    if status in ("", "unavailable"):
        return AVAILABLE, "nobody has it (checked on Fragment)"
    if status:
        return TAKEN, FRAGMENT_TAKEN.get(status, f"Fragment says: {status}")
    if ton_collectible(s, n):
        return TAKEN, FRAGMENT_TAKEN["sold"]
    return UNKNOWN, "no public page, and Fragment couldn't be checked to confirm"


def check_bluesky(s, n):
    # The official sign-up check: the exact endpoint bsky.app's "create account"
    # screen calls. It also rejects reserved/blocked handles, not just taken ones.
    r = s.get("https://bsky.social/xrpc/com.atproto.temp.checkHandleAvailability",
              params={"handle": f"{n}.bsky.social", "email": "a@example.com",
                      "birthDate": "2000-01-01T00:00:00.000Z"}, timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    d = json_or_none(r)
    if isinstance(d, dict) and isinstance(d.get("result"), dict):
        kind = str(d["result"].get("$type", ""))
        if kind.endswith("resultAvailable"):
            return AVAILABLE, ""
        if kind.endswith("resultUnavailable"):
            return TAKEN, ""
    if isinstance(d, dict) and d.get("error") in ("InvalidHandle", "InvalidRequest"):
        return INVALID, shorten(d.get("message") or "Bluesky says this handle isn't allowed")
    # Fallback: the plain existence lookup, so a changed endpoint never breaks the check.
    r = s.get("https://public.api.bsky.app/xrpc/com.atproto.identity.resolveHandle",
              params={"handle": f"{n}.bsky.social"}, timeout=TIMEOUT)
    if r.status_code == 200:
        return TAKEN, ""
    if r.status_code == 400:
        return AVAILABLE, ""
    return unexpected(r)


TAGS = re.compile(r"<[^>]+>")


def github_signup_check(s, n) -> Optional[Result]:
    """The check GitHub's sign-up form runs while you type a username. It also
    knows names that are reserved or held by deleted and renamed accounts."""
    r = s.get("https://github.com/signup_check_new/username",
              params={"value": n}, headers={"X-Requested-With": "XMLHttpRequest",
                                            "Referer": "https://github.com/signup"},
              timeout=TIMEOUT)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    message = " ".join(TAGS.sub(" ", r.text or "").replace("&#39;", "'").split())
    if r.status_code == 200 and "is available" in message:
        return AVAILABLE, ""
    if r.status_code == 422:
        if re.search(r"not available|unavailable|reserved", message, re.I):
            return TAKEN, ""
        if message:
            return INVALID, shorten(message)
    return None


def check_github(s, n):
    try:
        found = github_signup_check(s, n)
    except requests.RequestException:
        found = None
    if found:
        return found
    # Fallback: is there a profile? (Misses reserved and formerly used names.)
    r = s.head(f"https://github.com/{n}", allow_redirects=False, timeout=TIMEOUT)
    return by_status(r, taken=(200, 301, 302), available_detail=NO_PROFILE, free=LIKELY)


def check_gitlab(s, n):
    r = s.get(f"https://gitlab.com/users/{n}/exists",
              headers={"Accept": "application/json"}, timeout=TIMEOUT)
    d = json_or_none(r)
    if isinstance(d, dict) and "exists" in d:
        return (TAKEN, "") if d["exists"] else (AVAILABLE, "")
    return unexpected(r)


# Reddit blocks anonymous checks from apps; its official API works with keys the
# user creates at reddit.com/prefs/apps (a "script" app). Optional; kept locally.
REDDIT_APPS_URL = "https://www.reddit.com/prefs/apps"
_reddit = {"id": os.environ.get("REDDIT_CLIENT_ID", ""),
           "secret": os.environ.get("REDDIT_CLIENT_SECRET", ""),
           "token": "", "expires": 0.0}
_reddit_lock = threading.Lock()


def set_reddit_keys(client_id: str, secret: str) -> None:
    with _reddit_lock:
        _reddit.update(id=(client_id or "").strip(), secret=(secret or "").strip(),
                       token="", expires=0.0)


def reddit_keys_set() -> bool:
    return bool(_reddit["id"] and _reddit["secret"])


def reddit_token(s, fresh: bool = False) -> str:
    """An app-only access token for Reddit's API; raises RuntimeError when refused."""
    with _reddit_lock:
        if _reddit["token"] and not fresh and time.time() < _reddit["expires"]:
            return _reddit["token"]
        r = s.post("https://www.reddit.com/api/v1/access_token",
                   auth=(_reddit["id"], _reddit["secret"]),
                   data={"grant_type": "client_credentials"},
                   headers={"User-Agent": f"windows:useratlas:{VERSION} (username checker)"},
                   timeout=TIMEOUT)
        if r.status_code == 429:
            raise RateLimited(retry_after(r))
        d = json_or_none(r)
        token = d.get("access_token") if isinstance(d, dict) else None
        if not token:
            why = (d or {}).get("error") if isinstance(d, dict) else f"HTTP {r.status_code}"
            raise RuntimeError(f"Reddit didn't accept the API keys ({why})")
        _reddit["token"] = token
        _reddit["expires"] = time.time() + float(d.get("expires_in") or 3600) - 60
        return token


def check_reddit_api(s, n):
    h = {"User-Agent": f"windows:useratlas:{VERSION} (username checker)"}
    try:
        for attempt in range(2):
            h["Authorization"] = f"bearer {reddit_token(s, fresh=attempt > 0)}"
            r = s.get("https://oauth.reddit.com/api/username_available",
                      params={"user": n}, headers=h, timeout=TIMEOUT)
            if r.status_code != 401:
                break
    except RuntimeError as e:
        return UNKNOWN, str(e)
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    d = json_or_none(r)
    if r.status_code == 200 and d is True:
        return AVAILABLE, ""
    if r.status_code == 200 and d is False:
        return TAKEN, ""
    if r.status_code == 403:
        return UNKNOWN, "Reddit refused the API keys (is API access approved yet?)"
    # Fallback: does the profile exist?
    r = s.get(f"https://oauth.reddit.com/user/{n}/about", headers=h, timeout=TIMEOUT)
    return by_status(r, available_detail="no profile found (deleted names can't be claimed again)",
                     free=LIKELY)


def check_reddit(s, n):
    if reddit_keys_set():
        return check_reddit_api(s, n)
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
    if r.status_code in (401, 403):
        return UNKNOWN, "Reddit blocks checks without API keys (add them in Settings)"
    return by_status(r, available_detail="no profile found (deleted names can't be claimed again)",
                     free=LIKELY)


TWITCH_CLIENT_ID = "kimne78kx3ncx6brgo4mv6wki5h1ko"  # twitch.tv's own public client id


def check_twitch(s, n):
    # Twitch's sign-up availability check needs a browser integrity token, but
    # the account lookup covers every account, including banned and recently
    # deleted ones (whose names Twitch doesn't hand out again yet).
    r = s.post("https://gql.twitch.tv/gql", headers={"Client-Id": TWITCH_CLIENT_ID},
               timeout=TIMEOUT, json={
                   "query": "query($u:String!){user(login:$u,lookupType:ALL){id}}",
                   "variables": {"u": n}})
    if r.status_code == 429:
        raise RateLimited(retry_after(r))
    d = json_or_none(r)
    try:
        return (TAKEN, "") if d["data"]["user"] else (AVAILABLE, "")
    except (KeyError, TypeError):
        return unexpected(r)


def check_soundcloud(s, n):
    r = s.get(f"https://soundcloud.com/{n}", timeout=TIMEOUT)
    return by_status(r, available_detail=NO_PROFILE, free=LIKELY)


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


def dns_registered(s, domain: str) -> Optional[Result]:
    """Is the domain registered? Asked over DNS-over-HTTPS, which — unlike
    WHOIS (a raw port-43 socket) — rides the user's proxy and isn't
    WHOIS-rate-limited. A registered domain is delegated (has NS records); an
    unregistered one comes back NXDOMAIN. Returns a Result, or None when DNS
    can't give a clear answer, so the caller can fall back."""
    try:
        r = s.get("https://dns.google/resolve",
                  params={"name": domain, "type": "NS"},
                  headers={"Accept": "application/dns-json"}, timeout=TIMEOUT)
        if r.status_code != 200:
            return None
        d = r.json()
    except (requests.RequestException, ValueError, OSError):
        return None
    status = d.get("Status")
    if status == 3:  # NXDOMAIN: the name doesn't exist, so it's free
        return LIKELY, "not in DNS (the registry itself couldn't be asked)"
    if status == 0 and any(a.get("type") == 2 for a in d.get("Answer", [])):
        return TAKEN, "via DNS"  # has NS records -> delegated -> registered
    return None  # anything else is inconclusive; let the caller decide


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
                # RDAP is rate-limiting us: try DNS (over the proxy) first.
                return dns_registered(s, domain) or _raise_rate_limit(r)
            # any other answer: try WHOIS
        try:
            return whois_check(tld, domain)
        except RateLimited:
            # WHOIS doesn't go through the proxy and is rate-limiting the real
            # IP; DNS-over-HTTPS does go through the proxy, so try that instead.
            doh = dns_registered(s, domain)
            if doh is not None:
                return doh
            raise
    return check


def _raise_rate_limit(r) -> Result:
    raise RateLimited(retry_after(r))


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
        self._cache: Dict[str, bool] = {}   # blocked() is pure; memoize it
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
        hit = self._cache.get(name)
        if hit is not None:
            return hit
        self._cache[name] = hit = self._blocked(name)
        return hit

    def _blocked(self, name: str) -> bool:
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
          # Self-test controls must be valid *and* taken. Discord's new
          # lowercase handles reject "discord" (reserved) as invalid, so use
          # plain common names that migration-era users long since claimed.
          4.0, ["john", "alex", "mike", "max"], lowercase=True),
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

COLOR = {AVAILABLE: "\033[92m", LIKELY: "\033[36m", TAKEN: "\033[91m", INVALID: "\033[90m",
         UNKNOWN: "\033[93m"}
SHOWN = {AVAILABLE: "available", LIKELY: "probably free", TAKEN: "taken",
         INVALID: "not allowed", UNKNOWN: "unknown"}
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


def colored(status: str, width: int = 13) -> str:
    return f"{COLOR.get(status, '')}{SHOWN.get(status, status):<{width}}{RESET}"


class Store:
    """Writes every result to a CSV right away and remembers earlier runs."""

    FIELDS = ["time", "name", "platform", "status", "detail", "checks"]

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
        rows: List[dict] = []
        outdated = False
        if os.path.exists(path):
            with open(path, newline="", encoding="utf-8-sig") as f:
                reader = csv.DictReader(f, delimiter=";")
                outdated = "checks" not in (reader.fieldnames or [])
                for row in reader:
                    try:
                        status = row["status"]
                        # Free results from older, less careful checks are checked again.
                        if status in FREE and row.get("checks") != CHECKS_VERSION:
                            outdated = True
                            continue
                        self.results[(row["name"].lower(), row["platform"])] = (
                            status, row["detail"])
                        rows.append(row)
                    except KeyError:
                        continue
        if os.path.exists(path) and not outdated:
            self.f = open(path, "a", newline="", encoding="utf-8")
            self.writer = csv.writer(self.f, delimiter=";")
        elif os.path.exists(path):
            # Rewrite the file without the outdated rows, in the current format.
            self.f = open(path, "w", newline="", encoding="utf-8-sig")
            self.writer = csv.writer(self.f, delimiter=";")
            self.writer.writerow(self.FIELDS)
            for row in rows:
                self.writer.writerow([row.get(k) or "" for k in self.FIELDS[:-1]]
                                     + [row.get("checks") or CHECKS_VERSION])
            self.f.flush()
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
                                  name, p.key, status, detail, CHECKS_VERSION])
            self.f.flush()
        if self.on_result is not None:
            self.on_result(name, p.key, status, detail)
        elif status in FREE or not self.quiet:
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
    pool = proxy_count()
    switched = 0
    for attempt in range(max_tries):
        try:
            return p.check(s, name)
        except RateLimited as e:
            if attempt < max_tries - 1:
                # With a pool of proxies, hop to a fresh IP and retry at once
                # instead of waiting; only wait once every proxy was tried.
                if pool > 1 and switched < pool - 1 and switch_session_proxy(s):
                    switched += 1
                    if not stop.is_set():
                        say(f"  {p.title} rate-limited — switching proxy and retrying…")
                    if stop.wait(1):
                        return UNKNOWN, "stopped"
                    continue
                w = min(e.wait or wait, max_wait)
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
    if free[0] in FREE and taken[0] == TAKEN:
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
                 for s in (AVAILABLE, LIKELY, TAKEN, INVALID, UNKNOWN) if statuses.count(s)]
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

# Colors: "night atlas". Layered deep-indigo surfaces (sidebar darkest, then the
# page, then raised panels). Violet only marks the current selection and the main
# action; mint, coral and amber carry what the results mean.
C = {
    "bg": "#0F1020", "surface": "#0A0B17", "side_hover": "#161833",
    "card": "#161830", "panel_line": "#24274A", "field": "#1C1F3B",
    "hover": "#21244A", "border": "#2E3259", "border_hover": "#454A80",
    "line": "#222545",
    "text": "#ECEBFA", "muted": "#A0A2C8", "faint": "#6B6E98",
    "accent": "#8B5CF6", "accent_dark": "#7A4AEE", "accent_press": "#6A3BDD",
    "accent_soft": "#2A2359", "accent_text": "#BDA9FF", "accent_off": "#353064",
    "red": "#FB7185", "red_soft": "#33172A", "red_border": "#5A2340",
    "green": "#34D399", "amber": "#FBBF24", "amber_soft": "#3A2C10",
    "row_free": "#11292B", "selected": "#2B2559",
}
# Status pills in the detail panel: (fill, text, symbol, outline)
CHIP = {
    AVAILABLE: ("#10302A", "#4ADFA6", "✓", "#1D5545"),
    LIKELY: ("#142233", "#8CC8E8", "○", "#27425C"),
    TAKEN: ("#361627", "#FF8BA0", "✗", "#5D2541"),
    INVALID: ("#1C1F3B", "#8D90BA", "⊘", "#2E3259"),
    UNKNOWN: ("#382B10", "#FBC64E", "?", "#5E481A"),
    "waiting": ("#272157", "#BBA6FF", "…", "#3F358A"),
    "skipped": ("#171932", "#6B6E98", "–", "#262A4D"),
    "": ("#171932", "#6B6E98", "·", "#262A4D"),
}
CHIP_TEXT = {
    AVAILABLE: "available (the site confirmed it)",
    LIKELY: "probably free: no account found, but the site can't confirm it",
    TAKEN: "taken", INVALID: "not allowed",
    UNKNOWN: "unknown", "waiting": "still checking",
    "skipped": "skipped (failed the self-test)", "": "not checked yet",
}
SELFTEST_TEXT = {"works": "Works", "not working": "Not working right now",
                 "busy": "Testing…", "": "Not tested"}


def pick_family(root, candidates, fallback):
    """The first installed font family out of `candidates`, else `fallback`."""
    try:
        have = {str(f).lower(): str(f) for f in tkfont.families(root)}
    except tk.TclError:
        return fallback
    for name in candidates:
        if name.lower() in have:
            return have[name.lower()]
    return fallback


def blend(a: str, b: str, t: float) -> str:
    """Mix two #rrggbb colors: t=0 gives a, t=1 gives b."""
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(_rgb(a), _rgb(b)))


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


def _paint_wh(master, w: int, h: int, paint) -> "tk.PhotoImage":
    image = tk.PhotoImage(master=master, width=w, height=h)
    rows = []
    for y in range(h):
        row = []
        for x in range(w):
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


def _paint(master, n: int, paint) -> "tk.PhotoImage":
    return _paint_wh(master, n, n, paint)


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


def _rrect_distance(px, py, w, h, r) -> float:
    """Signed distance to a w×h rectangle with corner radius r (negative inside)."""
    qx = abs(px - w / 2) - (w / 2 - r)
    qy = abs(py - h / 2) - (h / 2 - r)
    return math.hypot(max(qx, 0.0), max(qy, 0.0)) + min(max(qx, qy), 0.0) - r


def paint_rounded(master, w, h, r, fill, background, border=None, border_width=1.0):
    """An anti-aliased rounded rectangle on a solid background, as a PhotoImage.

    Kept tiny and used as a 9-slice ttk image element, so one small image
    stretches to any button, field or panel size without new dependencies."""
    bg, fc = _rgb(background), _rgb(fill)
    bc = _rgb(border) if border else fc
    image = tk.PhotoImage(master=master, width=w, height=h)
    rows = []
    for y in range(h):
        row = []
        for x in range(w):
            d = _rrect_distance(x + 0.5, y + 0.5, w, h, r)
            outer = min(1.0, max(0.0, 0.5 - d))
            inner = min(1.0, max(0.0, 0.5 - d - border_width)) if border else outer
            row.append("#%02x%02x%02x" % tuple(
                round(bg[i] * (1 - outer) + bc[i] * (outer - inner) + fc[i] * inner)
                for i in range(3)))
        rows.append("{" + " ".join(row) + "}")
    image.put(" ".join(rows))
    return image


def widen(master, small, border: int, center: int) -> "tk.PhotoImage":
    """Grow a 9-slice image's 1-pixel middle to `center` pixels.

    Tk fills the stretchable middle of an image element by redrawing it tile by
    tile; a 1-pixel tile means one redraw per pixel of a panel, which makes big
    windows crawl. The copy below runs in Tk's C code, so it costs nothing."""
    n, b = small.width(), border
    m, size = n - 2 * b, 2 * b + center
    big = tk.PhotoImage(master=master, width=size, height=size)
    call, e = big.tk.call, size - b
    for sx, dx in ((0, 0), (n - b, e)):
        for sy, dy in ((0, 0), (n - b, e)):
            call(big, "copy", small, "-from", sx, sy, sx + b, sy + b, "-to", dx, dy)
    call(big, "copy", small, "-from", b, 0, b + m, b, "-to", b, 0, e, b)            # top
    call(big, "copy", small, "-from", b, n - b, b + m, n, "-to", b, e, e, size)     # bottom
    call(big, "copy", small, "-from", 0, b, b, b + m, "-to", 0, b, b, e)            # left
    call(big, "copy", small, "-from", n - b, b, n, b + m, "-to", e, b, size, e)     # right
    call(big, "copy", small, "-from", b, b, b + m, b + m, "-to", b, b, e, e)        # middle
    return big


def paint_tick(master, w: int, h: int, background: str, color: str) -> "tk.PhotoImage":
    """A small check mark, centered in w×h (marks a selected platform chip)."""
    bg, cc = _rgb(background), _rgb(color)
    dx = (w - 0.96 * h) / 2
    p = [(dx + 0.08 * h, 0.52 * h), (dx + 0.36 * h, 0.78 * h), (dx + 0.88 * h, 0.24 * h)]
    half = max(0.9, h * 0.075)

    def paint(px, py):
        d = min(_segment_distance(px, py, *p[0], *p[1]), _segment_distance(px, py, *p[1], *p[2]))
        return cc if d <= half else bg

    return _paint_wh(master, w, h, paint)


class Card:
    """A rounded panel with an optional title row (extra controls go in .head)."""
    k = 1.0  # UI scale, set by the window's style()

    def __init__(self, parent, title=None, hint=None, wrap=520, padding=(24, 20)):
        k = Card.k
        self.outer = ttk.Frame(parent, style="Panel.TFrame",
                               padding=tuple(int(round(v * k)) for v in padding))
        self.head = ttk.Frame(self.outer, style="Card.TFrame")
        if title:
            self.head.pack(fill="x")
            ttk.Label(self.head, text=title, style="Heading.TLabel").pack(side="left")
        if hint:
            ttk.Label(self.outer, text=hint, style="Card.Muted.TLabel",
                      wraplength=int(wrap * k), justify="left").pack(anchor="w",
                                                                     pady=(int(5 * k), 0))
        self.body = ttk.Frame(self.outer, style="Card.TFrame")
        self.body.pack(fill="both", expand=True,
                       pady=(int(18 * k) if (title or hint) else 0, 0))


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
        # Caches + batched rendering so a bulk run doesn't freeze the UI:
        self._active_cache: Optional[List[Platform]] = None
        self._problem_cache: Dict[Tuple[str, str], bool] = {}
        self.dirty: set = set()          # names whose row needs redrawing

        global _output
        _output = lambda t: self.events.put(("log", t))

        self.settings_path = os.path.join(self.folder, "settings.json")
        self.style()
        self.build()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.bind("<Control-Return>", lambda e: self.start())
        for i, (key, _) in enumerate(self.TABS, 1):
            self.root.bind(f"<Control-Key-{i}>", lambda e, k=key: self.show_tab(k))
        self.load_settings()
        self.show_tab("names")
        self.update_summary()
        self.root.after(100, self.process)
        self.log(f"UserAtlas {VERSION}. Results are saved in {self.log_path}")
        if proxy_count():
            n = proxy_count()
            self.log(f"Using {n} {'proxy' if n == 1 else 'proxies'} "
                     f"(e.g. {mask_proxy(proxy_url())}).")
        if LAUNCHER and LAUNCHER.get("message"):
            self.log(LAUNCHER["message"])
            self.status.set(LAUNCHER["message"])
        # Through the launcher the app was just updated; after that, check every hour.
        first = 3_600_000 if (LAUNCHER and LAUNCHER.get("source") == "github") else 1500
        self.root.after(first, self.check_periodically)

    # ----- style ------------------------------------------------------------

    def style(self):
        root = self.root
        try:
            scaling = float(root.tk.call("tk", "scaling"))  # pixels per point
        except (tk.TclError, ValueError):
            scaling = 4 / 3
        k = self.k = Card.k = max(1.0, scaling / (4 / 3))

        def px(v):
            return max(1, int(round(v * k)))
        self.px = px

        # Type: the platform's own modern UI face, with a real semibold for titles.
        system = tkfont.nametofont("TkDefaultFont").actual()["family"]
        if sys.platform == "darwin":
            text_family = display_family = system
            semi_text = semi_display = None
        else:
            text_family = pick_family(root, ("Segoe UI Variable Text", "Segoe UI", "Inter",
                                             "Cantarell", "Noto Sans", "DejaVu Sans"), system)
            display_family = pick_family(root, ("Segoe UI Variable Display", "Segoe UI",
                                                "Inter Display", "Inter"), text_family)
            semi_text = pick_family(root, ("Segoe UI Variable Text Semibold",
                                           "Segoe UI Variable Text Semib", "Segoe UI Semibold",
                                           "Inter SemiBold"), None)
            semi_display = pick_family(root, ("Segoe UI Variable Display Semibold",
                                              "Segoe UI Variable Display Semib",
                                              "Segoe UI Semibold", "Inter Display SemiBold",
                                              "Inter SemiBold"), semi_text)

        def font(size, semibold=False, display=False, *extra):
            family = display_family if display else text_family
            if semibold:
                semi = semi_display if display else semi_text
                if semi:
                    return (semi, -px(size)) + extra
                return (family, -px(size), "bold") + extra
            return (family, -px(size)) + extra

        self.f = {
            "normal": font(14), "small": font(13), "bold": font(14, True),
            "small_bold": font(13, True), "nav": font(14, True),
            "heading": font(16, True, True), "title": font(27, True, True),
            "big": font(28, True, True), "brand": font(18, True, True),
            "small_strike": font(13, False, False, "overstrike"),
        }
        for name, spec in (("TkDefaultFont", self.f["normal"]), ("TkTextFont", self.f["normal"]),
                           ("TkMenuFont", self.f["normal"]),
                           ("TkHeadingFont", self.f["small_bold"])):
            try:
                tkfont.nametofont(name).configure(
                    family=spec[0], size=spec[1],
                    weight="bold" if "bold" in spec[2:] else "normal")
            except tk.TclError:
                pass

        s = ttk.Style(root)
        try:
            s.theme_use("clam")
        except tk.TclError:
            pass
        root.configure(background=C["bg"])
        root.option_add("*TCombobox*Listbox.background", C["field"])
        s.configure(".", background=C["bg"], foreground=C["text"], font=self.f["normal"],
                    bordercolor=C["border"], lightcolor=C["card"], darkcolor=C["card"],
                    troughcolor=C["line"], focuscolor=C["accent"],
                    selectbackground=C["selected"], selectforeground="#FFFFFF",
                    insertcolor=C["text"], fieldbackground=C["field"])

        # Text on each surface: the page, a panel ("Card.") and the sidebar ("Bar.")
        for prefix, bg in (("", C["bg"]), ("Card.", C["card"]), ("Bar.", C["surface"])):
            s.configure(f"{prefix}TFrame", background=bg)
            s.configure(f"{prefix}TLabel", background=bg, foreground=C["text"])
            s.configure(f"{prefix}Muted.TLabel", background=bg, foreground=C["muted"],
                        font=self.f["small"])
        s.configure("PageTitle.TLabel", background=C["bg"], font=self.f["title"])
        s.configure("PageDesc.TLabel", background=C["bg"], foreground=C["muted"])
        s.configure("SectionTitle.TLabel", background=C["bg"], font=self.f["heading"])
        s.configure("Page.TLabel", background=C["bg"], foreground=C["muted"],
                    font=self.f["small"])
        s.configure("PageCounter.TLabel", background=C["bg"], foreground=C["muted"],
                    font=self.f["small"])
        s.configure("Strong.TLabel", background=C["bg"], font=self.f["bold"])
        s.configure("Heading.TLabel", background=C["card"], font=self.f["heading"])
        s.configure("Big.TLabel", background=C["card"], font=self.f["big"])
        s.configure("Counter.TLabel", background=C["card"], foreground=C["muted"],
                    font=self.f["small"])
        s.configure("Section.TLabel", background=C["card"], foreground=C["muted"],
                    font=self.f["small_bold"])
        s.configure("SearchHint.TLabel", background=C["field"], foreground=C["faint"])

        # ---- Rounded shapes: tiny anti-aliased images used as 9-slice elements ----
        self.images = []

        def rr(r, fill, bg, border=None):
            n = 2 * r + 3
            image = widen(root, paint_rounded(root, n, n, r, fill, bg, border), r + 1, px(48))
            self.images.append(image)
            return image

        def element(name, r, default, *states):
            # width/height/padding keep the (enlarged) image from setting the
            # element's minimum size; the style's own padding sizes the widget.
            try:
                s.element_create(name, "image", default, *states, border=r + 1, sticky="nsew",
                                 padding=0, width=2 * (r + 1), height=2 * (r + 1))
            except tk.TclError:
                pass  # already made (a second window in the same session)

        def boxed(style_name, el, inner):
            s.layout(style_name, [(el, {"sticky": "nsew", "children": inner})])

        r_panel, r_ctrl, r_pill = px(14), px(9), px(8)

        # Panels, and the frames around multi-line text fields
        element("Panel.bg", r_panel, rr(r_panel, C["card"], C["bg"], C["panel_line"]))
        s.layout("Panel.TFrame", [("Panel.bg", {"sticky": "nsew"})])
        s.configure("Panel.TFrame", background=C["card"])
        for name, bg in (("Field", C["card"]), ("PageField", C["bg"])):
            element(f"{name}.bg", r_ctrl, rr(r_ctrl, C["field"], bg, C["border"]),
                    ("focus", rr(r_ctrl, C["field"], bg, C["accent"])))
            s.layout(f"{name}.TFrame", [(f"{name}.bg", {"sticky": "nsew"})])
            s.configure(f"{name}.TFrame", background=C["field"])

        # Buttons
        label_inner = [("Button.padding", {"sticky": "nsew", "children": [
            ("Button.label", {"sticky": "nsew"})]})]

        def button(style_name, bg, fill, hover, press, border, fg, fg_off, fill_off,
                   border_hover=None, pad=(15, 8)):
            el = style_name.replace(".", "") + ".bg"
            edge = border_hover or border
            element(el, r_ctrl, rr(r_ctrl, fill, bg, border),
                    ("disabled", rr(r_ctrl, fill_off, bg, fill_off)),
                    ("pressed", rr(r_ctrl, press, bg, edge)),
                    ("active", rr(r_ctrl, hover, bg, edge)),
                    ("focus", rr(r_ctrl, fill, bg, C["accent"])))
            boxed(style_name, el, label_inner)
            s.configure(style_name, background=bg, foreground=fg, font=self.f["bold"],
                        padding=(px(pad[0]), px(pad[1])), anchor="center", focusthickness=0)
            s.map(style_name, foreground=[("disabled", fg_off)],
                  background=[("active", bg), ("pressed", bg)])

        for name, bg in (("TButton", C["card"]), ("Page.TButton", C["bg"])):
            button(name, bg, C["field"], C["hover"], C["line"], C["border"], C["text"],
                   C["faint"], bg, C["border_hover"])
        button("Accent.TButton", C["surface"], C["accent"], C["accent_dark"], C["accent_press"],
               C["accent"], "#FFFFFF", "#8F88BC", C["accent_off"], C["accent_dark"], pad=(18, 11))
        button("Stop.TButton", C["surface"], C["red_soft"], "#43192F", "#4F1D37", C["red_border"],
               C["red"], C["faint"], C["surface"], "#7A2C4C", pad=(18, 11))
        for name, bg in (("Link.TButton", C["card"]), ("Page.Link.TButton", C["bg"])):
            s.layout(name, [("Button.border", {"sticky": "nswe", "border": "1",
                                               "children": label_inner})])
            s.configure(name, background=bg, foreground=C["accent_text"], bordercolor=bg,
                        lightcolor=bg, darkcolor=bg, relief="flat", padding=(px(2), px(1)),
                        width=0, font=self.f["small_bold"], focusthickness=0)
            s.map(name, foreground=[("disabled", C["faint"]), ("active", "#E6DEFF")],
                  background=[("active", bg), ("pressed", bg)], bordercolor=[("active", bg)],
                  lightcolor=[("active", bg)], darkcolor=[("active", bg)])

        # One-line entry fields
        for name, bg in (("TEntry", C["card"]), ("Page.TEntry", C["bg"])):
            el = name.replace(".", "") + ".bg"
            element(el, r_ctrl, rr(r_ctrl, C["field"], bg, C["border"]),
                    ("readonly", rr(r_ctrl, C["field"], bg, C["line"])),
                    ("focus", rr(r_ctrl, C["field"], bg, C["accent"])))
            boxed(name, el, [("Entry.padding", {"sticky": "nsew", "children": [
                ("Entry.textarea", {"sticky": "nsew"})]})])
            s.configure(name, background=bg, foreground=C["text"], fieldbackground=C["field"],
                        insertcolor=C["text"], padding=(px(12), px(8)),
                        selectbackground=C["selected"], selectforeground="#FFFFFF")
            s.map(name, foreground=[("readonly", C["muted"])])

        # Platform chips: outlined when off, violet with a tick when picked
        # (both images the same size: an image element is sized by its default image)
        tick_w, tick_h = px(16), px(14)
        tick = paint_tick(root, tick_w, tick_h, C["accent_soft"], C["accent_text"])
        blank = tk.PhotoImage(master=root, width=tick_w, height=tick_h)
        blank.put(C["field"], to=(0, 0, tick_w, tick_h))
        self.images += [tick, blank]
        try:
            s.element_create("Chip.check", "image", blank, ("selected", tick), sticky="")
        except tk.TclError:
            pass
        element("Chip.bg", r_ctrl, rr(r_ctrl, C["field"], C["bg"], C["border"]),
                ("selected", "active", rr(r_ctrl, C["accent_soft"], C["bg"], C["accent_text"])),
                ("selected", rr(r_ctrl, C["accent_soft"], C["bg"], C["accent"])),
                ("active", rr(r_ctrl, C["field"], C["bg"], C["border_hover"])))
        boxed("Chip.TCheckbutton", "Chip.bg", [("Checkbutton.padding", {
            "sticky": "nsew", "children": [
                ("Chip.check", {"side": "right", "sticky": ""}),
                ("Checkbutton.label", {"side": "left", "sticky": "w"})]})])
        s.configure("Chip.TCheckbutton", background=C["bg"], foreground=C["muted"],
                    padding=(px(13), px(10)), focusthickness=0)
        s.map("Chip.TCheckbutton", foreground=[("selected", "#F2EEFF"), ("active", C["text"])],
              background=[("active", C["bg"])])

        # Status pills in the detail panel, one style per kind of result
        self.pill_styles = {}
        for i, (kind, (fill, fg, _symbol, outline)) in enumerate(CHIP.items()):
            el = f"Pill{i}.bg"
            element(el, r_pill, rr(r_pill, fill, C["card"], outline),
                    ("active", rr(r_pill, fill, C["card"], blend(outline, fg, 0.55))))
            name = f"Pill{i}.TLabel"
            boxed(name, el, [("Label.padding", {"sticky": "nsew", "children": [
                ("Label.label", {"sticky": "w"})]})])
            s.configure(name, background=fill, foreground=fg, padding=(px(11), px(7)),
                        font=self.f["small_strike"] if kind == INVALID else self.f["small"])
            self.pill_styles[kind] = name

        # Sidebar pages: a soft pill on hover, violet for the page you're on
        element("Nav.bg", r_ctrl, rr(r_ctrl, C["surface"], C["surface"]),
                ("selected", rr(r_ctrl, C["accent_soft"], C["surface"])),
                ("active", rr(r_ctrl, C["side_hover"], C["surface"])))
        boxed("Nav.TLabel", "Nav.bg", [("Label.padding", {"sticky": "nsew", "children": [
            ("Label.label", {"sticky": "w"})]})])
        s.configure("Nav.TLabel", background=C["surface"], foreground=C["muted"],
                    font=self.f["nav"], padding=(px(14), px(10)))
        s.map("Nav.TLabel", foreground=[("selected", "#F4F0FF"), ("active", C["text"])])
        s.configure("NavBadge.TLabel", background=C["surface"], foreground=C["amber"],
                    font=self.f["small_bold"])
        s.map("NavBadge.TLabel", background=[("selected", C["accent_soft"]),
                                             ("active", C["side_hover"])])

        # The "new version" notice in the sidebar
        element("Notice.bg", r_ctrl, rr(r_ctrl, C["accent_soft"], C["surface"], C["accent_off"]))
        s.layout("Notice.TFrame", [("Notice.bg", {"sticky": "nsew"})])
        s.configure("Notice.TFrame", background=C["accent_soft"])
        s.configure("Notice.TLabel", background=C["accent_soft"], foreground=C["accent_text"],
                    font=self.f["small"])
        s.configure("NoticeAction.TLabel", background=C["accent_soft"], foreground="#FFFFFF",
                    font=self.f["small_bold"])

        # Progress: a slim rounded track
        rp = px(3)
        element("Track.trough", rp, rr(rp, C["line"], C["surface"]))
        element("Track.pbar", rp, rr(rp, C["accent"], C["line"]))
        s.layout("Accent.Horizontal.TProgressbar", [("Track.trough", {
            "sticky": "nsew", "children": [("Track.pbar", {"side": "left", "sticky": "ns"})]})])
        s.configure("Accent.Horizontal.TProgressbar", background=C["surface"])

        # Tables
        line = tkfont.Font(root=root, font=self.f["normal"]).metrics("linespace")
        s.configure("Treeview", background=C["card"], fieldbackground=C["card"],
                    foreground=C["text"], bordercolor=C["card"], lightcolor=C["card"],
                    darkcolor=C["card"], borderwidth=0, rowheight=int(line * 2.2))
        s.map("Treeview", background=[("selected", C["selected"])],
              foreground=[("selected", "#FFFFFF")])
        s.configure("Treeview.Heading", background=C["card"], foreground=C["muted"],
                    font=self.f["small_bold"], relief="flat", bordercolor=C["line"],
                    lightcolor=C["card"], darkcolor=C["line"], padding=(px(10), px(10)))
        s.map("Treeview.Heading", background=[("active", C["card"])],
              foreground=[("active", C["text"])])
        s.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])

        # Slim rounded scrollbars, one per surface they sit on
        rs = px(3)
        for prefix, trough in (("", C["card"]), ("Field.", C["field"]), ("Page.", C["bg"])):
            el = (prefix.rstrip(".") or "Card") + "Slim.thumb"
            element(el, rs, rr(rs, "#363B68", trough), ("pressed", rr(rs, "#4D5290", trough)),
                    ("active", rr(rs, "#4D5290", trough)))
            name = f"{prefix}Vertical.TScrollbar"
            s.layout(name, [("Vertical.Scrollbar.trough", {"sticky": "ns", "children": [
                (el, {"expand": "1", "sticky": "nswe"})]})])
            s.configure(name, troughcolor=trough, background=trough, bordercolor=trough,
                        lightcolor=trough, darkcolor=trough, gripcount=0)

        # Checkboxes and radio buttons
        for kind in ("TCheckbutton", "TRadiobutton"):
            for prefix, bg in (("", C["bg"]), ("Card.", C["card"])):
                st = prefix + kind
                s.configure(st, background=bg, foreground=C["text"], padding=(0, px(4)),
                            focusthickness=0)
                s.map(st, background=[("active", bg)], foreground=[("disabled", C["faint"])])
        self.make_indicators(s)

    def make_indicators(self, s):
        """Own rounded checkboxes and radio buttons in the accent color."""
        n, gap = self.px(17), self.px(10)
        for name, bg, check_style, radio_style in (
                ("Page", C["bg"], "TCheckbutton", "TRadiobutton"),
                ("Card", C["card"], "Card.TCheckbutton", "Card.TRadiobutton")):
            off = draw_checkbox(self.root, n, bg, C["field"], C["border_hover"], False)
            on = draw_checkbox(self.root, n, bg, C["accent"], C["accent"], True)
            off_dim = draw_checkbox(self.root, n, bg, C["card"], C["border"], False)
            on_dim = draw_checkbox(self.root, n, bg, C["accent_off"], C["accent_off"], True)
            r_off = draw_radio(self.root, n, bg, C["field"], C["border_hover"], None)
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
        r, px = self.root, self.px
        r.title("UserAtlas")
        self.place_window()
        r.columnconfigure(0, weight=0)   # sidebar (fixed width)
        r.columnconfigure(1, weight=0)   # hairline
        r.columnconfigure(2, weight=1)   # pages
        r.rowconfigure(0, weight=1)

        # ---- Sidebar: brand, the pages, and everything that applies to a whole run ----
        side = tk.Frame(r, bg=C["surface"], width=px(240))
        side.grid(row=0, column=0, sticky="ns")
        side.pack_propagate(False)
        tk.Frame(r, bg=C["line"], width=1).grid(row=0, column=1, sticky="ns")

        brand = tk.Frame(side, bg=C["surface"])
        brand.pack(fill="x", padx=px(24), pady=(px(28), px(30)))
        n = px(34)
        tile = paint_rounded(r, n, n, px(10), C["accent"], C["surface"])
        self.images.append(tile)
        tk.Label(brand, image=tile, text="@", compound="center", fg="#FFFFFF",
                 bg=C["surface"], font=self.f["brand"], bd=0).pack(side="left")
        tk.Label(brand, text="UserAtlas", bg=C["surface"], fg=C["text"],
                 font=self.f["brand"]).pack(side="left", padx=(px(12), 0))

        nav = tk.Frame(side, bg=C["surface"])
        nav.pack(fill="x", padx=px(14))
        self.tab_widgets = {}
        for key, title in self.TABS:
            label = ttk.Label(nav, text=title, style="Nav.TLabel", cursor="hand2")
            label.pack(fill="x", pady=(0, px(3)))
            badge = ttk.Label(label, text="", style="NavBadge.TLabel", cursor="hand2")
            for w in (label, badge):
                w.bind("<Button-1>", lambda e, k=key: self.show_tab(k))
                w.bind("<Enter>", lambda e, k=key: self.tab_hover(k, True))
                w.bind("<Leave>", lambda e, k=key: self.tab_hover(k, False))
            self.tab_widgets[key] = (label, label, badge)

        foot = tk.Frame(side, bg=C["surface"])
        foot.pack(side="bottom", fill="x", padx=px(20), pady=(px(12), px(24)))
        self.summary_text = tk.StringVar()
        ttk.Label(foot, textvariable=self.summary_text, style="Bar.Muted.TLabel").pack(
            anchor="w", pady=(0, px(12)))

        self.update_pill = ttk.Frame(foot, style="Notice.TFrame", padding=(px(12), px(9)),
                                     cursor="hand2")
        self.update_text = ttk.Label(self.update_pill, text="", style="Notice.TLabel",
                                     cursor="hand2")
        self.update_text.pack(side="left")
        self.update_button = ttk.Label(self.update_pill, text="Update",
                                       style="NoticeAction.TLabel", cursor="hand2")
        self.update_button.pack(side="right")
        for w in (self.update_pill, self.update_text, self.update_button):
            w.bind("<Button-1>", lambda e: self.click_update())

        # One slot for the main action: Start, or Stop while a run is going
        self.action_slot = tk.Frame(foot, bg=C["surface"])
        self.action_slot.pack(fill="x")
        self.start_button = ttk.Button(self.action_slot, text="Start checking",
                                       style="Accent.TButton", command=self.start)
        self.start_button.pack(fill="x")
        self.stop_button = ttk.Button(self.action_slot, text="Stop checking",
                                      style="Stop.TButton", command=self.stopping,
                                      state="disabled")

        self.status = tk.StringVar(value="Ready when you are.")
        ttk.Label(foot, textvariable=self.status, style="Bar.Muted.TLabel",
                  wraplength=px(196), justify="left").pack(anchor="w", pady=(px(14), 0))
        self.progress = ttk.Progressbar(foot, style="Accent.Horizontal.TProgressbar",
                                        mode="determinate")  # shown once a run starts

        # ---- Pages: stacked, the current one raised ----
        holder = ttk.Frame(r)
        holder.grid(row=0, column=2, sticky="nsew")
        holder.columnconfigure(0, weight=1)
        holder.rowconfigure(0, weight=1)
        self.pages = {}
        for key, _ in self.TABS:
            p = ttk.Frame(holder, padding=(px(40), px(34), px(40), px(30)))
            p.grid(row=0, column=0, sticky="nsew")
            self.pages[key] = p
        self.build_names(self.pages["names"])
        self.build_platforms(self.pages["platforms"])
        self.build_results(self.pages["results"])
        self.build_selftest(self.pages["selftest"])
        self.build_settings(self.pages["settings"])

    # -- window size, settings file and small building blocks

    def read_settings(self) -> dict:
        try:
            with open(self.settings_path, encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except (OSError, ValueError):
            return {}

    def write_settings(self, **changes) -> Optional[str]:
        """Merge `changes` into settings.json. Returns an error text, or None."""
        data = self.read_settings()
        data.update(changes)
        try:
            os.makedirs(os.path.dirname(self.settings_path) or ".", exist_ok=True)
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(data, f)
        except OSError as e:
            return str(e)
        return None

    def place_window(self):
        """Open big: the size you left it at, or most of the screen, centered."""
        r, px = self.root, self.px
        sw, sh = r.winfo_screenwidth(), r.winfo_screenheight()
        min_w, min_h = min(px(1120), sw - 40), min(px(700), sh - 80)
        r.minsize(min_w, min_h)
        saved = self.read_settings().get("window")
        if isinstance(saved, dict):
            try:
                w, h, x, y = (int(saved[key]) for key in ("w", "h", "x", "y"))
                if (min_w <= w <= sw and min_h <= h <= sh
                        and 0 <= x <= sw - px(200) and 0 <= y <= sh - px(120)):
                    r.geometry(f"{w}x{h}+{x}+{y}")
                    if saved.get("zoomed") and os.name == "nt":
                        r.after(0, lambda: r.state("zoomed"))
                    return
            except (KeyError, TypeError, ValueError):
                pass
        w = max(min(int(sw * 0.86), px(2000)), min_w)
        h = max(min(int(sh * 0.86), px(1300)), min_h)
        r.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 2 - px(16))}")

    def remember_window(self):
        try:
            zoomed = self.root.state() == "zoomed"
            m = re.match(r"(\d+)x(\d+)\+(-?\d+)\+(-?\d+)", self.root.geometry())
        except tk.TclError:
            return
        window = dict(self.read_settings().get("window") or {}) if zoomed else {}
        if m and not zoomed:
            window.update(zip(("w", "h", "x", "y"), map(int, m.groups())))
        if window:
            window["zoomed"] = zoomed
            self.write_settings(window=window)

    def page_header(self, p, title, description="", variable=None, scroll=False):
        """Big page title with a description; returns (actions, body)."""
        px = self.px
        head = ttk.Frame(p)
        head.pack(fill="x", pady=(0, px(24)))
        # Actions are packed first so they always keep their room; the text wraps.
        actions = ttk.Frame(head)
        actions.pack(side="right", anchor="s", padx=(px(24), 0))
        text = ttk.Frame(head)
        text.pack(side="left", fill="x", expand=True)
        ttk.Label(text, text=title, style="PageTitle.TLabel").pack(anchor="w")
        desc = None
        if variable is not None:
            # Live text (e.g. a hover hint) gets a fixed two-line box: if its height
            # followed the text, hovering would shift the page under the pointer and
            # the hint would flicker on and off.
            line = tkfont.Font(root=self.root, font=self.f["normal"]).metrics("linespace")
            box = ttk.Frame(text, height=2 * line + px(4))
            box.pack(fill="x", pady=(px(6), 0))
            box.pack_propagate(False)
            desc = ttk.Label(box, textvariable=variable, style="PageDesc.TLabel",
                             wraplength=px(720), justify="left")
            desc.pack(anchor="nw")
        elif description:
            desc = ttk.Label(text, text=description, style="PageDesc.TLabel",
                             wraplength=px(720), justify="left")
            desc.pack(anchor="w", pady=(px(6), 0))
        if desc is not None:
            text.bind("<Configure>", lambda e: desc.configure(
                wraplength=max(px(200), min(px(720), e.width))))
        if scroll:
            body = self.scroll_area(p)
        else:
            body = ttk.Frame(p)
            body.pack(fill="both", expand=True)
        return actions, body

    def scroll_area(self, parent):
        """A page body that scrolls when a small window can't fit it all."""
        outer = ttk.Frame(parent)
        outer.pack(fill="both", expand=True)
        canvas = tk.Canvas(outer, bg=C["bg"], highlightthickness=0, borderwidth=0)
        bar = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview,
                            style="Page.Vertical.TScrollbar")
        canvas.pack(side="left", fill="both", expand=True)
        inner = ttk.Frame(canvas)
        window = canvas.create_window(0, 0, window=inner, anchor="nw")
        canvas.configure(yscrollcommand=self.autohide(bar, side="right", fill="y", before=canvas))
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=(0, 0, e.width, e.height)))
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(window, width=e.width))

        def wheel(event):
            if canvas.yview() == (0.0, 1.0):
                return
            up = getattr(event, "num", None) == 4 or getattr(event, "delta", 0) > 0
            canvas.yview_scroll(-3 if up else 3, "units")

        def inside():
            x, y = canvas.winfo_pointerxy()
            return (canvas.winfo_rootx() <= x < canvas.winfo_rootx() + canvas.winfo_width()
                    and canvas.winfo_rooty() <= y < canvas.winfo_rooty() + canvas.winfo_height())

        def hook(on):
            for sequence in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                if on:
                    canvas.bind_all(sequence, wheel)
                elif not inside():  # leaving onto a widget inside isn't leaving
                    canvas.unbind_all(sequence)
        canvas.bind("<Enter>", lambda e: hook(True))
        canvas.bind("<Leave>", lambda e: hook(False))
        return inner

    def autohide(self, bar, **pack):
        """A yscrollcommand that only shows the scrollbar when there's more to see."""
        def set_(first, last):
            first, last = float(first), float(last)
            if first <= 0.0 and last >= 1.0:
                if bar.winfo_ismapped():
                    bar.pack_forget()
            elif not bar.winfo_ismapped():
                bar.pack(**pack)
            bar.set(first, last)
        return set_

    def text_box(self, parent, height=None, font=None, surface="card"):
        """A rounded multi-line text field whose outline lights up on focus."""
        px = self.px
        border = ttk.Frame(parent, style="Field.TFrame" if surface == "card" else "PageField.TFrame",
                           padding=px(5))
        box = tk.Text(border, wrap="none", undo=True, relief="flat", borderwidth=0,
                      highlightthickness=0, padx=px(10), pady=px(8),
                      font=font or self.f["normal"], bg=C["field"], fg=C["text"],
                      insertbackground=C["text"], selectbackground=C["selected"],
                      selectforeground="#FFFFFF", spacing1=px(3), spacing3=px(3))
        if height:
            box.configure(height=height)
        scroll = ttk.Scrollbar(border, orient="vertical", command=box.yview,
                               style="Field.Vertical.TScrollbar")
        box.pack(side="left", fill="both", expand=True)
        box.configure(yscrollcommand=self.autohide(scroll, side="right", fill="y", before=box))
        box.bind("<FocusIn>", lambda e: border.state(["focus"]))
        box.bind("<FocusOut>", lambda e: border.state(["!focus"]))
        return border, box

    def fit_columns(self):
        """On a narrow window, drop the per-group columns rather than clip them."""
        base = ["name", "available", "allowed"]
        if not self.groups:
            return
        need = sum(int(self.table.column(c, "minwidth")) for c in base + self.groups)
        cols = base + (self.groups if self.table.winfo_width() >= need else [])
        current = [str(c) for c in self.table["displaycolumns"]]
        if current != cols:
            self.table.configure(displaycolumns=cols)

    def table_hover(self, event):
        """Light up the results row under the pointer."""
        row = self.table.identify_row(event.y) if event is not None else ""
        if row == self._hover_row:
            return
        for iid, on in ((self._hover_row, False), (row, True)):
            if iid and self.table.exists(iid):
                tags = [t for t in (self.table.item(iid, "tags") or ()) if t != "hover"]
                self.table.item(iid, tags=tags + (["hover"] if on else []))
        self._hover_row = row

    # -- page: Names

    def build_names(self, p):
        px = self.px
        actions, body = self.page_header(
            p, "Names", "Paste or type the handles you want to check, one per line. Commas and "
                        "spaces work too; an @ in front is dropped and anything after # is "
                        "ignored.")
        ttk.Button(actions, text="Load file…", style="Page.TButton",
                   command=self.load_file).pack(side="left")
        ttk.Button(actions, text="Paste", style="Page.TButton",
                   command=self.paste_names).pack(side="left", padx=(px(8), 0))
        ttk.Button(actions, text="Clear", style="Page.TButton",
                   command=self.clear_names).pack(side="left", padx=(px(8), 0))

        body.columnconfigure(0, weight=5, uniform="names")
        body.columnconfigure(1, weight=7, uniform="names")
        body.rowconfigure(0, weight=1)
        k = Card(body, "Your list")
        k.outer.grid(row=0, column=0, sticky="nsew", padx=(0, px(20)))
        self.name_count = tk.StringVar(value="0 names")
        ttk.Label(k.head, textvariable=self.name_count, style="Counter.TLabel").pack(side="right")
        border, self.names_box = self.text_box(k.body)
        border.pack(fill="both", expand=True)
        self.names_box.bind("<<Modified>>", self.names_changed)
        ttk.Label(k.body, style="Card.Muted.TLabel",
                  text="Ctrl+Enter starts checking.").pack(anchor="w", pady=(px(12), 0))

        # Live check against each site's naming rules (no internet needed)
        rc = Card(body, "Name rules", "Whether each site you picked allows the name. Checked "
                                      "as you type, before anything goes online.", wrap=500)
        rc.outer.grid(row=0, column=1, sticky="nsew")
        self.rules_count = tk.StringVar(value="")
        ttk.Label(rc.head, textvariable=self.rules_count, style="Counter.TLabel").pack(side="right")
        box = ttk.Frame(rc.body, style="Card.TFrame")
        box.pack(fill="both", expand=True)
        self.rules_table = ttk.Treeview(box, columns=("name", "allowed", "problem"),
                                        show="headings", selectmode="browse", height=8)
        for col, title, width, stretch, anchor in (("name", "Name", 170, False, "w"),
                                                   ("allowed", "Allowed", 96, False, "center"),
                                                   ("problem", "Why not", 260, True, "w")):
            self.rules_table.heading(col, text=title, anchor=anchor)
            self.rules_table.column(col, width=px(width), minwidth=px(60), stretch=stretch,
                                    anchor=anchor)
        self.rules_table.tag_configure("fits", foreground=C["green"])
        self.rules_table.tag_configure("issue", foreground=C["amber"])
        self.rules_table.tag_configure("blocked", foreground=C["red"])
        rs = ttk.Scrollbar(box, orient="vertical", command=self.rules_table.yview)
        self.rules_table.pack(side="left", fill="both", expand=True)
        self.rules_table.configure(yscrollcommand=self.autohide(
            rs, side="right", fill="y", before=self.rules_table))
        self.rules_table.bind("<<TreeviewSelect>>", lambda e: self.show_rule_detail())
        self.rules_empty = ttk.Label(box, style="Card.Muted.TLabel", justify="center",
                                     text="Names appear here as you type.")
        self.rules_empty.place(relx=0.5, rely=0.45, anchor="center")

        detail = ttk.Frame(rc.body, style="Field.TFrame", padding=px(5))
        detail.pack(fill="x", pady=(px(14), 0))
        self.rules_detail = tk.Text(detail, height=6, wrap="word", state="disabled",
                                    relief="flat", borderwidth=0, highlightthickness=0,
                                    padx=px(10), pady=px(8), font=self.f["small"], bg=C["field"],
                                    fg=C["text"], spacing1=px(2), spacing3=px(2),
                                    selectbackground=C["selected"])
        self.rules_detail.tag_configure("head", font=self.f["small_bold"], foreground="#FFFFFF")
        self.rules_detail.tag_configure("site", font=self.f["small_bold"], foreground=C["text"])
        self.rules_detail.tag_configure("ok", foreground=C["green"])
        self.rules_detail.tag_configure("muted", foreground=C["muted"])
        self.rules_detail.tag_configure("blocked", foreground=C["red"])
        self.rules_detail.pack(fill="both", expand=True)
        self.rules_after = None
        self.show_rule_detail()

    # -- page: Platforms

    def build_platforms(self, p):
        px = self.px
        self.platform_hint_default = "Hover a platform to see its naming rules."
        self.platform_hint = tk.StringVar(value=self.platform_hint_default)
        actions, body = self.page_header(p, "Platforms", variable=self.platform_hint, scroll=True)
        self.platform_count = tk.StringVar()
        ttk.Label(actions, textvariable=self.platform_count, style="PageCounter.TLabel").pack(
            side="left", padx=(0, px(16)))
        ttk.Button(actions, text="Select all", style="Page.TButton",
                   command=lambda: self.set_all(True)).pack(side="left")
        ttk.Button(actions, text="Clear all", style="Page.TButton",
                   command=lambda: self.set_all(False)).pack(side="left", padx=(px(8), 0))

        columns = 6
        self.checks: Dict[str, tk.BooleanVar] = {}
        self.group_counts: Dict[str, tk.StringVar] = {}
        for gi, group in enumerate(GROUPS):
            section = ttk.Frame(body)
            section.pack(fill="x", padx=(0, px(8)), pady=(0 if gi == 0 else px(24), 0))
            row = ttk.Frame(section)
            row.pack(fill="x")
            ttk.Label(row, text=GROUP_TITLES[group], style="SectionTitle.TLabel").pack(side="left")
            ttk.Label(row, text=GROUP_HINTS[group], style="Page.TLabel").pack(
                side="left", padx=(px(12), 0), pady=(px(3), 0))
            ttk.Button(row, text="None", style="Page.Link.TButton",
                       command=lambda g=group: self.set_group(g, False)).pack(side="right")
            ttk.Button(row, text="All", style="Page.Link.TButton",
                       command=lambda g=group: self.set_group(g, True)).pack(
                side="right", padx=(0, px(12)))
            counter = tk.StringVar()
            self.group_counts[group] = counter
            ttk.Label(row, textvariable=counter, style="PageCounter.TLabel").pack(
                side="right", padx=(0, px(18)))

            grid = ttk.Frame(section)
            grid.pack(fill="x", pady=(px(12), 0))
            for c in range(columns):
                grid.columnconfigure(c, weight=1, uniform="chips")
            if group == "domains":
                domain_rules = all_platforms(["com"])[-1].rules.describe()
                items = [(f"domain.{t}", f".{t}", f".{t} domains: {domain_rules}")
                         for t in split_list(STANDARD_TLDS)]
            else:
                items = [(q.key, q.short_title, f"{q.short_title} names: {q.rules.describe()}")
                         for q in self.everything if q.group == group]
            for i, (key, text, rule_text) in enumerate(items):
                v = tk.BooleanVar(value=True)
                v.trace_add("write", lambda *_: self.update_summary())
                self.checks[key] = v
                chip = ttk.Checkbutton(grid, text=text, variable=v, style="Chip.TCheckbutton",
                                       cursor="hand2")
                chip.grid(row=i // columns, column=i % columns, sticky="ew",
                          padx=(0, px(10)), pady=(0, px(10)))
                chip.bind("<Enter>", lambda e, t=rule_text: self.platform_hint.set(t))
                chip.bind("<Leave>", lambda e: self.platform_hint.set(self.platform_hint_default))
            if group == "domains":
                extra = ttk.Frame(section)
                extra.pack(fill="x", pady=(px(6), 0))
                ttk.Label(extra, text="Other extensions").pack(side="left")
                self.extra_tlds = tk.StringVar()
                self.extra_tlds.trace_add("write", lambda *_: self.update_summary())
                ttk.Entry(extra, textvariable=self.extra_tlds, style="Page.TEntry",
                          width=22).pack(side="left", padx=(px(14), px(14)))
                ttk.Label(extra, text="For example: de, be, app", style="Page.TLabel").pack(
                    side="left")

    # -- page: Results

    def build_results(self, p):
        px = self.px
        actions, body = self.page_header(
            p, "Results", "Every name against every platform. Click a column to sort, and pick "
                          "a name to see where it's free.")
        self.search = tk.StringVar()
        self.search.trace_add("write", lambda *_: self.show())
        search = ttk.Entry(actions, textvariable=self.search, style="Page.TEntry", width=22)
        search.pack(side="left")
        hint = ttk.Label(actions, text="Search names", style="SearchHint.TLabel",
                         cursor="xterm")

        def place_hint(*_):
            try:
                focused = self.root.focus_get() is search
            except (KeyError, tk.TclError):
                focused = False
            if self.search.get() or focused:
                hint.place_forget()
            else:
                hint.place(in_=search, x=px(13), rely=0.5, anchor="w")
        hint.bind("<Button-1>", lambda e: search.focus_set())
        search.bind("<FocusIn>", place_hint, add="+")
        search.bind("<FocusOut>", place_hint, add="+")
        self.search.trace_add("write", place_hint)
        self.root.after_idle(place_hint)
        self.only_available = tk.BooleanVar(value=False)
        ttk.Checkbutton(actions, text="Only names free somewhere", variable=self.only_available,
                        command=self.show).pack(side="left", padx=(px(20), px(20)))
        ttk.Button(actions, text="Export CSV…", style="Page.TButton",
                   command=self.export).pack(side="left")

        body.columnconfigure(0, weight=1)
        body.rowconfigure(0, weight=1)
        # The detail panel takes about a third of the room, within sensible bounds.
        body.bind("<Configure>", lambda e: body.columnconfigure(
            1, minsize=max(px(360), min(px(470), int(e.width * 0.36)))))
        left = Card(body, padding=(10, 8))
        left.outer.grid(row=0, column=0, sticky="nsew", padx=(0, px(20)))
        self.table = ttk.Treeview(left.body, show="headings", selectmode="browse")
        ys = ttk.Scrollbar(left.body, orient="vertical", command=self.table.yview)
        self.table.pack(side="left", fill="both", expand=True)
        self.table.configure(yscrollcommand=self.autohide(ys, side="right", fill="y",
                                                          before=self.table))
        self.table.tag_configure("allavailable", background=C["row_free"])
        self.table.tag_configure("noneavailable", foreground=C["faint"])
        self.table.tag_configure("hover", background=C["hover"])
        self._hover_row = ""
        self.table.bind("<Configure>", lambda e: self.fit_columns(), add="+")
        self.table.bind("<Motion>", self.table_hover)
        self.table.bind("<Leave>", lambda e: self.table_hover(None))
        self.table.bind("<<TreeviewSelect>>", self.selection)
        self.empty = ttk.Label(left.body, style="Card.Muted.TLabel", justify="center",
                               text="No results yet.\n"
                                    "Add names, then press Start checking.")
        self.empty.place(relx=0.5, rely=0.42, anchor="center")

        right = Card(body, padding=(26, 24))
        right.outer.grid(row=0, column=1, sticky="nsew")
        self.detail = right.body
        self._pill_cols = 3
        self.detail.bind("<Configure>", lambda e: self.root.after_idle(self.refit_pills))
        self.build_table([], [])
        self.show_detail(None)

    # -- page: Self-test & log

    def build_selftest(self, p):
        px = self.px
        actions, body = self.page_header(
            p, "Self-test & log", "Before a run, each platform gets a name that must be taken "
                                  "and a random one that must be free. Platforms that get it "
                                  "wrong are skipped, so you never see a false ‘available’.")
        self.test_button = ttk.Button(actions, text="Run self-test", style="Page.TButton",
                                      command=lambda: self.start(only_selftest=True))
        self.test_button.pack(side="left")
        body.columnconfigure(0, weight=1)
        body.rowconfigure(0, weight=3)
        body.rowconfigure(1, weight=2)
        k = Card(body, padding=(10, 8))
        k.outer.grid(row=0, column=0, sticky="nsew", pady=(0, px(20)))
        box = ttk.Frame(k.body, style="Card.TFrame")
        box.pack(fill="both", expand=True)
        self.test_table = ttk.Treeview(box, columns=("platform", "group", "state", "why"),
                                       show="headings", selectmode="none", height=6)
        for col, title, width, stretch in (("platform", "Platform", 220, False),
                                           ("group", "Group", 130, False),
                                           ("state", "Status", 220, False),
                                           ("why", "Details", 320, True)):
            self.test_table.heading(col, text=title, anchor="w")
            self.test_table.column(col, width=px(width), stretch=stretch, anchor="w")
        self.test_table.tag_configure("works", foreground=C["text"])
        self.test_table.tag_configure("not working", foreground=C["amber"])
        self.test_table.tag_configure("busy", foreground=C["accent_text"])
        self.test_table.tag_configure("", foreground=C["faint"])
        ts = ttk.Scrollbar(box, orient="vertical", command=self.test_table.yview)
        self.test_table.pack(side="left", fill="both", expand=True)
        self.test_table.configure(yscrollcommand=self.autohide(
            ts, side="right", fill="y", before=self.test_table))

        m = Card(body, "Activity")
        m.outer.grid(row=1, column=0, sticky="nsew")
        ttk.Button(m.head, text="Clear", style="Link.TButton", command=self.clear_log).pack(
            side="right")
        self.log_box = tk.Text(m.body, height=5, wrap="word", state="disabled", relief="flat",
                               borderwidth=0, highlightthickness=0, font=self.f["small"],
                               bg=C["card"], fg=C["text"], spacing1=px(3), spacing3=px(3),
                               selectbackground=C["selected"])
        self.log_box.tag_configure("time", foreground=C["faint"])
        ls = ttk.Scrollbar(m.body, orient="vertical", command=self.log_box.yview)
        ls.pack(side="right", fill="y")
        self.log_box.configure(yscrollcommand=ls.set)
        self.log_box.pack(side="left", fill="both", expand=True)

    # -- page: Settings

    def build_settings(self, p):
        px = self.px
        _, body = self.page_header(p, "Settings", scroll=True)
        body.columnconfigure(0, weight=1, uniform="settings")
        body.columnconfigure(1, weight=1, uniform="settings")
        columns = [ttk.Frame(body), ttk.Frame(body)]
        columns[0].grid(row=0, column=0, sticky="nsew", padx=(0, px(56)))
        columns[1].grid(row=0, column=1, sticky="nsew")
        wrap = px(500)
        flowing = {0: [], 1: []}  # labels that wrap to their column's actual width

        def flow(column, label, indent=0):
            flowing[column].append((label, indent))
            return label

        for i, column in enumerate(columns):
            column.bind("<Configure>", lambda e, i=i: [
                label.configure(wraplength=max(px(160), min(px(560), e.width - indent)))
                for label, indent in flowing[i]])

        def section(column, title, description=None):
            parent = columns[column]
            if parent.winfo_children():
                tk.Frame(parent, bg=C["line"], height=1).pack(fill="x", pady=px(24))
            ttk.Label(parent, text=title, style="SectionTitle.TLabel").pack(anchor="w")
            if description:
                flow(column, ttk.Label(parent, text=description, style="Page.TLabel",
                                       wraplength=wrap, justify="left")).pack(
                    anchor="w", pady=(px(4), 0))
            box = ttk.Frame(parent)
            box.pack(fill="x", pady=(px(14), 0))
            return box

        box = section(0, "Speed", "The calmer, the smaller the chance a site briefly blocks you.")
        self.speed = tk.DoubleVar(value=1.0)
        for title, factor, hint in SPEEDS:
            ttk.Radiobutton(box, text=title, value=factor, variable=self.speed).pack(anchor="w")
            flow(0, ttk.Label(box, text=hint, style="Page.TLabel", wraplength=wrap,
                              justify="left"), px(27)).pack(anchor="w", padx=(px(27), 0),
                                                            pady=(0, px(8)))

        box = section(0, "When starting")
        self.selftest_on = tk.BooleanVar(value=True)
        self.recheck = tk.BooleanVar(value=False)
        for var, title, hint in (
                (self.selftest_on, "Run a self-test first",
                 "Recommended. Platforms that don't answer properly right now are skipped."),
                (self.recheck, "Check earlier results again",
                 "Normally, names that were already checked aren't checked again.")):
            ttk.Checkbutton(box, text=title, variable=var).pack(anchor="w")
            flow(0, ttk.Label(box, text=hint, style="Page.TLabel", wraplength=wrap,
                              justify="left"), px(27)).pack(anchor="w", padx=(px(27), 0),
                                                            pady=(0, px(8)))

        box = section(0, "Storage", "Every result is saved right away. Stop halfway and the "
                                    "next run carries on where you left off.")
        field_ = ttk.Entry(box, style="Page.TEntry")
        field_.insert(0, self.log_path)
        field_.configure(state="readonly")
        field_.pack(side="left", fill="x", expand=True)
        ttk.Button(box, text="Open folder", style="Page.TButton",
                   command=self.open_folder).pack(side="left", padx=(px(10), 0))

        box = section(1, "Proxies", "Optional. Paste one proxy per line as IP:PORT:USER:PASS, "
                                    "the way most providers hand them out. IP:PORT and full "
                                    "URLs such as socks5h://host:port work too. With several, "
                                    "checks rotate through them and switch when one gets "
                                    "rate-limited. SOCKS needs 'pip install requests[socks]'.")
        border, self.proxy_box = self.text_box(box, height=4, font=self.f["small"],
                                               surface="page")
        border.pack(fill="x")
        # Faintly show the expected format in the empty box as a hint.
        self._proxy_ph = "IP:PORT:USER:PASS\n(one proxy per line)"
        self._proxy_ph_on = False
        self.proxy_box.bind("<FocusIn>", lambda e: self._proxy_hide_ph(), add="+")
        self.proxy_box.bind("<FocusOut>", lambda e: self._proxy_show_ph(), add="+")
        self._proxy_show_ph()
        row = ttk.Frame(box)
        row.pack(fill="x", pady=(px(10), 0))
        ttk.Button(row, text="Test proxies", style="Page.TButton",
                   command=self.test_proxy).pack(side="left")
        ttk.Button(row, text="Save proxies", style="Page.TButton",
                   command=self.save_proxy).pack(side="left", padx=(px(8), 0))
        self.proxy_status = tk.StringVar(value="")
        flow(1, ttk.Label(box, textvariable=self.proxy_status, style="Page.TLabel",
                          wraplength=wrap, justify="left")).pack(anchor="w", pady=(px(8), 0))

        box = section(1, "Reddit API keys",
                      "Reddit only answers apps that use its official API. Create a "
                      "'script' app on Reddit's app page and paste its ID (under the app "
                      "name) and secret here. Reddit may first ask you to request API "
                      "access. Without keys, Reddit is skipped.")
        self.reddit_id = tk.StringVar(value=_reddit["id"])
        self.reddit_secret = tk.StringVar(value=_reddit["secret"])
        for title, var, show in (("App ID", self.reddit_id, ""),
                                 ("Secret", self.reddit_secret, "•")):
            row = ttk.Frame(box)
            row.pack(fill="x", pady=(0, px(8)))
            ttk.Label(row, text=title, width=8).pack(side="left")
            ttk.Entry(row, textvariable=var, show=show, style="Page.TEntry").pack(
                side="left", fill="x", expand=True)
        row = ttk.Frame(box)
        row.pack(fill="x", pady=(px(2), 0))
        ttk.Button(row, text="Save keys", style="Page.TButton",
                   command=self.save_reddit_keys).pack(side="left")
        ttk.Button(row, text="Open Reddit's app page", style="Page.Link.TButton",
                   command=lambda: webbrowser.open(REDDIT_APPS_URL)).pack(
            side="left", padx=(px(16), 0))
        self.reddit_status = tk.StringVar(value="")
        flow(1, ttk.Label(box, textvariable=self.reddit_status, style="Page.TLabel",
                          wraplength=wrap, justify="left")).pack(anchor="w", pady=(px(8), 0))

        box = section(1, "Version")
        ttk.Label(box, text=f"UserAtlas {VERSION}", style="Strong.TLabel").pack(anchor="w")
        if LAUNCHER:
            origin = ("just fetched from GitHub" if LAUNCHER.get("source") == "github"
                      else "offline copy")
            below = f"App {str(LAUNCHER.get('commit', ''))[:7]}, {origin}."
        else:
            below = "Running as a plain script."
        ttk.Label(box, text=below, style="Page.TLabel").pack(anchor="w", pady=(px(2), 0))
        self.update_status = tk.StringVar(value="")
        ttk.Label(box, textvariable=self.update_status, style="Page.TLabel").pack(anchor="w")
        row = ttk.Frame(box)
        row.pack(fill="x", pady=(px(10), 0))
        self.check_button = ttk.Button(row, text="Check for updates", style="Page.TButton",
                                       command=lambda: self.check_updates(manual=True))
        self.check_button.pack(side="left")
        ttk.Button(row, text="View on GitHub", style="Page.Link.TButton",
                   command=lambda: webbrowser.open(f"https://github.com/{GITHUB_REPO}")
                   ).pack(side="left", padx=(px(16), 0))

        box = section(1, "About results")
        flow(1, ttk.Label(box, wraplength=wrap, justify="left",
                          text="‘Available’ (✓) means the site itself confirmed the name can "
                               "be taken, through the check its sign-up form uses or the "
                               "official registry. ‘Probably free’ (○) means no account was "
                               "found, but the site has no public way to confirm it: banned, "
                               "deleted or private accounts can still hold such a name "
                               "(TikTok, YouTube, Snapchat, SoundCloud and X work this way). "
                               "Click a platform on the Results page to go straight to its "
                               "page.")).pack(anchor="w")

    # ----- tabs -------------------------------------------------------------

    def show_tab(self, key):
        self.current_tab = key
        self.pages[key].tkraise()
        for k, (label, _, badge) in self.tab_widgets.items():
            state = ["selected"] if k == key else ["!selected"]
            label.state(state)
            badge.state(state)
        if key == "selftest" and not self.busy:
            self.fill_test_table(self.chosen_platforms(quiet=True))

    def tab_hover(self, key, inside):
        label, _, badge = self.tab_widgets[key]
        if not inside:
            # moving onto the badge inside the row isn't leaving the row
            try:
                under = self.root.winfo_containing(*self.root.winfo_pointerxy())
            except (KeyError, tk.TclError):
                under = None
            if under in (label, badge):
                return
        state = ["active"] if inside else ["!active"]
        label.state(state)
        badge.state(state)

    def set_badge(self, key, text, warning=False):
        badge = self.tab_widgets[key][2]
        text = text.replace("⚠", "").strip()
        if text:
            badge.configure(text=text)
            badge.place(relx=1.0, x=-self.px(14), rely=0.5, anchor="e")
        else:
            badge.place_forget()

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
                self.group_counts[group].set(f"{on} of {len(keys)}")
            total += on
        self.platform_count.set(f"{total} selected")
        plats = f"{total} {'platform' if total == 1 else 'platforms'}"
        self.summary_text.set(f"{n} {'name' if n == 1 else 'names'} on {plats}" if n
                              else f"No names yet, {plats} picked")
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
                first = "Contains a blocked word"
                tag = "blocked"
            elif broken:
                q, why = broken[0]
                first = f"{q.short_title}: {why}"
                if len(broken) > 1:
                    first += f"  (+{len(broken) - 1} more)"
                tag = "issue"
            else:
                first = "Allowed everywhere"
                tag = "fits"
            self.rules_table.insert("", "end", iid=name.lower(), tags=(tag,),
                                    values=("  " + name,
                                            f"{len(platforms) - len(broken)} of {len(platforms)}",
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
        if len(names) > 500:
            self.status.set(f"Preparing {len(names)} names…")
            self.root.update_idletasks()
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
        self.start_button.configure(state="disabled" if busy else "normal")
        self.test_button.configure(state="disabled" if busy else "normal")
        self.stop_button.configure(state="normal" if busy else "disabled")
        # The sidebar holds one main action: Start, swapped for Stop during a run.
        if busy:
            self.start_button.pack_forget()
            self.stop_button.pack(fill="x")
            if not self.progress.winfo_ismapped():
                self.progress.pack(fill="x", pady=(self.px(12), 0))
        else:
            self.stop_button.pack_forget()
            self.start_button.pack(fill="x")
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
        self.remember_window()
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
            for _ in range(2000):
                message = self.events.get_nowait()
                getattr(self, "on_" + message[0])(*message[1:])
        except queue.Empty:
            pass
        self.flush_dirty()
        if self.refresh_detail:
            self.refresh_detail = False
            self.show_detail(self.selected)
        if self.busy and self.phase == "checking" and time.time() - self.last_status > 0.5:
            self.last_status = time.time()
            rest = max((self.remaining.get(q.key, 0) * (q.delay * self.factor + 0.6)
                        for q in self.platforms if q.key not in self.skipped), default=0)
            self.status.set(f"{self.done_count} of {self.total} checks done, "
                            f"{duration_text(rest)} to go.")
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
        # Don't redraw here — a bulk run would redraw each row P times. Mark the
        # row dirty and let process() flush it once per tick (see flush_dirty).
        self.dirty.add(name)
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
            self.invalidate_active()          # skipped set changed
            self.dirty.update(self.names)     # every row's denominator shifts
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
        if self._active_cache is None:
            self._active_cache = [q for q in self.platforms if q.key not in self.skipped]
        if group is None:
            return self._active_cache
        return [q for q in self._active_cache if q.group == group]

    def invalidate_active(self):
        self._active_cache = None

    def problem_for(self, name, q) -> bool:
        """Cached bool(q.problem(name)). problem() runs the blocked-word filter
        and rule checks, which are static for a run — caching keeps them out of
        the per-result render path that a bulk run hammers."""
        k = (name.lower(), q.key)
        v = self._problem_cache.get(k)
        if v is None:
            v = bool(q.problem(name))
            self._problem_cache[k] = v
        return v

    def status_of(self, name, q) -> str:
        return self.results.get((name.lower(), q.key), ("", ""))[0]

    def available_count(self, name, group: Optional[str] = None) -> int:
        return sum(1 for q in self.active_platforms(group) if self.status_of(name, q) == AVAILABLE)

    def likely_count(self, name, group: Optional[str] = None) -> int:
        return sum(1 for q in self.active_platforms(group) if self.status_of(name, q) == LIKELY)

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
        self._problem_cache = {}     # fresh run: names/platforms may have changed
        self.invalidate_active()
        self.dirty = set()
        self.table.configure(columns=cols, displaycolumns=cols)
        px = self.px
        self.headings = {"name": "Name", "available": "Available", "allowed": "Allowed"}
        self.table.column("name", width=px(200), minwidth=px(120), stretch=True, anchor="w")
        self.table.column("available", width=px(110), minwidth=px(84), stretch=True,
                          anchor="center")
        self.table.column("allowed", width=px(100), minwidth=px(80), stretch=True,
                          anchor="center")
        for g in self.groups:
            self.headings[g] = GROUP_TITLES[g]
            self.table.column(g, width=px(100), minwidth=px(80), stretch=True, anchor="center")
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
        self.fit_columns()

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
        likely = f" (+{st.count(LIKELY)})" if LIKELY in st else ""
        return (f"{st.count(AVAILABLE)}{likely} of {len(platforms)}"
                + ("" if all(st) else "  …"))

    def allowed_count(self, name) -> int:
        """Platforms whose rules (and own answer) allow this name."""
        return sum(1 for q in self.active_platforms()
                   if self.status_of(name, q) != INVALID and not self.problem_for(name, q))

    def row_values(self, name):
        active = self.active_platforms()
        return (["  " + name, self.count_text(name, active),
                 f"{self.allowed_count(name)} of {len(active)}"]
                + [self.count_text(name, self.active_platforms(g)) for g in self.groups])

    def row_tags(self, name):
        st = [self.status_of(name, q) for q in self.active_platforms()]
        if not st or not all(st):
            return ()
        if self.available_everywhere(name):
            return ("allavailable",)
        if not FREE & set(st):
            return ("noneavailable",)
        return ()

    def update_row(self, name):
        iid = name.lower()
        if not self.table.exists(iid):
            return
        tags = self.row_tags(name) + (("hover",) if iid == self._hover_row else ())
        self.table.item(iid, values=self.row_values(name), tags=tags)
        if iid in self.hidden and self.visible(name):
            self.table.move(iid, "", "end")
            self.hidden.discard(iid)

    def refresh_rows(self):
        for name in self.names:
            self.update_row(name)

    def flush_dirty(self):
        """Redraw the rows that changed since the last tick, in one batch, and
        advance the progress bar. Keeps a big run from freezing the UI."""
        if self.busy and self.phase == "checking":
            try:
                self.progress["value"] = self.done_count
            except tk.TclError:
                pass
        if not self.dirty:
            return
        names, self.dirty = self.dirty, set()
        for name in names:
            self.update_row(name)

    def visible(self, name) -> bool:
        term = self.search.get().strip().lower()
        if term and term not in name.lower():
            return False
        return not (self.only_available.get() and self.available_count(name) == 0
                    and self.likely_count(name) == 0)

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
            group = None if col == "available" else col
            return (-self.available_count(name, group), -self.likely_count(name, group))

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
            self.show_detail(self.table.set(sel[0], "name").strip())

    def show_detail(self, name):
        px = self.px
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
            ttk.Label(self.detail, text="Pick a name", style="Heading.TLabel").pack(anchor="w")
            ttk.Label(self.detail, style="Card.Muted.TLabel", wraplength=px(340), justify="left",
                      text="You'll see on each platform whether it's free. ✓ is confirmed by "
                           "the site, ○ means no account was found but the site can't confirm "
                           "it. Click a platform to open its page.").pack(anchor="w", pady=(px(6), px(22)))
            grid = ttk.Frame(self.detail, style="Card.TFrame")
            grid.pack(fill="x")
            for c in range(2):
                grid.columnconfigure(c, weight=1, uniform="legend")
            for i, (kind, text) in enumerate(((AVAILABLE, "Available"), (LIKELY, "Probably free"),
                                              (TAKEN, "Taken"), (INVALID, "Not allowed"),
                                              (UNKNOWN, "Unknown"), ("waiting", "Checking"),
                                              ("skipped", "Skipped"))):
                ttk.Label(grid, text=f"{CHIP[kind][2]}  {text}", style=self.pill_styles[kind]).grid(
                    row=i // 2, column=i % 2, sticky="ew", padx=(0, px(8)), pady=(0, px(8)))
            return

        head = ttk.Frame(self.detail, style="Card.TFrame")
        head.pack(fill="x")
        ttk.Label(head, text=name, style="Big.TLabel", wraplength=px(290)).pack(side="left")
        ttk.Button(head, text="Copy", style="Link.TButton",
                   command=lambda: self.copy(name)).pack(side="right", anchor="n", pady=(px(8), 0))
        active = self.active_platforms()
        waiting = sum(1 for q in active if not self.status_of(name, q))
        likely = self.likely_count(name)
        ttk.Label(self.detail, text=f"Available on {self.available_count(name)} of "
                                    f"{len(active)} platforms"
                                    + (f", probably free on {likely} more" if likely else ""),
                  style="Card.Muted.TLabel").pack(anchor="w", pady=(px(2), 0))
        if waiting and self.busy:
            ttk.Label(self.detail, text=f"{waiting} still checking",
                      style="Card.Muted.TLabel").pack(anchor="w")

        # The hint sits at the bottom and is placed first, so it's always visible.
        default = "Hover a platform for details; click one to open its page."
        self.hint = tk.StringVar(value=default)
        # A fixed two-line box, filled edge to edge, so a shorter hint fully
        # replaces a longer one and the platforms above never shift.
        line = tkfont.Font(font=self.f["normal"]).metrics("linespace")
        box = ttk.Frame(self.detail, style="Card.TFrame", height=line * 2 + px(4))
        box.pack(side="bottom", fill="x", pady=(px(12), 0))
        box.pack_propagate(False)
        hint = ttk.Label(box, textvariable=self.hint, style="Card.Muted.TLabel",
                         wraplength=px(350), justify="left", anchor="nw")
        hint.pack(fill="both", expand=True)
        box.bind("<Configure>", lambda e: hint.configure(wraplength=max(px(120), e.width)))

        # The platforms sit in a scrollable area, for small windows or many extensions.
        holder = ttk.Frame(self.detail, style="Card.TFrame")
        holder.pack(fill="both", expand=True, pady=(px(6), 0))
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
        canvas.bind("<Configure>", lambda e: (canvas.itemconfigure(window_id, width=e.width),
                                              arrange()))
        for button in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            canvas.bind(button, self.wheel)
        if position:
            self.root.after_idle(lambda: canvas.yview_moveto(position))

        per_row = self._pill_cols = self.pill_columns()
        for group in GROUPS:
            ps = [q for q in self.platforms if q.group == group]
            if not ps:
                continue
            ttk.Label(inner, text=GROUP_TITLES[group],
                      style="Section.TLabel").pack(anchor="w", pady=(px(16), px(8)))
            grid = ttk.Frame(inner, style="Card.TFrame")
            grid.pack(fill="x")
            for c in range(per_row):
                grid.columnconfigure(c, weight=1, uniform="chip")
            for i, q in enumerate(ps):
                self.chip(grid, name, q, default).grid(row=i // per_row, column=i % per_row,
                                                       sticky="ew", padx=(0, px(6)),
                                                       pady=(0, px(6)))

    def pill_columns(self) -> int:
        """Three platform pills per row, or two when the panel is narrow."""
        width = self.detail.winfo_width()
        return 3 if width <= 1 or width >= self.px(340) else 2

    def refit_pills(self):
        if self.selected and self.pill_columns() != self._pill_cols:
            self.show_detail(self.selected)

    def chip(self, parent, name, q, default):
        status, detail = self.results.get((name.lower(), q.key), ("", ""))
        if not status and self.problem_for(name, q):
            status, detail = INVALID, q.problem(name)
        kind = status or ("skipped" if q.key in self.skipped
                          else "waiting" if self.busy else "")
        label = ttk.Label(parent, text=f"{CHIP.get(kind, CHIP[''])[2]}  {q.short_title}",
                          style=self.pill_styles.get(kind, self.pill_styles[""]),
                          cursor="hand2" if q.link else "")
        if kind == INVALID and detail:
            hint = f"{q.title} doesn't allow this name: {detail}."
        else:
            hint = f"{q.title}: {CHIP_TEXT.get(kind, kind)}" + (f" ({detail})" if detail else "") + "."
        if q.key == "reddit" and kind == "skipped" and not reddit_keys_set():
            hint += " Reddit needs API keys: add them in Settings."
        if q.link:
            hint += " Click to open its page."
            label.bind("<Button-1>", lambda e: webbrowser.open(q.link_for(name)))

        def enter(_):
            label.state(["active"])
            self.hint.set(hint)

        def leave(_):
            label.state(["!active"])
            self.hint.set(default)
        label.bind("<Enter>", enter)
        label.bind("<Leave>", leave)
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
        self.update_pill.pack(fill="x", pady=(0, self.px(12)), before=self.action_slot)
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
                "  " + q.title, GROUP_TITLES[q.group], "", ""))
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
            messagebox.showinfo("UserAtlas", "There's nothing to export yet. Check some "
                                             "names first.")
            return
        path = filedialog.asksaveasfilename(
            title="Export CSV", defaultextension=".csv", initialfile="overview.csv",
            filetypes=[("CSV (opens in Excel)", "*.csv")])
        if not path:
            return
        try:
            write_overview(path, self.names, self.platforms, self.results)
        except OSError as e:
            messagebox.showerror("UserAtlas", f"Exporting failed:\n{e}")
            return
        self.log(f"CSV exported: {path}")
        self.status.set("CSV exported.")

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

    # ----- proxy ------------------------------------------------------------

    def load_settings(self):
        data = self.read_settings()
        text = data.get("proxies") or data.get("proxy") or ""
        if not isinstance(text, str):
            text = ""
        apply_proxy_text(text)
        keys = data.get("reddit") if isinstance(data.get("reddit"), dict) else {}
        if keys.get("id") and keys.get("secret"):
            set_reddit_keys(str(keys["id"]), str(keys["secret"]))
        if getattr(self, "reddit_id", None) is not None:
            self.reddit_id.set(_reddit["id"])
            self.reddit_secret.set(_reddit["secret"])
            self.reddit_status.set("Keys saved; Reddit is checked through its API."
                                   if reddit_keys_set() else "")
        if getattr(self, "proxy_box", None) is not None:
            self._proxy_hide_ph()
            self.proxy_box.delete("1.0", "end")
            if text.strip():
                self.proxy_box.insert("1.0", text.strip() + "\n")
            self._proxy_show_ph()

    def _proxy_show_ph(self):
        """Show the faint IP:PORT:USER:PASS hint while the proxy box is empty."""
        box = getattr(self, "proxy_box", None)
        if box is None or box.get("1.0", "end").strip():
            return
        box.delete("1.0", "end")
        box.insert("1.0", self._proxy_ph)
        box.configure(fg=C["faint"])
        self._proxy_ph_on = True

    def _proxy_hide_ph(self):
        """Clear the hint when the user focuses or fills the box."""
        if getattr(self, "_proxy_ph_on", False):
            self.proxy_box.delete("1.0", "end")
            self.proxy_box.configure(fg=C["text"])
            self._proxy_ph_on = False

    def proxy_text(self) -> str:
        """What the user actually typed — empty while the hint is showing."""
        if getattr(self, "_proxy_ph_on", False):
            return ""
        return self.proxy_box.get("1.0", "end")

    def proxy_summary(self, valid, invalid, saved=False):
        pre = "Saved. " if saved else ""
        n = len(valid)
        if not n and not invalid:
            return pre + "Using your normal connection."
        bits = []
        if n:
            rot = " (checks rotate through them)" if n > 1 else ""
            bits.append(f"{n} {'proxy' if n == 1 else 'proxies'} active{rot}")
        if invalid:
            ex = ", ".join(shorten(x, 24) for x in invalid[:3])
            more = "" if len(invalid) <= 3 else "…"
            bits.append(f"{len(invalid)} line(s) skipped (bad format): {ex}{more}")
        return pre + "; ".join(bits) + "."

    def save_reddit_keys(self):
        client_id, secret = self.reddit_id.get().strip(), self.reddit_secret.get().strip()
        if bool(client_id) != bool(secret):
            self.reddit_status.set("Fill in both the app ID and the secret.")
            return
        set_reddit_keys(client_id, secret)
        error = self.write_settings(reddit={"id": client_id, "secret": secret})
        if error:
            self.reddit_status.set(f"Couldn't save the keys: {error}")
            return
        if not client_id:
            self.reddit_status.set("Keys removed. Reddit is skipped.")
            return
        self.reddit_status.set("Saved. Testing the keys…")

        def run():
            s = new_session()
            try:
                status, detail = check_reddit_api(s, "spez")
            except Exception as e:  # network trouble, rate limit
                status, detail = UNKNOWN, shorten(e)
            msg = ("Saved. The keys work; Reddit is checked through its API."
                   if status == TAKEN else f"Saved, but the test failed: {detail or status}.")
            self.events.put(("reddit_result", msg))
            self.events.put(("log", f"Reddit API keys: {msg}"))

        threading.Thread(target=run, daemon=True).start()

    def save_proxy(self):
        text = self.proxy_text().strip()
        valid, invalid = apply_proxy_text(text)
        error = self.write_settings(proxies=text)
        if error:
            self.proxy_status.set(f"Couldn't save the setting: {error}")
            return
        self.proxy_status.set(self.proxy_summary(valid, invalid, saved=True))

    def test_proxy(self):
        text = self.proxy_text()
        valid, invalid = apply_proxy_text(text)
        if not valid:
            self.proxy_status.set(
                "No proxies to test — using your normal connection." if not invalid
                else f"Couldn't read {len(invalid)} line(s). Use IP:PORT:USER:PASS, one per line.")
            return
        self.proxy_status.set(f"Testing {len(valid)} "
                              f"{'proxy' if len(valid) == 1 else 'proxies'}…")

        def run():
            results = test_proxies(valid)
            bad = [(u, info) for u, ok, info in results if not ok]
            good = len(results) - len(bad)
            msg = (f"{good} of {len(valid)} "
                   f"{'proxy' if len(valid) == 1 else 'proxies'} reached the internet")
            if invalid:
                msg += f"; {len(invalid)} line(s) skipped (bad format)"
            if bad:
                u, info = bad[0]
                msg += f". First that failed: {mask_proxy(u)} — {info}"
            else:
                msg += "."
            self.events.put(("log", msg))
            self.events.put(("proxy_result", msg))

        threading.Thread(target=run, daemon=True).start()

    def on_proxy_result(self, msg):
        self.proxy_status.set(msg)

    def on_reddit_result(self, msg):
        self.reddit_status.set(msg)

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
    ap.add_argument("--proxy", default="",
                    help="route checks through your own proxy in IP:PORT:USER:PASS form "
                         "(or IP:PORT, or a full http/https/socks5h URL); separate several "
                         "with commas and checks rotate through them")
    args = ap.parse_args(argv)
    if args.window:
        return start_window()
    if args.proxy:
        valid, invalid = apply_proxy_text(args.proxy)
        if valid:
            n = len(valid)
            say(f"Using {n} {'proxy' if n == 1 else 'proxies'} (e.g. {mask_proxy(valid[0])}).")
        if invalid:
            say(f"Skipped {len(invalid)} proxy entr{'y' if len(invalid) == 1 else 'ies'} "
                f"with an unreadable format.")

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
        say("Note: 'available' means the site itself confirmed the name is free. 'Probably "
            "free' means no account was found, but the site can't confirm it (banned, "
            "deleted or private accounts may still hold the name).")
        return 0
    except KeyboardInterrupt:
        say("Stopped. Run the same command again to continue.")
        return 130


if __name__ == "__main__":
    sys.exit(main())
