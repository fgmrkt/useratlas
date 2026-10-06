#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
UserAtlas launcher: this is what's installed on your computer as UserAtlas.exe.

The launcher contains Python itself, but not the app. Every time it starts:
  1. it asks GitHub what the latest version of the app/ folder is;
  2. it downloads only the files that changed, and verifies every file against
     the checksum GitHub provides (git blob sha1);
  3. it test-loads the new version first. If that fails, it keeps the previous
     working version;
  4. it starts the app.
Without internet the most recently downloaded version starts as usual.

So shipping an improvement means: change the code in app/ on GitHub. A new
launcher (new installer) is only needed when app/info.json asks for a higher
"min_launcher", for example because the app needs a new package.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
import traceback
import webbrowser
from datetime import datetime

LAUNCHER_VERSION = 1
REPO = "fgmrkt/useratlas"
BRANCH = "main"
APP_FOLDER = "app"
MAIN_FILE = "useratlas.py"
TIMEOUT = 15
# For testing you can point to another source; by default it's plain GitHub.
API = os.environ.get("USERATLAS_API", "https://api.github.com").rstrip("/")
RAW = os.environ.get("USERATLAS_RAW", "https://raw.githubusercontent.com").rstrip("/")
RELEASES = f"https://github.com/{REPO}/releases/latest"


def _bundled():
    """Everything the app may use. These imports make PyInstaller put them in the
    .exe; --selfcheck calls this to verify they're really in there."""
    import argparse, base64, collections, concurrent.futures, copy, csv, ctypes, dataclasses  # noqa
    import decimal, email.utils, fnmatch, functools, glob, html, http.client, importlib  # noqa
    import itertools, json, logging, math, pathlib, platform, pprint, queue, random, re  # noqa
    import socket, sqlite3, ssl, statistics, string, tempfile, textwrap, typing, unicodedata  # noqa
    import urllib.parse, urllib.request, uuid, webbrowser, zipfile  # noqa
    import tkinter, tkinter.colorchooser, tkinter.filedialog, tkinter.font  # noqa
    import tkinter.messagebox, tkinter.simpledialog, tkinter.ttk  # noqa
    import requests  # noqa


# ---------------------------------------------------------------------------
# Folders
# ---------------------------------------------------------------------------

def base_dir() -> str:
    if os.name == "nt":
        base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
        return os.path.join(base, "UserAtlas")
    return os.path.join(os.path.expanduser("~"), ".local", "share", "useratlas")


def app_dir() -> str:
    return os.path.join(base_dir(), "app")


def write_log(line: str):
    try:
        os.makedirs(base_dir(), exist_ok=True)
        path = os.path.join(base_dir(), "launcher.log")
        if os.path.exists(path) and os.path.getsize(path) > 200_000:
            os.replace(path, path + ".1")
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"{datetime.now():%Y-%m-%d %H:%M:%S}  {line}\n")
    except OSError:
        pass


# ---------------------------------------------------------------------------
# GitHub
# ---------------------------------------------------------------------------

class NoConnection(Exception):
    pass


def git_blob_sha(content: bytes) -> str:
    """The same checksum git (and GitHub) uses for a file."""
    return hashlib.sha1(b"blob %d\0" % len(content) + content).hexdigest()


def _session():
    import requests
    s = requests.Session()
    s.headers.update({"User-Agent": f"UserAtlas-launcher/{LAUNCHER_VERSION}",
                      "Accept": "application/vnd.github+json"})
    return s


def _api(s, path: str):
    try:
        r = s.get(f"{API}{path}", timeout=TIMEOUT)
    except Exception as e:
        raise NoConnection(f"no connection to GitHub ({type(e).__name__})")
    if r.status_code in (403, 429):
        raise NoConnection("GitHub asks to wait a moment (too many requests)")
    if r.status_code != 200:
        raise NoConnection(f"GitHub answered {r.status_code}")
    return r.json()


def latest_commit(s) -> str:
    return _api(s, f"/repos/{REPO}/commits/{BRANCH}")["sha"]


def files_on_github(s, commit: str) -> dict:
    """{relative path: blob sha} of everything in app/ at this commit."""
    d = _api(s, f"/repos/{REPO}/git/trees/{commit}?recursive=1")
    prefix = APP_FOLDER + "/"
    out = {}
    for item in d.get("tree", []):
        path = item.get("path", "")
        if item.get("type") == "blob" and path.startswith(prefix):
            rel = path[len(prefix):]
            if rel and ".." not in rel.split("/") and not rel.startswith("/"):
                out[rel] = item["sha"]
    if MAIN_FILE not in out:
        raise NoConnection(f"{APP_FOLDER}/{MAIN_FILE} not found on GitHub")
    return out


def download(s, commit: str, rel: str, expected: str) -> bytes:
    try:
        r = s.get(f"{RAW}/{REPO}/{commit}/{APP_FOLDER}/{rel}", timeout=TIMEOUT)
    except Exception as e:
        raise NoConnection(f"download failed ({type(e).__name__})")
    if r.status_code != 200:
        raise NoConnection(f"download of {rel} returned {r.status_code}")
    if git_blob_sha(r.content) != expected:
        raise NoConnection(f"{rel} doesn't match GitHub's checksum")
    return r.content


# ---------------------------------------------------------------------------
# Local copy
# ---------------------------------------------------------------------------

def read_source(folder: str) -> dict:
    try:
        with open(os.path.join(folder, ".source.json"), encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def read_info(folder: str) -> dict:
    try:
        with open(os.path.join(folder, "info.json"), encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def test_load(folder: str):
    """Loads the app under a temporary name; raises if the code is broken."""
    name = f"_useratlas_trial_{int(time.time() * 1000)}"
    spec = importlib.util.spec_from_file_location(name, os.path.join(folder, MAIN_FILE))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod  # needed by e.g. dataclasses
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.modules.pop(name, None)
    if not callable(getattr(mod, "main", None)):
        raise RuntimeError("the app has no main()")


def clean_leftovers(base: str):
    for name in os.listdir(base) if os.path.isdir(base) else []:
        if name.startswith("new-"):
            shutil.rmtree(os.path.join(base, name), ignore_errors=True)


def update(report=lambda text: None) -> dict:
    """Makes sure app/current contains the latest working version.
    Returns {"folder", "commit", "source", "message"}."""
    base = app_dir()
    current = os.path.join(base, "current")
    previous = os.path.join(base, "previous")
    os.makedirs(base, exist_ok=True)
    clean_leftovers(base)
    old = read_source(current)

    try:
        report("Asking GitHub for the latest version…")
        s = _session()
        commit = latest_commit(s)
        if old.get("commit") == commit and os.path.exists(os.path.join(current, MAIN_FILE)):
            return {"folder": current, "commit": commit, "source": "github", "message": ""}
        files = files_on_github(s, commit)
    except NoConnection as e:
        write_log(f"Not updated: {e}")
        if os.path.exists(os.path.join(current, MAIN_FILE)):
            return {"folder": current, "commit": old.get("commit", ""), "source": "copy",
                    "message": f"Started with the most recently downloaded version ({e})."}
        raise

    new = os.path.join(base, f"new-{os.getpid()}")
    shutil.rmtree(new, ignore_errors=True)
    try:
        old_files = old.get("files", {})
        to_fetch = [rel for rel, sha in files.items()
                    if old_files.get(rel) != sha
                    or not os.path.exists(os.path.join(current, rel))]
        for rel in sorted(files):
            target = os.path.join(new, *rel.split("/"))
            os.makedirs(os.path.dirname(target), exist_ok=True)
            if rel in to_fetch:
                report(f"Downloading ({to_fetch.index(rel) + 1}/{len(to_fetch)}): {rel}")
                content = download(s, commit, rel, files[rel])
            else:
                with open(os.path.join(current, *rel.split("/")), "rb") as f:
                    content = f.read()
            with open(target, "wb") as f:
                f.write(content)
        with open(os.path.join(new, ".source.json"), "w", encoding="utf-8") as f:
            json.dump({"commit": commit, "files": files,
                       "fetched": datetime.now().isoformat(timespec="seconds")}, f, indent=1)

        report("Checking the new version…")
        test_load(new)
    except Exception as e:
        shutil.rmtree(new, ignore_errors=True)
        reason = str(e) if isinstance(e, NoConnection) else f"{type(e).__name__}: {e}"
        write_log(f"New version {commit[:7]} not used: {reason}")
        if os.path.exists(os.path.join(current, MAIN_FILE)):
            return {"folder": current, "commit": old.get("commit", ""), "source": "copy",
                    "message": f"The newest version couldn't be used ({reason}); "
                               f"started the previous version."}
        raise NoConnection(reason)

    # Swap: current -> previous, new -> current
    try:
        shutil.rmtree(previous, ignore_errors=True)
        if os.path.exists(current):
            os.replace(current, previous)
        os.replace(new, current)
        folder = current
    except OSError as e:  # e.g. a second window has the folder open; try again next time
        write_log(f"Swapping failed ({e}); starting from {new}")
        folder = new
    write_log(f"Updated to {commit[:7]} ({len(to_fetch)} file(s) downloaded)")
    return {"folder": folder, "commit": commit, "source": "github", "message": ""}


# ---------------------------------------------------------------------------
# Splash screen and starting
# ---------------------------------------------------------------------------

def restart():
    """Starts the launcher again (which then fetches the latest version)."""
    env = {k: v for k, v in os.environ.items() if not k.startswith(("_PYI", "_MEIPASS"))}
    env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"
    if getattr(sys, "frozen", False):
        command = [sys.executable]
    else:
        command = [sys.executable, os.path.abspath(__file__)]
    subprocess.Popen(command, env=env, close_fds=True)


def newer_available(current_commit: str):
    """For the app: is there anything on GitHub newer than what's running now?"""
    def check():
        latest = latest_commit(_session())
        return latest if latest != current_commit else None
    return check


def splash(work):
    """Shows a small dark window while `work()` runs in the background."""
    import tkinter as tk
    from tkinter import font as tkfont
    from tkinter import ttk

    outcome = {}
    root = tk.Tk()
    family = tkfont.nametofont("TkDefaultFont").actual()["family"]
    root.overrideredirect(True)
    root.configure(background="#101016")
    w, h = 440, 200
    root.geometry(f"{w}x{h}+{(root.winfo_screenwidth() - w) // 2}"
                  f"+{(root.winfo_screenheight() - h) // 3}")
    frame = tk.Frame(root, bg="#101016", highlightthickness=1, highlightbackground="#2A2140")
    frame.pack(fill="both", expand=True)
    tk.Label(frame, text="@", bg="#8B5CF6", fg="#FFFFFF", font=(family, 18, "bold"),
             width=2).pack(pady=(28, 8))
    tk.Label(frame, text="UserAtlas", bg="#101016", fg="#ECECF3",
             font=(family, 14, "bold")).pack()
    status = tk.StringVar(value="Starting…")
    tk.Label(frame, textvariable=status, bg="#101016", fg="#9A9AB2",
             font=(family, 10)).pack(pady=(4, 12))
    style = ttk.Style(root)
    try:
        style.theme_use("clam")
    except tk.TclError:
        pass
    style.configure("Splash.Horizontal.TProgressbar", troughcolor="#1C1C26", background="#8B5CF6",
                    bordercolor="#1C1C26", lightcolor="#8B5CF6", darkcolor="#8B5CF6", thickness=5)
    bar = ttk.Progressbar(frame, mode="indeterminate", length=300,
                          style="Splash.Horizontal.TProgressbar")
    bar.pack()
    bar.start(12)

    messages: "queue.Queue[str]" = queue.Queue()
    finished = threading.Event()

    def background():
        try:
            outcome["ok"] = work(messages.put)
        except BaseException as e:
            outcome["error"] = e
        finished.set()

    def poll():  # only the window thread touches Tk
        try:
            while True:
                status.set(messages.get_nowait())
        except queue.Empty:
            pass
        if finished.is_set():
            root.quit()
        else:
            root.after(80, poll)

    threading.Thread(target=background, daemon=True).start()
    root.after(80, poll)
    root.mainloop()
    bar.stop()  # otherwise the animation keeps running after closing
    root.update_idletasks()
    root.destroy()
    if "error" in outcome:
        raise outcome["error"]
    return outcome.get("ok")


def notice(title: str, text: str, kind: str = "info", retry: bool = False):
    import tkinter as tk
    from tkinter import messagebox
    root = tk.Tk()
    root.withdraw()
    try:
        if retry:
            return messagebox.askretrycancel(title, text, parent=root)
        if kind == "yesno":
            return messagebox.askyesno(title, text, parent=root)
        getattr(messagebox, "showerror" if kind == "error" else "showinfo")(title, text, parent=root)
    finally:
        root.destroy()


def start_app(info: dict) -> int:
    folder = info["folder"]
    needs = read_info(folder)
    if int(needs.get("min_launcher", 1)) > LAUNCHER_VERSION:
        if notice("UserAtlas", "This version of UserAtlas needs a newer installation. "
                               "Open the download page?", kind="yesno"):
            webbrowser.open(RELEASES)
        return 1
    spec = importlib.util.spec_from_file_location("useratlas", os.path.join(folder, MAIN_FILE))
    mod = importlib.util.module_from_spec(spec)
    sys.modules["useratlas"] = mod
    spec.loader.exec_module(mod)
    mod.LAUNCHER = {
        "version": LAUNCHER_VERSION,
        "commit": info.get("commit", ""),
        "source": info.get("source", ""),
        "message": info.get("message", ""),
        "newer": newer_available(info.get("commit", "")),
        "restart": restart,
        "releases": RELEASES,
    }
    return mod.main([]) or 0


def main() -> int:
    if sys.argv[1:] == ["--selfcheck"]:
        try:
            _bundled()
            return 0
        except Exception:
            return 1
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass

    while True:
        try:
            info = splash(update)
            break
        except NoConnection as e:
            if not notice("UserAtlas", f"UserAtlas couldn't fetch the app from GitHub.\n\n{e}\n\n"
                                       "Check your internet connection and try again.",
                          retry=True):
                return 1
    try:
        return start_app(info)
    except Exception:
        error = traceback.format_exc()
        write_log("The app crashed:\n" + error)
        notice("UserAtlas", "Something went wrong in UserAtlas.\n\n"
                            f"{error.strip().splitlines()[-1]}\n\n"
                            f"Details are in {os.path.join(base_dir(), 'launcher.log')}",
               kind="error")
        return 1


if __name__ == "__main__":
    sys.exit(main())
