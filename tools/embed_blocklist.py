#!/usr/bin/env python3
"""Regenerate the embedded word list inside app/useratlas.py from app/blocklist.json.

Run this after editing app/blocklist.json:

    python tools/embed_blocklist.py
"""
import base64
import json
import os
import re
import textwrap
import zlib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
data = json.load(open(os.path.join(ROOT, "app", "blocklist.json"), encoding="utf-8"))
payload = {"terms": data["terms"], "safe_words": data["safe_words"]}
raw = json.dumps(payload, separators=(",", ":")).encode()
blob = base64.b64encode(zlib.compress(raw, 9)).decode()
indented = "\n".join('    "' + line + '"' for line in textwrap.wrap(blob, 100))

path = os.path.join(ROOT, "app", "useratlas.py")
src = open(path, encoding="utf-8").read()
src, n = re.subn(r"_BLOCKLIST_BLOB = \(\n.*?\n\)",
                 "_BLOCKLIST_BLOB = (\n%s\n)" % indented, src, count=1, flags=re.S)
assert n == 1, "could not find _BLOCKLIST_BLOB to replace"
open(path, "w", encoding="utf-8").write(src)
print(f"Embedded {len(payload['terms'])} terms and {len(payload['safe_words'])} safe words "
      f"({len(blob)} base64 chars).")
