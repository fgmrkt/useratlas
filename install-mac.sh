#!/bin/bash
# Installs (or updates) UserAtlas.app from the latest GitHub release.
#
#   curl -fsSL https://raw.githubusercontent.com/fgmrkt/useratlas/main/install-mac.sh | bash
#
# Downloading with Terminal instead of a browser means macOS doesn't put the
# "downloaded from the internet" mark on the app, so it opens without the
# "Apple cannot check it for malicious software" block. The app isn't
# notarized by Apple; this is the usual way to install such open-source apps.
set -euo pipefail

URL="https://github.com/fgmrkt/useratlas/releases/latest/download/UserAtlas-macOS.zip"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "Downloading UserAtlas…"
curl -fsSL "$URL" -o "$TMP/UserAtlas-macOS.zip"
ditto -x -k "$TMP/UserAtlas-macOS.zip" "$TMP"

DEST="/Applications"
if [ ! -w "$DEST" ]; then
  DEST="$HOME/Applications"
  mkdir -p "$DEST"
fi

rm -rf "$DEST/UserAtlas.app"
ditto "$TMP/UserAtlas.app" "$DEST/UserAtlas.app"
xattr -dr com.apple.quarantine "$DEST/UserAtlas.app" 2>/dev/null || true

echo "Installed: $DEST/UserAtlas.app"
if [ -z "${USERATLAS_NO_OPEN:-}" ]; then
  open "$DEST/UserAtlas.app"
fi
