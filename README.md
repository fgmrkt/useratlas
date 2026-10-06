# UserAtlas

Find out in one go where your usernames are still available: gaming platforms, social networks, developer sites and domain names.

**[⬇ Download UserAtlasSetup.exe](https://github.com/fgmrkt/useratlas/releases/latest/download/UserAtlasSetup.exe)** (Windows, no Python needed)

## Installing

1. Download `UserAtlasSetup.exe` and double-click it.
2. First time? Windows may show *"Windows protected your PC"* because the installer isn't digitally signed. Click **More info**, then **Run anyway**.
3. UserAtlas is now in your Start menu (and on your desktop if you like). Remove it via **Settings → Apps**, like any other app.

## How the app keeps itself up to date

UserAtlas.exe is a small launcher with Python built in. The actual app lives in the [`app/`](app/) folder of this repository. Every time it starts, the launcher:

1. asks GitHub what the latest version of `app/` is;
2. downloads only the files that changed, and verifies each one against GitHub's checksum;
3. test-loads the new version first. If it doesn't work, the previous working version starts instead;
4. starts the app.

Without internet, the most recently downloaded version starts. If a new version appears while you're using the app, it shows **Restart** at the top.

## What it checks

| Group | Platforms |
|---|---|
| Gaming | Minecraft, Roblox, Steam, Discord, Chess.com, Lichess |
| Socials | Instagram, TikTok, X, YouTube, Snapchat, Telegram, Bluesky |
| Other | GitHub, GitLab, Reddit, Twitch, SoundCloud |
| Domains | .com, .net, .org, .nl, .eu, .io, .gg, .lol and any extension you add |

The app first runs a self-test per platform: a known name must be taken and a random name must be available. Platforms that get this wrong are skipped, so you never get a false "available". Results are saved in `%APPDATA%\UserAtlas`, so you can stop and continue later.

"Available" means no account or registration was found. Some names are still blocked or reserved; you'll only find out when claiming.

## For the maintainer

| What you want | What you do |
|---|---|
| Improve the app | Change `app/useratlas.py` and push to `main`. Everyone gets it on their next start. Bump `version` in `app/info.json` when you want the version number in the app to change. |
| A new installer | Only needed when `launcher/launcher.py` changes. Go to **Actions → Build → Run workflow** and enter a version number, e.g. `1.1.0`. |
| The app needs a new Python package | Add the package to the build step and to `_bundled()` in the launcher, raise `LAUNCHER_VERSION`, set `min_launcher` in `app/info.json` to the same number, and release a new installer. Older launchers will then ask to update. |

Every push is checked: the app must load, and on Windows the installer is built, test-installed and removed again. That test installer is under **Actions** → the run → *Artifacts*.

Note: anything you push to `main` in `app/` goes straight to all users. A broken version is caught (the previous one starts instead), but test big changes first with `python app/useratlas.py`.

## Running it yourself with Python

```
pip install requests
python app/useratlas.py                 # window
python app/useratlas.py names.txt       # terminal
python app/useratlas.py --help          # all options
```
