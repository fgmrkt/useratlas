# UserAtlas

Find out in one go where your usernames are still available: gaming platforms, social networks, developer sites and domain names.

**Download:** [UserAtlasSetup.exe (Windows)](https://github.com/fgmrkt/useratlas/releases/latest/download/UserAtlasSetup.exe) · [UserAtlas-macOS.zip (Mac)](https://github.com/fgmrkt/useratlas/releases/latest/download/UserAtlas-macOS.zip) — no Python needed.

## Installing

**Windows**
1. Download `UserAtlasSetup.exe` and double-click it.
2. First time? Windows may show *"Windows protected your PC"* because the installer isn't digitally signed. Click **More info**, then **Run anyway**.
3. UserAtlas is now in your Start menu (and on your desktop if you like). Remove it via **Settings → Apps**, like any other app.

**macOS**
1. Download `UserAtlas-macOS.zip`, unzip it and move `UserAtlas.app` into your Applications folder.
2. First time: right-click the app and choose **Open** (it isn't signed by Apple), then confirm. After that you can open it normally.

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

Every name is also checked against each site's own naming rules (length, allowed characters, how a name may start or end, reserved words), right as you type it. The **Name rules** card on the Names tab tells you exactly why a site won't allow a name, for example *"Minecraft: too long (at most 16 characters)"* or *"X: can't contain 'twitter' or 'admin'"*. Names that break a site's rules are marked **not allowed** there and aren't sent to that site. When a site itself refuses a name (Roblox, X and Discord say so), its own reason is shown.

**Blocked words.** Names that contain a slur or strong profanity are flagged in red as a **blocked word** and marked not allowed on sites that reject such handles at sign-up (all the gaming and social platforms). Code sites (GitHub, GitLab) and domains don't filter words, so they aren't affected. The check catches look-alike spellings too (for example `n1gga`, `f4g`) and ignores innocent words that merely contain a flagged substring (like *therapist* or *grapefruit*). The word list comes from the MIT-licensed [dsojevic/profanity-list](https://github.com/dsojevic/profanity-list) and is used only to reject offensive usernames — the app never shows which word matched.

### How availability is checked

Where a site offers an official sign-up/validation endpoint — the same one its registration form uses — UserAtlas uses that rather than scraping a profile page, so the answer reflects whether you could actually claim the name at sign-up (Roblox, Discord, X, GitHub, GitLab, Reddit and Bluesky work this way; Minecraft and TikTok need a login and fall back to a profile lookup). The app does **not** create real accounts — that needs email confirmation and a CAPTCHA, and would make junk accounts — so the blocked-word filter above is what catches offensive names the availability endpoints would otherwise report as free.

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
python app/useratlas.py names.txt --rules   # only check each site's name rules (offline)
python app/useratlas.py --list          # all platforms and their name rules
python app/useratlas.py --help          # all options
```
