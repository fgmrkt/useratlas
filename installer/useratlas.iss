; Installer for UserAtlas (Inno Setup 6).
; Built on GitHub by .github/workflows/build.yml:
;   iscc /DAppVersion=1.2.0 installer\useratlas.iss
; Installs for the current user only, so no administrator rights are needed.

#ifndef AppVersion
  #define AppVersion "0.0.0"
#endif

[Setup]
AppId={{E0C560FB-3F40-46AD-93AF-E70CB40FAE86}
AppName=UserAtlas
AppVersion={#AppVersion}
AppVerName=UserAtlas
AppPublisher=fgmrkt
AppPublisherURL=https://github.com/fgmrkt/useratlas
AppSupportURL=https://github.com/fgmrkt/useratlas/issues
AppUpdatesURL=https://github.com/fgmrkt/useratlas/releases
DefaultDirName={localappdata}\Programs\UserAtlas
DefaultGroupName=UserAtlas
DisableProgramGroupPage=yes
DisableDirPage=yes
DisableReadyPage=yes
PrivilegesRequired=lowest
OutputDir=..\dist
OutputBaseFilename=UserAtlasSetup
SetupIconFile=..\app\useratlas.ico
UninstallDisplayIcon={app}\UserAtlas.exe
UninstallDisplayName=UserAtlas
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
CloseApplications=yes
RestartApplications=no

[Languages]
Name: "english"; MessagesFile: "compiler:Default.isl"

[Tasks]
Name: "desktopicon"; Description: "Create a desktop shortcut"; GroupDescription: "Extra:"

[Files]
Source: "..\dist\UserAtlas.exe"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{autoprograms}\UserAtlas"; Filename: "{app}\UserAtlas.exe"
Name: "{autodesktop}\UserAtlas"; Filename: "{app}\UserAtlas.exe"; Tasks: desktopicon

[Run]
Filename: "{app}\UserAtlas.exe"; Description: "Start UserAtlas now"; Flags: nowait postinstall skipifsilent

[UninstallDelete]
; The app files fetched from GitHub; your own results (in %APPDATA%\UserAtlas) are kept.
Type: filesandordirs; Name: "{localappdata}\UserAtlas\app"
Type: files; Name: "{localappdata}\UserAtlas\launcher.log"
Type: files; Name: "{localappdata}\UserAtlas\launcher.log.1"
Type: dirifempty; Name: "{localappdata}\UserAtlas"
