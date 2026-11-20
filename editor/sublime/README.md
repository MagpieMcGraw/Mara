# Mara for Sublime Text

Two packages, each a folder here:

- `Mara/` — the language: colors for `.mara` files (Mara.sublime-syntax),
  `//` for Toggle Comment, an indent after a line ending in `{`, and
  `wrap_width` 80 for .mara files (Alt+Q rewraps a comment paragraph at it).
- `MaraAsk/` — `mara ask` from a key, and the `mara view` window following
  the cursor. Its README says how it works.

## Install

Copy both folders into Sublime's `Packages/` folder
(`Preferences → Browse Packages…`) and restart Sublime Text. On Windows:

```
xcopy /E /I /Y "C:\Code\Mara\editor\sublime\Mara" "%APPDATA%\Sublime Text\Packages\Mara"
xcopy /E /I /Y "C:\Code\Mara\editor\sublime\MaraAsk" "%APPDATA%\Sublime Text\Packages\MaraAsk"
```

The folders here are the packages' source: change them here, then copy
again, as anyone using the language would.

## The language server

Errors as you type, Goto Definition, references, symbols, completion and
renames come from `mara lsp`, through the LSP package (Package Control →
Install Package → LSP). Add a client in `Preferences → Package Settings →
LSP → Settings`:

```
{
	"clients": {
		"mara": {
			"command": ["mara", "lsp"],
			"enabled": true,
			"selector": "source.mara",
			"initializationOptions": {
				"hover": false,        // a popup: what's under the mouse, its doc comment
				"diagnostics": true,   // errors and warnings: squiggles, the diagnostics panel
				"definition": true,    // Goto Definition (F12)
				"references": true,    // Find References (shift+F12)
				"symbols": true,       // Goto Symbol (ctrl+R): the file's definitions
				"completion": true,    // the names that fit where you type, after `x.` too; a fun's call with its params to fill in (Tab to the next)
				"renames": true        // Rename (F2); a declaration renamed by hand offers its uses
			}
		}
	}
}
```

`mara` is the compiler on PATH; give its full path otherwise. After changing
an option, run `LSP: Restart Servers` from the command palette.
