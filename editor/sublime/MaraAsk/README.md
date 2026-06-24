# Mara Ask — Sublime Text plugin

A keystroke front-end for `mara ask`. Put the cursor on a name and ask; the answer
appears in an output panel with every `file:line` clickable.

## How it works

- **Subject** comes from the editor: the word under the cursor (a type / function),
  or — when that isn't a top-level name — the variable declared on the cursor's line,
  via `mara ask at <file>:<line>`. The `mara_ask` command tries the name first and
  falls back to `at` automatically.
- **Kind** defaults to the subject's natural one (the tool's own rule): a struct →
  `types`, a function → `call`, a variable → `flow`. Pass an explicit kind/direction
  to override.
- **cwd** is the current file's directory, so the analyzer roots on that module.
- **Output** goes to a reused scratch view (`✦ Mara Ask`) parked in a **right-hand
  split column** — a full-height editor pane you can resize (drag the divider),
  fold, and search. It's cleared on each query (entries never run together) with
  the command echoed on the first line, and sets `result_file_regex` so **F4 / click
  jumps to any printed location**. Focus returns to your code after each query, so
  the next keystroke still reads the word under your cursor. The split is only
  auto-created when the window is a single pane (it won't disturb a layout you set
  up); width is the `split_ratio` setting.

## Commands & keys

| Command | Default key | What |
|---|---|---|
| `mara_ask` | `Ctrl+K Ctrl+A` | ask about the subject under the cursor (natural kind) |
| `mara_ask_pick` | `Ctrl+K Ctrl+D` | choose a matrix cell (types/call/flow × above/below) |

All cells are also in the command palette (`Mara Ask: …`). Rebind in
`Default (Windows).sublime-keymap`.

## Settings (`Mara Ask.sublime-settings`)

- `mara_path` — path to the compiler exe (default `C:/Code/Mara/Mara.exe`).
- `default_depth` — `0` uses the tool's default depth; set `1`–`2` to keep large
  subjects from flooding the panel.

## Install

Copy this `MaraAsk/` folder into your Sublime `Packages/` directory
(`Preferences → Browse Packages…`), then **restart Sublime Text**. The canonical
source lives in the Mara repo at `editor/sublime/MaraAsk/`.

> The bundled **`.python-version`** (`3.8`) is required: it opts the package into
> Sublime Text 4's modern plugin host. Without it ST4 loads the package under the
> legacy Python 3.3 host, where `subprocess.run` / `CREATE_NO_WINDOW` don't exist —
> the commands then appear in the palette but silently die when run (the error only
> shows in the ST console, `View → Show Console`). Keep this file when you copy the
> folder.
