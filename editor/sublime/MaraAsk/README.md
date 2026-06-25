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
- **Drill** — the output pane is itself queryable: put the cursor on any name in the
  results and hit the same key. It reuses the module dir of the query that filled the
  pane; a type/function resolves by name, and a variable (in `flow` results) falls
  back to the `file:line` on its row (`at` is variable-only). So you walk the graph in
  place — no tabbing back to your code.
- **Highlight** — a `flow` query also marks its variables right in the code: the
  queried variable in one colour, the variables its flow surfaces (suppliers for
  `above`, modifications + uses for `below`) in another, at their def sites in every
  open file. So `flow above`/`below` is also a visual map, not just a list. Cleared on
  the next query or with **Ctrl+K Ctrl+C**; turn it off with `"highlight_flow": false`.

## Commands & keys

| Command | Default key | What |
|---|---|---|
| `mara_ask` | `Ctrl+K Ctrl+A` | ask about the subject under the cursor (natural kind) |
| `mara_ask_pick` | `Ctrl+K Ctrl+D` | choose a matrix cell (types/call/flow × above/below) |
| `mara_ask_clear_highlights` | `Ctrl+K Ctrl+C` | clear the in-code flow highlight |

All cells are also in the command palette (`Mara Ask: …`). Rebind in
`Default (Windows).sublime-keymap`.

## Settings (`Mara Ask.sublime-settings`)

- `mara_path` — path to the compiler exe (default `C:/Code/Mara/Mara.exe`).
- `default_depth` — `0` uses the tool's default depth; set `1`–`2` to keep large
  subjects from flooding the panel.
- `highlight_flow` — mark a flow result's variables in the code (default `true`).
- `highlight_subject_scope` / `highlight_scope` — region colours for the queried
  variable and the surfaced variables (default `region.bluish` / `region.yellowish`;
  any scope your color scheme defines).

## Install

Copy this `MaraAsk/` folder into your Sublime `Packages/` directory
(`Preferences → Browse Packages…`), then **restart Sublime Text**. The canonical
source lives in the Mara repo at `editor/sublime/MaraAsk/`.

**For development**, junction the package to the repo instead of copying, so edits
are live (no re-copy, no drift). On Windows (no admin needed):

```
rmdir "%APPDATA%\Sublime Text\Packages\MaraAsk"
mklink /J "%APPDATA%\Sublime Text\Packages\MaraAsk" "C:\Code\Mara\editor\sublime\MaraAsk"
```

Then a repo edit is picked up on the next Sublime plugin reload. (Don't later
"sync" by copying into `Packages\` — that would replace the junction with a stale
copy, the exact drift the junction avoids.)

> The bundled **`.python-version`** (`3.8`) is required: it opts the package into
> Sublime Text 4's modern plugin host. Without it ST4 loads the package under the
> legacy Python 3.3 host, where `subprocess.run` / `CREATE_NO_WINDOW` don't exist —
> the commands then appear in the palette but silently die when run (the error only
> shows in the ST console, `View → Show Console`). Keep this file when you copy the
> folder.
