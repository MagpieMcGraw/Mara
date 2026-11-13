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

- **The window** — with `mara view` open, each query also shows in the window's
  **Ask** panel (`mara ask -show`). And when the **cursor rests** in a `.mara`
  file, the window is told where it is, for reading after an alt-tab. It follows
  you: it moves to that file's module, and its title says which one. Reading in
  the stdlib or doc/ doesn't move it.
  - its **Docs** panel looks it up: what the name at the cursor (an
    operator: the function it calls) refers to first — the compiler's answer, a local's or a param's too
    — then the text matches in the file's directory, the stdlib and doc/, with
    doc comments and signatures;
  - its **Ask** panel shows
    what's at the cursor at its top: for a variable or a field, the types along
    its path, where it's declared, and every place it's written and read in the
    module and the modules it uses, each opening in the editor when clicked. A
    field used through a value lists that value's uses, followed through locals
    and params, with any it can't be sure of under `maybe`; at the field's
    declaration, every value's. For anything else named, what it is, its type and
    where it's declared; an operator, the function it calls.

  The plugin sends one byte, the cursor's place in the saved file (`mara ask
  -cursor cursor at <file>@<byte>`; a **highlight** on one line, two), and the
  compiler says what's there. Of the two tokens a cursor can touch, a name
  wins; just past `]` or a call's `)`, what they close; in a call's `(` or `,`,
  the fun called; between tokens, the nearest on the line; on a blank line or
  in a comment, nothing, and what the window shows stays. A highlight is the
  smallest expression holding it. Ask answers from the saved file: it finds the
  line you're on there, so the line numbers it lists are the saved file's, and a
  line that isn't saved yet it says so. Saving asks again at the cursor.

  The window is also told where this Sublime is (`mara editor`, once it's
  open): a call in its **Crash** panel — the program's last crash, the calls
  that were running — opens here at its line, clicked. And its colors
  (`mara colors`, again when they change): the window's **Theme → Sublime**
  colors its panels with your color scheme, and code as Sublime does.

## Commands & keys

| Command | Default key | What |
|---|---|---|
| `mara_ask` | `Ctrl+K Ctrl+A` | ask about the subject under the cursor (natural kind) |
| `mara_ask_pick` | `Ctrl+K Ctrl+D` | choose a matrix cell (types/call/flow × above/below) |
| `mara_ask_clear_highlights` | `Ctrl+K Ctrl+C` | clear the in-code flow highlight |
| `mara_view` | right-click → Open mara view | the window (`mara view`) on the file's module — brought to the front and moved here when it's open already — with what was right-clicked looked up there (its Docs, and Ask's what's-at-the-cursor), as a rest on it would |

All cells are also in the command palette (`Mara Ask: …`; the window: `Mara:
open mara view`). Rebind in `Default (Windows).sublime-keymap`.

The window's item is in the right-click menu itself, not LSP's submenu:
LSP's has no `"id"`, and Sublime only merges menu items by id — another
"LSP" entry would be a second submenu.

## Settings (`Mara Ask.sublime-settings`)

- `mara_path` — path to the compiler exe (default `C:/Code/Mara/Mara.exe`).
- `default_depth` — `0` uses the tool's default depth; set `1`–`2` to keep large
  subjects from flooding the panel.
- `highlight_flow` — mark a flow result's variables in the code (default `true`).
- `highlight_subject_scope` / `highlight_scope` — region colours for the queried
  variable and the surfaced variables (default `region.bluish` / `region.yellowish`;
  any scope your color scheme defines).
- `show_in_window` — show queries in a `mara view` window's Ask panel (default `true`).
- `delay_ms` — how long the cursor rests before a window is told (default `300`).
- `docs_at_cursor` — look what's at the cursor up in the window's Docs panel
  (default `true`).
- `what_at_cursor` — show what's at the cursor at the top of the window's Ask
  panel (default `true`). Which token the cursor means is the compiler's call:
  the plugin sends a byte (`mara ask -cursor cursor at <file>@<byte>`).
- `tell_colors` — tell the windows your color scheme's colors, for their Sublime
  theme (default `true`).

## The language server (`mara lsp`)

Besides this plugin, the compiler is a language server: `mara lsp` speaks the
Language Server Protocol, so Sublime's **LSP** package (or any editor's client)
gets Goto Definition, Find References, Goto Symbol, completion, Rename, hover
and errors from it. When you rename a declaration by hand, a code action (the
lightbulb, or `LSP: Code Action`) offers to rename its uses too, or to put the
name back — offered, never asked.
Each file is checked with its module as the editor has it — saved or not, and
half-written: what parses is checked. In
`Preferences → Package Settings → LSP → Settings`, under `"clients"`:

```
"mara": {
    "command": ["C:/Code/Mara/Mara.exe", "lsp"],
    "enabled": true,
    "selector": "source.mara",
    "initializationOptions": {
        "hover": false,        // a popup: what's under the mouse, its doc comment
        "diagnostics": false,  // errors and warnings: squiggles, the diagnostics panel
        "definition": true,    // Goto Definition
        "references": true,    // Find References
        "symbols": true,       // Goto Symbol: the file's definitions
        "completion": true,    // the names that fit where you type, after `x.` too
        "renames": true,       // Rename; a declaration renamed by hand: its uses offered too
    }
}
```

Each option turns a feature off on the server's side: it isn't offered, so
nothing shows. After a change, `LSP: Restart Servers`. (The LSP package's own
`disabled_capabilities` per client does the same from the client's side, and
its settings style what's shown — `diagnostics_highlight_style` and the like —
for every language.) While Sublime runs `mara lsp`, Mara.exe is in use: to
rebuild the compiler, restart the servers after, or rename the running exe
aside first.

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
