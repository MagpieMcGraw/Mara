# Mara for VS Code

Colors for `.mara` files, the language server (`mara lsp`: errors as you
type, hover, go to definition, references, the file's symbols, completion,
rename and its quick fixes), building and debugging a program, and the
`mara view` window.

## Install

    code --install-extension mara-0.2.1.vsix

(Or the Extensions view's … menu → Install from VSIX.) `python pack.py`
makes the .vsix again after the extension changes. The extension runs
the compiler it finds as `mara` on PATH; the setting `mara.path` names
another.

## Debugging

It needs Microsoft's C/C++ extension (`ms-vscode.cpptools`), whose debugger
reads the program's debug info — the PDB every build but `-release` writes
on Windows (cppvsdbg), DWARF elsewhere (cppdbg with gdb). Breakpoints go in
`.mara` files.

F5 in a `.mara` file with no launch.json builds the module in the file's
folder (`mara build`) and debugs the program it made. A launch.json entry:

    {
        "type": "mara",
        "request": "launch",
        "name": "Build and debug",
        "cwd": "${workspaceFolder}",
        "module": "game",          // what `mara build` builds; left out: the one in cwd
        "buildArgs": ["-x86"],     // more for `mara build`
        "args": [],                // the program's command line
        "build": true,             // false: debug "program" as it is
        "program": "game.exe"      // left out: the one the build made
    }

A failed build's errors are in the Mara output panel.

## The window

"Mara: Open View" (the command palette, or a right-click in a .mara file)
opens `mara view` on the file's module, or brings it here. While it's open,
the cursor resting in a .mara file tells it where you are: it moves to that
module, its Docs panel looks up what's there and its Ask panel shows it. A
place clicked in its panels opens here, at its line. `mara.view.followCursor`
turns the following off; `mara.view.delayMs` is how long a rest is.
