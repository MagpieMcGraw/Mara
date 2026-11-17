// Mara in VS Code: the language server (`mara lsp`) spoken to directly — no
// npm packages — `mara build` before debugging with the C/C++ extension's
// debugger, which reads the program's PDB (DWARF off Windows), and the
// `mara view` window following the cursor.
const vscode = require("vscode");
const cp = require("child_process");
const fs = require("fs");
const path = require("path");

let out;          // the "Mara" output panel
let server;       // the language server, while it runs
let diagnostics;  // its errors and warnings, by file
let listening;    // the editor's side registered (once: it talks to whichever server runs)

function activate(context) {
    out = vscode.window.createOutputChannel("Mara");
    diagnostics = vscode.languages.createDiagnosticCollection("mara");
    context.subscriptions.push(out, diagnostics);
    startServer(context);
    context.subscriptions.push(
        vscode.commands.registerCommand("mara.restartServer", () => { stopServer(); startServer(context); }),
        vscode.debug.registerDebugConfigurationProvider("mara", debugProvider),
        { dispose: stopServer });
    registerView(context);
}

function deactivate() { return stopServer(); }

function maraPath() { return vscode.workspace.getConfiguration("mara").get("path") || "mara"; }

function workspaceDir() {
    const folder = vscode.workspace.workspaceFolders && vscode.workspace.workspaceFolders[0];
    return folder ? folder.uri.fsPath : undefined;
}

// --- the language server ------------------------------------------------------

// `mara lsp` on stdin and stdout: messages framed by a Content-Length header,
// each a JSON-RPC request, response or notification.
class Server {
    constructor(proc) {
        this.proc = proc;
        this.next = 1;
        this.waiting = new Map();   // request id: its promise's resolve and reject
        this.buffer = Buffer.alloc(0);
        proc.stdout.on("data", (chunk) => this.read(chunk));
        proc.stderr.on("data", (chunk) => out.append(chunk.toString()));
    }
    send(message) {
        const body = Buffer.from(JSON.stringify({ jsonrpc: "2.0", ...message }), "utf8");
        this.proc.stdin.write(`Content-Length: ${body.length}\r\n\r\n`);
        this.proc.stdin.write(body);
    }
    request(method, params) {
        const id = this.next++;
        return new Promise((resolve, reject) => {
            this.waiting.set(id, { resolve, reject });
            this.send({ id, method, params });
        });
    }
    notify(method, params) { this.send({ method, params }); }
    read(chunk) {
        this.buffer = Buffer.concat([this.buffer, chunk]);
        for (;;) {
            const end = this.buffer.indexOf("\r\n\r\n");
            if (end < 0) return;
            const length = /Content-Length:\s*(\d+)/i.exec(this.buffer.subarray(0, end).toString());
            if (!length) { this.buffer = this.buffer.subarray(end + 4); continue; }
            const start = end + 4, n = Number(length[1]);
            if (this.buffer.length < start + n) return;
            const message = JSON.parse(this.buffer.subarray(start, start + n).toString("utf8"));
            this.buffer = this.buffer.subarray(start + n);
            this.handle(message);
        }
    }
    handle(message) {
        if (message.id !== undefined && message.method === undefined) {   // a response
            const w = this.waiting.get(message.id);
            if (!w) return;
            this.waiting.delete(message.id);
            if (message.error) w.reject(new Error(message.error.message)); else w.resolve(message.result);
        } else if (message.method === "textDocument/publishDiagnostics") {
            const p = message.params;
            diagnostics.set(vscode.Uri.parse(p.uri), p.diagnostics.map(toDiagnostic));
        } else if (message.method === "window/logMessage" || message.method === "window/showMessage") {
            out.appendLine(message.params.message);
        } else if (message.id !== undefined) {   // a request of the server's: none is known
            this.send({ id: message.id, error: { code: -32601, message: `no ${message.method}` } });
        }
    }
}

async function startServer(context) {
    const proc = cp.spawn(maraPath(), ["lsp"], { cwd: workspaceDir() });
    const s = new Server(proc);
    server = s;
    proc.on("error", (e) => {
        if (server === s) server = undefined;
        vscode.window.showErrorMessage(`Mara: couldn't start \`${maraPath()} lsp\` (${e.message}). Set mara.path to the compiler.`);
    });
    proc.on("exit", (code) => {
        if (server !== s) return;
        server = undefined;
        for (const w of s.waiting.values()) w.reject(new Error("mara lsp stopped"));
        out.appendLine(`mara lsp stopped (${code}): Mara: Restart the Language Server starts it again.`);
    });
    try {
        await s.request("initialize", {
            processId: process.pid,
            rootUri: workspaceDir() ? vscode.Uri.file(workspaceDir()).toString() : null,
            capabilities: { general: { positionEncodings: ["utf-16"] } },
        });
    } catch (e) {
        out.appendLine(`mara lsp: ${e.message}`);
        return;
    }
    s.notify("initialized", {});
    for (const doc of vscode.workspace.textDocuments) opened(doc);
    if (listening) return;
    listening = true;
    const mara = { language: "mara" };
    context.subscriptions.push(
        vscode.workspace.onDidOpenTextDocument(opened),
        vscode.workspace.onDidChangeTextDocument((e) => {
            if (e.document.languageId !== "mara" || !server) return;
            server.notify("textDocument/didChange", {
                textDocument: { uri: e.document.uri.toString(), version: e.document.version },
                contentChanges: [{ text: e.document.getText() }],
            });
        }),
        vscode.workspace.onDidSaveTextDocument((doc) => {
            if (doc.languageId === "mara" && server) server.notify("textDocument/didSave", { textDocument: { uri: doc.uri.toString() } });
        }),
        vscode.workspace.onDidCloseTextDocument((doc) => {
            if (doc.languageId === "mara" && server) server.notify("textDocument/didClose", { textDocument: { uri: doc.uri.toString() } });
        }),
        vscode.languages.registerHoverProvider(mara, { provideHover: (doc, pos) => ask("textDocument/hover", doc, pos, toHover) }),
        vscode.languages.registerDefinitionProvider(mara, { provideDefinition: (doc, pos) => ask("textDocument/definition", doc, pos, toLocations) }),
        vscode.languages.registerReferenceProvider(mara, {
            provideReferences: (doc, pos, ctx) => ask("textDocument/references", doc, pos, toLocations, { context: { includeDeclaration: ctx.includeDeclaration } }),
        }),
        vscode.languages.registerDocumentSymbolProvider(mara, {
            provideDocumentSymbols: (doc) => request("textDocument/documentSymbol", { textDocument: { uri: doc.uri.toString() } }, toSymbols),
        }),
        vscode.languages.registerCompletionItemProvider(mara, { provideCompletionItems: (doc, pos) => ask("textDocument/completion", doc, pos, toCompletions) }, "."),
        vscode.languages.registerRenameProvider(mara, {
            provideRenameEdits: (doc, pos, newName) => ask("textDocument/rename", doc, pos, toWorkspaceEdit, { newName }, true),
        }),
        vscode.languages.registerCodeActionsProvider(mara, {
            provideCodeActions: (doc, range, ctx) => request("textDocument/codeAction", {
                textDocument: { uri: doc.uri.toString() },
                range: fromRange(range),
                context: { diagnostics: ctx.diagnostics.map(fromDiagnostic) },
            }, toCodeActions),
        }));
}

function stopServer() {
    const s = server;
    server = undefined;
    if (!s) return;
    diagnostics.clear();
    return s.request("shutdown", null).catch(() => {}).then(() => { s.notify("exit", null); setTimeout(() => s.proc.kill(), 500); });
}

function opened(doc) {
    if (doc.languageId !== "mara" || !server) return;
    server.notify("textDocument/didOpen", {
        textDocument: { uri: doc.uri.toString(), languageId: "mara", version: doc.version, text: doc.getText() },
    });
}

// A request about a point in a file; its answer made VS Code's by `convert`
// (nothing: none). A rename's refusal is shown; another failure is logged.
function ask(method, doc, pos, convert, more = {}, rethrow = false) {
    return request(method, { textDocument: { uri: doc.uri.toString() }, position: fromPosition(pos), ...more }, convert, rethrow);
}

async function request(method, params, convert, rethrow = false) {
    if (!server) return undefined;
    try {
        const result = await server.request(method, params);
        return result == null ? undefined : convert(result);
    } catch (e) {
        if (rethrow) throw e;
        out.appendLine(`${method}: ${e.message}`);
        return undefined;
    }
}

// --- LSP's shapes and VS Code's ------------------------------------------------

const fromPosition = (p) => ({ line: p.line, character: p.character });
const fromRange = (r) => ({ start: fromPosition(r.start), end: fromPosition(r.end) });
const toPosition = (p) => new vscode.Position(p.line, p.character);
const toRange = (r) => new vscode.Range(toPosition(r.start), toPosition(r.end));
const SEVERITY = [undefined, vscode.DiagnosticSeverity.Error, vscode.DiagnosticSeverity.Warning, vscode.DiagnosticSeverity.Information, vscode.DiagnosticSeverity.Hint];

function toDiagnostic(d) {
    const out = new vscode.Diagnostic(toRange(d.range), d.message, SEVERITY[d.severity] ?? vscode.DiagnosticSeverity.Error);
    out.source = d.source;
    return out;
}

function fromDiagnostic(d) {
    return { range: fromRange(d.range), message: d.message, severity: SEVERITY.indexOf(d.severity), source: d.source };
}

function toHover(h) {
    const c = h.contents;
    const text = typeof c === "string" ? c : Array.isArray(c) ? c.map((x) => x.value ?? x).join("\n\n") : c.value;
    return new vscode.Hover(new vscode.MarkdownString(text), h.range ? toRange(h.range) : undefined);
}

function toLocations(x) {
    return (Array.isArray(x) ? x : [x]).map((l) => new vscode.Location(vscode.Uri.parse(l.uri), toRange(l.range)));
}

function toSymbols(list) {
    // (LSP's kinds count from 1, VS Code's from 0.)
    const one = (s) => {
        const sym = new vscode.DocumentSymbol(s.name, s.detail || "", s.kind - 1, toRange(s.range), toRange(s.selectionRange || s.range));
        sym.children = (s.children || []).map(one);
        return sym;
    };
    return list.map((s) => s.location
        ? new vscode.SymbolInformation(s.name, s.kind - 1, s.containerName || "", new vscode.Location(vscode.Uri.parse(s.location.uri), toRange(s.location.range)))
        : one(s));
}

function toCompletions(x) {
    const items = Array.isArray(x) ? x : x.items;
    return new vscode.CompletionList(items.map((c) => {
        const item = new vscode.CompletionItem(c.label, c.kind ? c.kind - 1 : undefined);
        item.detail = c.detail;
        item.sortText = c.sortText;
        if (c.insertText) item.insertText = c.insertText;
        return item;
    }), !!x.isIncomplete);
}

function toWorkspaceEdit(w) {
    const edit = new vscode.WorkspaceEdit();
    for (const [uri, edits] of Object.entries(w.changes || {})) {
        for (const e of edits) edit.replace(vscode.Uri.parse(uri), toRange(e.range), e.newText);
    }
    for (const change of w.documentChanges || []) {
        for (const e of change.edits || []) edit.replace(vscode.Uri.parse(change.textDocument.uri), toRange(e.range), e.newText);
    }
    return edit;
}

function toCodeActions(list) {
    return list.map((a) => {
        const kind = a.kind ? vscode.CodeActionKind.Empty.append(a.kind) : undefined;
        const action = new vscode.CodeAction(a.title, kind);
        if (a.edit) action.edit = toWorkspaceEdit(a.edit);
        action.isPreferred = !!a.isPreferred;
        return action;
    });
}

// --- building and debugging ------------------------------------------------------

// A "mara" launch: `mara build` (its output in the Mara panel; errors stop
// it), then the program it made run under the C/C++ extension's debugger —
// cppvsdbg on Windows (the PDB), cppdbg with gdb elsewhere (DWARF).
const debugProvider = {
    provideDebugConfigurations() {
        return [{ type: "mara", request: "launch", name: "Build and debug", cwd: "${workspaceFolder}" }];
    },
    async resolveDebugConfiguration(folder, config) {
        if (!config.type && !config.request) {   // F5 with no launch.json
            const doc = vscode.window.activeTextEditor && vscode.window.activeTextEditor.document;
            if (!doc || doc.languageId !== "mara") return config;
            config = { type: "mara", request: "launch", name: "Build and debug", cwd: path.dirname(doc.uri.fsPath) };
        }
        if (!vscode.extensions.getExtension("ms-vscode.cpptools")) {
            vscode.window.showErrorMessage("Debugging a Mara program needs Microsoft's C/C++ extension (ms-vscode.cpptools): install it from the Extensions view.");
            return undefined;
        }
        // (Called before VS Code fills in its ${…} variables: the ones a
        // build needs filled in here.)
        const doc = vscode.window.activeTextEditor && vscode.window.activeTextEditor.document;
        const fill = (s) => s && s
            .replace(/\$\{workspaceFolder\}/g, (folder && folder.uri.fsPath) || workspaceDir() || "")
            .replace(/\$\{fileDirname\}/g, doc ? path.dirname(doc.uri.fsPath) : "")
            .replace(/\$\{file\}/g, doc ? doc.uri.fsPath : "");
        const cwd = fill(config.cwd) || (folder && folder.uri.fsPath) || workspaceDir();
        let program = config.program && path.resolve(cwd, fill(config.program));
        if (config.build !== false) {
            const args = ["build", ...(config.module ? [config.module] : []), ...(config.buildArgs || [])];
            out.appendLine(`> ${maraPath()} ${args.join(" ")}   (in ${cwd})`);
            const built = await run(maraPath(), args, cwd);
            out.append(built.text);
            if (built.code !== 0) {
                out.show(true);
                vscode.window.showErrorMessage("mara build failed: its errors are in the Mara output.");
                return undefined;
            }
            const made = /Compiled module '[^']*' -> (.+)$/m.exec(built.text);
            if (!program && made) program = path.resolve(cwd, made[1].trim());
        }
        if (!program) {
            vscode.window.showErrorMessage("Mara: no program to debug. Set \"program\" in the launch configuration.");
            return undefined;
        }
        const windows = process.platform === "win32";
        const debug = {
            type: windows ? "cppvsdbg" : "cppdbg",
            request: "launch",
            name: config.name || "Mara",
            program,
            args: config.args || [],
            cwd,
            stopAtEntry: !!config.stopAtEntry,
        };
        if (config.console) debug.console = config.console;
        if (!windows) debug.MIMode = "gdb";
        return debug;
    },
};

function run(command, args, cwd) {
    return new Promise((resolve) => {
        const proc = cp.spawn(command, args, { cwd });
        let text = "";
        proc.stdout.on("data", (d) => { text += d.toString(); });
        proc.stderr.on("data", (d) => { text += d.toString(); });
        proc.on("error", (e) => resolve({ code: -1, text: `couldn't run ${command}: ${e.message}\n` }));
        proc.on("close", (code) => resolve({ code, text }));
    });
}

// --- the window: `mara view` --------------------------------------------------
//
// As the Sublime plugin does: "Mara: Open View" opens the window on the file's
// module (`mara view`), or brings it here; when the cursor rests in a .mara file
// the window is told where it is (`mara ask -cursor cursor at <file>@<byte>`,
// the byte in the file as saved), and follows: its Docs panel looks up what's
// there, its Ask panel shows it; a save has its Docs read the files again
// (`mara docs -reload`) and Ask asked again. The windows are told VS Code is
// the editor a clicked place opens in (`mara editor <Code.exe> -g`).

let restTimer;       // the cursor's rest, waited for
let lastRest;        // what was last told: the same again isn't
let editorTold = false;

function viewSettings() { return vscode.workspace.getConfiguration("mara.view"); }

function registerView(context) {
    context.subscriptions.push(
        vscode.commands.registerCommand("mara.openView", openView),
        vscode.window.onDidChangeTextEditorSelection((e) => cursorMoved(e.textEditor)),
        vscode.workspace.onDidSaveTextDocument(savedForView));
}

async function openView() {
    const editor = vscode.window.activeTextEditor;
    const doc = editor && editor.document;
    if (!doc || doc.languageId !== "mara" || doc.isUntitled) {
        vscode.window.setStatusBarMessage("mara view: open a saved .mara file first — the window opens on its folder's module", 5000);
        return;
    }
    const cwd = path.dirname(doc.uri.fsPath);
    const module = moduleOf(doc.getText());
    const opened = await run(maraPath(), ["view", ...(module ? [module] : [])], cwd);
    if (opened.code !== 0) {
        vscode.window.setStatusBarMessage("mara view: " + (opened.text.trim().split("\n")[0] || `failed (exit ${opened.code})`), 8000);
        return;
    }
    const spec = byteSpec(doc, editor.selection);
    if (!spec) return;
    // (A window just opened may not listen yet: asked again, a little apart.)
    const giveUp = Date.now() + 8000;
    for (;;) {
        const docs = await run(maraPath(), ["docs", "at", spec], cwd);
        if (!docs.text.includes("no window is open") || Date.now() > giveUp) break;
        await new Promise((r) => setTimeout(r, 150));
    }
    await tellEditor(cwd);
    await run(maraPath(), ["ask", "-cursor", "what", "at", spec], cwd);
}

function cursorMoved(editor) {
    const doc = editor && editor.document;
    if (!doc || doc.languageId !== "mara" || doc.uri.scheme !== "file") return;
    if (!viewSettings().get("followCursor", true)) return;
    clearTimeout(restTimer);
    restTimer = setTimeout(() => cursorRested(editor), viewSettings().get("delayMs", 300));
}

async function cursorRested(editor) {
    if (vscode.window.activeTextEditor !== editor || editor.selections.length !== 1) return;
    const doc = editor.document, sel = editor.selection;
    if (!sel.isEmpty && (sel.start.line !== sel.end.line || sel.end.character - sel.start.character > 200)) return;
    const key = `${doc.uri.fsPath}|${sel.start.line}:${sel.start.character}-${sel.end.character}|${doc.version}`;
    if (key === lastRest) return;
    lastRest = key;
    const cwd = path.dirname(doc.uri.fsPath);
    await tellEditor(cwd);
    const spec = byteSpec(doc, sel);
    await run(maraPath(), ["ask", "-cursor", ...(spec ? ["cursor", "at", spec] : ["#unsaved"])], cwd);
}

async function savedForView(doc) {
    if (doc.languageId !== "mara" || doc.uri.scheme !== "file") return;
    const cwd = path.dirname(doc.uri.fsPath);
    await run(maraPath(), ["docs", "-reload"], cwd);
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document !== doc || !viewSettings().get("followCursor", true)) return;
    const spec = byteSpec(doc, editor.selection);
    if (spec) await run(maraPath(), ["ask", "-cursor", "what", "at", spec], cwd);
}

// The windows told VS Code opens a place clicked in them: this Code.exe, `-g
// <file>:<line>`. Once one has it (it keeps it for every window); till then,
// tried again at each rest.
async function tellEditor(cwd) {
    if (editorTold) return;
    const told = await run(maraPath(), ["editor", process.execPath, "-g"], cwd);
    editorTold = told.code === 0;
}

// The module a file declares: its first line that isn't blank or a comment
// (`//`, or a `/* … */` block, which nests).
function moduleOf(text) {
    let depth = 0;
    for (const line of text.slice(0, 8000).split("\n")) {
        const s = line.trim();
        if (depth > 0 || s.startsWith("/*")) {
            depth += (s.match(/\/\*/g) || []).length - (s.match(/\*\//g) || []).length;
            continue;
        }
        if (!s || s.startsWith("//")) continue;
        const m = /^module\s+([A-Za-z0-9_.]+)/.exec(s);
        return m ? m[1] : undefined;
    }
    return undefined;
}

// A selection on one line as the compiler takes it: "<file>@<byte>" or
// "<file>@<lo>-<hi>", bytes in the file as saved, from 0 (VS Code counts UTF-16
// units). With unsaved edits the line is found in the saved file; undefined
// when it isn't there yet.
function byteSpec(doc, sel) {
    let saved;
    try { saved = fs.readFileSync(doc.uri.fsPath); } catch { return undefined; }
    const lines = [];
    for (let at = 0; ;) {
        const nl = saved.indexOf(10, at);
        if (nl < 0) { lines.push(saved.subarray(at)); break; }
        lines.push(saved.subarray(at, nl));
        at = nl + 1;
    }
    let row = sel.start.line;
    if (doc.isDirty) {
        const now = doc.getText().split(/\r?\n/);
        row = savedLine(now, lines.map((b) => b.toString("utf8").replace(/\r$/, "")), row);
        if (row === undefined) return undefined;
    }
    if (row >= lines.length) return undefined;
    let start = 0;
    for (let i = 0; i < row; i++) start += lines[i].length + 1;
    const text = doc.lineAt(sel.start.line).text;
    const lo = start + Buffer.byteLength(text.slice(0, sel.start.character), "utf8");
    const hi = start + Buffer.byteLength(text.slice(0, sel.end.character), "utf8");
    const name = path.basename(doc.uri.fsPath);
    return lo === hi ? `${name}@${lo}` : `${name}@${lo}-${hi}`;
}

// The line in `saved` that line n of `now` is: the lines around an edit line
// up; between them, the longest run of lines both share. undefined when line n
// isn't in `saved`.
function savedLine(now, saved, n) {
    let start = 0;
    while (start < now.length && start < saved.length && now[start] === saved[start]) start++;
    if (n < start) return n;
    let nowEnd = now.length, savedEnd = saved.length;
    while (nowEnd > start && savedEnd > start && now[nowEnd - 1] === saved[savedEnd - 1]) { nowEnd--; savedEnd--; }
    if (n >= nowEnd) return n - nowEnd + savedEnd;
    // (The edited middle, usually a few lines: the longest common run, by table.)
    const a = now.slice(start, nowEnd), b = saved.slice(start, savedEnd);
    if (a.length * b.length > 4000000) return undefined;
    const table = Array.from({ length: a.length + 1 }, () => new Int32Array(b.length + 1));
    for (let i = a.length - 1; i >= 0; i--) {
        for (let j = b.length - 1; j >= 0; j--) {
            table[i][j] = a[i] === b[j] ? table[i + 1][j + 1] + 1 : Math.max(table[i + 1][j], table[i][j + 1]);
        }
    }
    for (let i = 0, j = 0; i < a.length && j < b.length;) {
        if (a[i] === b[j]) {
            if (start + i === n) return start + j;
            i++; j++;
        } else if (table[i + 1][j] >= table[i][j + 1]) {
            if (start + i === n) return undefined;
            i++;
        } else {
            j++;
        }
    }
    return undefined;
}

module.exports = { activate, deactivate };
