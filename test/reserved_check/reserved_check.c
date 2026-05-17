// Inspect SDL3's `reserved` field on every event SDL dispatches.
// Mirrors swap_test's setup (SDL3 + OpenGL 4.5 Core + render loop) so the
// keyboard-event-eating conditions are reproduced. Prints every event with
// type / reserved / timestamp; flags any event whose reserved != 0.
//
// Build (run from this directory):
//   "C:\Program Files\LLVM\bin\clang.exe" reserved_check.c ^
//     -I "../../code/SDL/include" -L "../../code/SDL" ^
//     -lSDL3 -lopengl32 -o reserved_check.exe
//
// Run:
//   Copy SDL3.dll next to the exe (or use the one in this dir if present),
//   then ./reserved_check.exe. Press keys / move mouse / close window.

#include <stdio.h>
#include <stdint.h>
#include <SDL3/SDL.h>
#include <SDL3/SDL_opengl.h>

static const char *event_name(Uint32 type) {
    switch (type) {
    case SDL_EVENT_QUIT:                  return "Quit";
    case SDL_EVENT_TERMINATING:           return "Terminating";
    case SDL_EVENT_KEY_DOWN:              return "KeyDown";
    case SDL_EVENT_KEY_UP:                return "KeyUp";
    case SDL_EVENT_TEXT_EDITING:          return "TextEditing";
    case SDL_EVENT_TEXT_INPUT:            return "TextInput";
    case SDL_EVENT_MOUSE_MOTION:          return "MouseMotion";
    case SDL_EVENT_MOUSE_BUTTON_DOWN:     return "MouseButtonDown";
    case SDL_EVENT_MOUSE_BUTTON_UP:       return "MouseButtonUp";
    case SDL_EVENT_MOUSE_WHEEL:           return "MouseWheel";
    case SDL_EVENT_WINDOW_SHOWN:          return "WindowShown";
    case SDL_EVENT_WINDOW_HIDDEN:         return "WindowHidden";
    case SDL_EVENT_WINDOW_EXPOSED:        return "WindowExposed";
    case SDL_EVENT_WINDOW_MOVED:          return "WindowMoved";
    case SDL_EVENT_WINDOW_RESIZED:        return "WindowResized";
    case SDL_EVENT_WINDOW_FOCUS_GAINED:   return "WindowFocusGained";
    case SDL_EVENT_WINDOW_FOCUS_LOST:     return "WindowFocusLost";
    case SDL_EVENT_WINDOW_MOUSE_ENTER:    return "WindowMouseEnter";
    case SDL_EVENT_WINDOW_MOUSE_LEAVE:    return "WindowMouseLeave";
    case SDL_EVENT_WINDOW_CLOSE_REQUESTED:return "WindowCloseRequested";
    case SDL_EVENT_DROP_FILE:             return "DropFile";
    case SDL_EVENT_DROP_TEXT:             return "DropText";
    case SDL_EVENT_DROP_BEGIN:            return "DropBegin";
    case SDL_EVENT_DROP_COMPLETE:         return "DropComplete";
    case SDL_EVENT_DROP_POSITION:         return "DropPosition";
    default:                              return "(other)";
    }
}

int main(int argc, char *argv[]) {
    (void)argc; (void)argv;

    if (!SDL_Init(SDL_INIT_VIDEO)) {
        fprintf(stderr, "SDL_Init failed: %s\n", SDL_GetError());
        return 1;
    }

    SDL_GL_SetAttribute(SDL_GL_CONTEXT_PROFILE_MASK, SDL_GL_CONTEXT_PROFILE_CORE);
    SDL_GL_SetAttribute(SDL_GL_CONTEXT_MAJOR_VERSION, 4);
    SDL_GL_SetAttribute(SDL_GL_CONTEXT_MINOR_VERSION, 5);

    SDL_Window *win = SDL_CreateWindow("reserved check", 400, 300, SDL_WINDOW_OPENGL);
    if (!win) {
        fprintf(stderr, "CreateWindow failed: %s\n", SDL_GetError());
        SDL_Quit();
        return 1;
    }

    SDL_GLContext ctx = SDL_GL_CreateContext(win);
    if (!ctx) {
        fprintf(stderr, "GL_CreateContext failed: %s\n", SDL_GetError());
        SDL_DestroyWindow(win);
        SDL_Quit();
        return 1;
    }

    printf("Polling. Press keys, move mouse, close window to quit.\n");
    printf("Each event line shows what SDL writes to type / reserved / timestamp.\n");
    printf("Lines with `<-- reserved!=0` are the cases worth investigating.\n\n");
    fflush(stdout);

    int running = 1;
    while (running) {
        SDL_Event e;
        while (SDL_PollEvent(&e)) {
            const char *flag = e.common.reserved != 0 ? "  <-- reserved!=0" : "";
            printf("type=0x%08x (%-22s) reserved=0x%08x (%u) ts=%llu",
                   (unsigned)e.common.type,
                   event_name(e.common.type),
                   (unsigned)e.common.reserved,
                   (unsigned)e.common.reserved,
                   (unsigned long long)e.common.timestamp);
            if (e.type == SDL_EVENT_KEY_DOWN || e.type == SDL_EVENT_KEY_UP) {
                printf(" scancode=%d key=0x%x repeat=%d",
                       (int)e.key.scancode, (unsigned)e.key.key, (int)e.key.repeat);
            }
            printf("%s\n", flag);
            fflush(stdout);

            if (e.type == SDL_EVENT_QUIT) {
                running = 0;
            }
        }

        glClearColor(0.5f, 0.5f, 0.5f, 1.0f);
        glClear(GL_COLOR_BUFFER_BIT);
        SDL_GL_SwapWindow(win);
    }

    SDL_GL_DestroyContext(ctx);
    SDL_DestroyWindow(win);
    SDL_Quit();
    return 0;
}
