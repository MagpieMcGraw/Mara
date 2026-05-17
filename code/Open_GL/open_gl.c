// No system headers needed — this file declares everything it uses (GL types,
// printf forward-decl, NULL). That way Mara's auto-compile path can produce
// the static lib on a fresh clone without depending on glibc-devel / MSVC SDK
// headers being installed. The printf symbol still resolves at link time from
// libc.so.6 (Linux) / ucrt.dll (Windows), both of which are part of the OS.
//
// User-authored .c files in foreign blocks can use whatever headers they like
// — clang's normal search path is unchanged. This restriction applies only to
// the bundled bindings shipped with Mara.

// ---------------------------------------------------------------------------
// Stand-ins for the two libc pieces we'd otherwise pull from headers
// ---------------------------------------------------------------------------

extern int printf(const char *fmt, ...);
#define NULL ((void*)0)

// ---------------------------------------------------------------------------
// GL types — inline-typedef'd rather than pulled from <GL/gl.h>, which on
// Windows transitively requires <windows.h>. We only need the trivial integer
// shapes; the actual symbols (glClear, glCreateShader, etc.) are resolved at
// link time by the host platform — opengl32.lib on Windows for 1.1 symbols
// and SDL_GL_GetProcAddress'd at runtime for modern ones; emscripten's
// libGL.js for everything on web. Keeping this file header-free means it
// compiles unchanged under emcc with no platform shims.
// ---------------------------------------------------------------------------

typedef unsigned int  GLuint;
typedef unsigned int  GLenum;
typedef unsigned int  GLbitfield;
typedef int           GLsizei;
typedef int           GLint;
typedef float         GLfloat;
typedef unsigned char GLboolean;
typedef char          GLchar;
// GLsizeiptr / GLintptr are pointer-sized signed integers (8 bytes on every
// 64-bit target Mara cares about). `long long` is 64 bits everywhere; using
// it directly avoids needing <stddef.h> for ptrdiff_t.
typedef long long     GLsizeiptr;
typedef long long     GLintptr;

// Function pointer types
typedef GLuint (*PFN_glCreateShader)(GLenum type);
typedef void   (*PFN_glShaderSource)(GLuint shader, GLsizei count, const GLchar *const*string, const GLint *length);
typedef void   (*PFN_glCompileShader)(GLuint shader);
typedef void   (*PFN_glDeleteShader)(GLuint shader);
typedef GLuint (*PFN_glCreateProgram)(void);
typedef void   (*PFN_glAttachShader)(GLuint program, GLuint shader);
typedef void   (*PFN_glLinkProgram)(GLuint program);
typedef void   (*PFN_glDeleteProgram)(GLuint program);
typedef void   (*PFN_glUseProgram)(GLuint program);
typedef GLint  (*PFN_glGetUniformLocation)(GLuint program, const GLchar *name);
typedef void   (*PFN_glUniform1f)(GLint location, GLfloat v0);
typedef void   (*PFN_glUniform1i)(GLint location, GLint v0);
typedef void   (*PFN_glUniform2f)(GLint location, GLfloat v0, GLfloat v1);
typedef void   (*PFN_glUniform3f)(GLint location, GLfloat v0, GLfloat v1, GLfloat v2);
typedef void   (*PFN_glUniformMatrix4fv)(GLint location, GLsizei count, GLboolean transpose, const GLfloat *value);
typedef void   (*PFN_glGenVertexArrays)(GLsizei n, GLuint *arrays);
typedef void   (*PFN_glBindVertexArray)(GLuint array);
typedef void   (*PFN_glGenBuffers)(GLsizei n, GLuint *buffers);
typedef void   (*PFN_glBindBuffer)(GLenum target, GLuint buffer);
typedef void   (*PFN_glBufferData)(GLenum target, GLsizeiptr size, const void *data, GLenum usage);
typedef void   (*PFN_glBufferSubData)(GLenum target, GLintptr offset, GLsizeiptr size, const void *data);
typedef void   (*PFN_glEnableVertexAttribArray)(GLuint index);
typedef void   (*PFN_glVertexAttribPointer)(GLuint index, GLint size, GLenum type, GLboolean normalized, GLsizei stride, const void *pointer);
typedef void   (*PFN_glVertexAttribIPointer)(GLuint index, GLint size, GLenum type, GLsizei stride, const void *pointer);
typedef void   (*PFN_glVertexAttribDivisor)(GLuint index, GLuint divisor);
typedef void   (*PFN_glActiveTexture)(GLenum texture);
typedef void   (*PFN_glTexImage3D)(GLenum target, GLint level, GLint internalformat, GLsizei width, GLsizei height, GLsizei depth, GLint border, GLenum format, GLenum type, const void *pixels);
typedef void   (*PFN_glTexSubImage3D)(GLenum target, GLint level, GLint xoffset, GLint yoffset, GLint zoffset, GLsizei width, GLsizei height, GLsizei depth, GLenum format, GLenum type, const void *pixels);
typedef void   (*PFN_glGenerateMipmap)(GLenum target);
typedef void   (*PFN_glGetShaderiv)(GLuint shader, GLenum pname, GLint *params);
typedef void   (*PFN_glGetShaderInfoLog)(GLuint shader, GLsizei bufSize, GLsizei *length, GLchar *infoLog);
typedef void   (*PFN_glGetProgramiv)(GLuint program, GLenum pname, GLint *params);
typedef void   (*PFN_glGetProgramInfoLog)(GLuint program, GLsizei bufSize, GLsizei *length, GLchar *infoLog);
typedef void   (*PFN_glMultiDrawElementsIndirect)(GLenum mode, GLenum type, const void *indirect, GLsizei drawcount, GLsizei stride);
typedef void   (*PFN_glDetachShader)(GLuint program, GLuint shader);
typedef void   (*PFN_glDeleteVertexArrays)(GLsizei n, const GLuint *arrays);
typedef void   (*PFN_glDeleteBuffers)(GLsizei n, const GLuint *buffers);

// ---------------------------------------------------------------------------
// Internal function pointers
// ---------------------------------------------------------------------------
static PFN_glCreateShader             _glCreateShader;
static PFN_glShaderSource             _glShaderSource;
static PFN_glCompileShader            _glCompileShader;
static PFN_glDeleteShader             _glDeleteShader;
static PFN_glCreateProgram            _glCreateProgram;
static PFN_glAttachShader             _glAttachShader;
static PFN_glLinkProgram              _glLinkProgram;
static PFN_glDeleteProgram            _glDeleteProgram;
static PFN_glUseProgram               _glUseProgram;
static PFN_glGetUniformLocation       _glGetUniformLocation;
static PFN_glUniform1f                _glUniform1f;
static PFN_glUniform1i                _glUniform1i;
static PFN_glUniform2f                _glUniform2f;
static PFN_glUniform3f                _glUniform3f;
static PFN_glUniformMatrix4fv         _glUniformMatrix4fv;
static PFN_glGenVertexArrays          _glGenVertexArrays;
static PFN_glBindVertexArray          _glBindVertexArray;
static PFN_glGenBuffers               _glGenBuffers;
static PFN_glBindBuffer               _glBindBuffer;
static PFN_glBufferData               _glBufferData;
static PFN_glBufferSubData            _glBufferSubData;
static PFN_glEnableVertexAttribArray  _glEnableVertexAttribArray;
static PFN_glVertexAttribPointer      _glVertexAttribPointer;
static PFN_glVertexAttribIPointer     _glVertexAttribIPointer;
static PFN_glVertexAttribDivisor      _glVertexAttribDivisor;
static PFN_glActiveTexture            _glActiveTexture;
static PFN_glTexImage3D               _glTexImage3D;
static PFN_glTexSubImage3D            _glTexSubImage3D;
static PFN_glGenerateMipmap           _glGenerateMipmap;
static PFN_glGetShaderiv              _glGetShaderiv;
static PFN_glGetShaderInfoLog         _glGetShaderInfoLog;
static PFN_glGetProgramiv             _glGetProgramiv;
static PFN_glGetProgramInfoLog        _glGetProgramInfoLog;
static PFN_glMultiDrawElementsIndirect _glMultiDrawElementsIndirect;
static PFN_glDetachShader              _glDetachShader;
static PFN_glDeleteVertexArrays        _glDeleteVertexArrays;
static PFN_glDeleteBuffers             _glDeleteBuffers;

// ---------------------------------------------------------------------------
// Loader — call after creating a GL context. Caller passes the platform's
// proc-address function (typically SDL_GL_GetProcAddress) so this file has no
// link-time dependency on a specific windowing library.
// ---------------------------------------------------------------------------
typedef void *(*GetProcAddressFn)(const char *);

void gl_load(GetProcAddressFn SDL_GL_GetProcAddress) {
    _glCreateShader            = (PFN_glCreateShader)SDL_GL_GetProcAddress("glCreateShader");
    _glShaderSource            = (PFN_glShaderSource)SDL_GL_GetProcAddress("glShaderSource");
    _glCompileShader           = (PFN_glCompileShader)SDL_GL_GetProcAddress("glCompileShader");
    _glDeleteShader            = (PFN_glDeleteShader)SDL_GL_GetProcAddress("glDeleteShader");
    _glCreateProgram           = (PFN_glCreateProgram)SDL_GL_GetProcAddress("glCreateProgram");
    _glAttachShader            = (PFN_glAttachShader)SDL_GL_GetProcAddress("glAttachShader");
    _glLinkProgram             = (PFN_glLinkProgram)SDL_GL_GetProcAddress("glLinkProgram");
    _glDeleteProgram           = (PFN_glDeleteProgram)SDL_GL_GetProcAddress("glDeleteProgram");
    _glUseProgram              = (PFN_glUseProgram)SDL_GL_GetProcAddress("glUseProgram");
    _glGetUniformLocation      = (PFN_glGetUniformLocation)SDL_GL_GetProcAddress("glGetUniformLocation");
    _glUniform1f               = (PFN_glUniform1f)SDL_GL_GetProcAddress("glUniform1f");
    _glUniform1i               = (PFN_glUniform1i)SDL_GL_GetProcAddress("glUniform1i");
    _glUniform2f               = (PFN_glUniform2f)SDL_GL_GetProcAddress("glUniform2f");
    _glUniform3f               = (PFN_glUniform3f)SDL_GL_GetProcAddress("glUniform3f");
    _glUniformMatrix4fv        = (PFN_glUniformMatrix4fv)SDL_GL_GetProcAddress("glUniformMatrix4fv");
    _glGenVertexArrays         = (PFN_glGenVertexArrays)SDL_GL_GetProcAddress("glGenVertexArrays");
    _glBindVertexArray         = (PFN_glBindVertexArray)SDL_GL_GetProcAddress("glBindVertexArray");
    _glGenBuffers              = (PFN_glGenBuffers)SDL_GL_GetProcAddress("glGenBuffers");
    _glBindBuffer              = (PFN_glBindBuffer)SDL_GL_GetProcAddress("glBindBuffer");
    _glBufferData              = (PFN_glBufferData)SDL_GL_GetProcAddress("glBufferData");
    _glBufferSubData           = (PFN_glBufferSubData)SDL_GL_GetProcAddress("glBufferSubData");
    _glEnableVertexAttribArray = (PFN_glEnableVertexAttribArray)SDL_GL_GetProcAddress("glEnableVertexAttribArray");
    _glVertexAttribPointer     = (PFN_glVertexAttribPointer)SDL_GL_GetProcAddress("glVertexAttribPointer");
    _glVertexAttribIPointer    = (PFN_glVertexAttribIPointer)SDL_GL_GetProcAddress("glVertexAttribIPointer");
    _glVertexAttribDivisor     = (PFN_glVertexAttribDivisor)SDL_GL_GetProcAddress("glVertexAttribDivisor");
    _glActiveTexture           = (PFN_glActiveTexture)SDL_GL_GetProcAddress("glActiveTexture");
    _glTexImage3D              = (PFN_glTexImage3D)SDL_GL_GetProcAddress("glTexImage3D");
    _glTexSubImage3D           = (PFN_glTexSubImage3D)SDL_GL_GetProcAddress("glTexSubImage3D");
    _glGenerateMipmap          = (PFN_glGenerateMipmap)SDL_GL_GetProcAddress("glGenerateMipmap");
    _glGetShaderiv             = (PFN_glGetShaderiv)SDL_GL_GetProcAddress("glGetShaderiv");
    _glGetShaderInfoLog        = (PFN_glGetShaderInfoLog)SDL_GL_GetProcAddress("glGetShaderInfoLog");
    _glGetProgramiv            = (PFN_glGetProgramiv)SDL_GL_GetProcAddress("glGetProgramiv");
    _glGetProgramInfoLog       = (PFN_glGetProgramInfoLog)SDL_GL_GetProcAddress("glGetProgramInfoLog");
    _glMultiDrawElementsIndirect = (PFN_glMultiDrawElementsIndirect)SDL_GL_GetProcAddress("glMultiDrawElementsIndirect");
    _glDetachShader              = (PFN_glDetachShader)SDL_GL_GetProcAddress("glDetachShader");
    _glDeleteVertexArrays        = (PFN_glDeleteVertexArrays)SDL_GL_GetProcAddress("glDeleteVertexArrays");
    _glDeleteBuffers             = (PFN_glDeleteBuffers)SDL_GL_GetProcAddress("glDeleteBuffers");
}

// ---------------------------------------------------------------------------
// Wrapper functions — these are real function symbols that LLVM IR can call
// ---------------------------------------------------------------------------

// Shaders
GLuint glCreateShader(GLenum type)                                                    { return _glCreateShader(type); }
void   glShaderSource(GLuint shader, GLsizei count, const GLchar *const*string, const GLint *length) { _glShaderSource(shader, count, string, length); }
void   glCompileShader(GLuint shader)                                                 { _glCompileShader(shader); }
void   glDeleteShader(GLuint shader)                                                  { _glDeleteShader(shader); }

// Programs
GLuint glCreateProgram(void)                                                          { return _glCreateProgram(); }
void   glAttachShader(GLuint program, GLuint shader)                                  { _glAttachShader(program, shader); }
void   glLinkProgram(GLuint program)                                                  { _glLinkProgram(program); }
void   glDeleteProgram(GLuint program)                                                { _glDeleteProgram(program); }
void   glUseProgram(GLuint program)                                                   { _glUseProgram(program); }

// Uniforms
GLint  glGetUniformLocation(GLuint program, const GLchar *name)                       { return _glGetUniformLocation(program, name); }
void   glUniform1f(GLint location, GLfloat v0)                                        { _glUniform1f(location, v0); }
void   glUniform2f(GLint location, GLfloat v0, GLfloat v1)                            { _glUniform2f(location, v0, v1); }
void   glUniform3f(GLint location, GLfloat v0, GLfloat v1, GLfloat v2)                { _glUniform3f(location, v0, v1, v2); }
void   glUniform1i(GLint location, GLint v0)                                          { _glUniform1i(location, v0); }
void   glUniformMatrix4fv(GLint location, GLsizei count, GLboolean transpose, const GLfloat *value) { _glUniformMatrix4fv(location, count, transpose, value); }

// VAOs
void   glGenVertexArrays(GLsizei n, GLuint *arrays)                                   { _glGenVertexArrays(n, arrays); }
void   glBindVertexArray(GLuint array)                                                { _glBindVertexArray(array); }

// Buffers
void   glGenBuffers(GLsizei n, GLuint *buffers)                                       { _glGenBuffers(n, buffers); }
void   glBindBuffer(GLenum target, GLuint buffer)                                     { _glBindBuffer(target, buffer); }
void   glBufferData(GLenum target, GLsizeiptr size, const void *data, GLenum usage)   { _glBufferData(target, size, data, usage); }
void   glBufferSubData(GLenum target, GLintptr offset, GLsizeiptr size, const void *data) { _glBufferSubData(target, offset, size, data); }

// Vertex attributes
void   glEnableVertexAttribArray(GLuint index)                                        { _glEnableVertexAttribArray(index); }
void   glVertexAttribPointer(GLuint index, GLint size, GLenum type, GLboolean normalized, GLsizei stride, const void *pointer) { _glVertexAttribPointer(index, size, type, normalized, stride, pointer); }
void   glVertexAttribIPointer(GLuint index, GLint size, GLenum type, GLsizei stride, const void *pointer) { _glVertexAttribIPointer(index, size, type, stride, pointer); }
void   glVertexAttribDivisor(GLuint index, GLuint divisor)                            { _glVertexAttribDivisor(index, divisor); }

// Texture
void   glActiveTexture(GLenum texture)                                                { _glActiveTexture(texture); }
void   glTexImage3D(GLenum target, GLint level, GLint internalformat, GLsizei width, GLsizei height, GLsizei depth, GLint border, GLenum format, GLenum type, const void *pixels) { _glTexImage3D(target, level, internalformat, width, height, depth, border, format, type, pixels); }
void   glTexSubImage3D(GLenum target, GLint level, GLint xoffset, GLint yoffset, GLint zoffset, GLsizei width, GLsizei height, GLsizei depth, GLenum format, GLenum type, const void *pixels) { _glTexSubImage3D(target, level, xoffset, yoffset, zoffset, width, height, depth, format, type, pixels); }
void   glGenerateMipmap(GLenum target)                                                { _glGenerateMipmap(target); }

// Shader info
void   glGetShaderiv(GLuint shader, GLenum pname, GLint *params)                      { _glGetShaderiv(shader, pname, params); }
void   glGetShaderInfoLog(GLuint shader, GLsizei bufSize, GLsizei *length, GLchar *infoLog) { _glGetShaderInfoLog(shader, bufSize, length, infoLog); }
void   glGetProgramiv(GLuint program, GLenum pname, GLint *params)                    { _glGetProgramiv(program, pname, params); }
void   glGetProgramInfoLog(GLuint program, GLsizei bufSize, GLsizei *length, GLchar *infoLog) { _glGetProgramInfoLog(program, bufSize, length, infoLog); }

// Shader management
void   glDetachShader(GLuint program, GLuint shader)                                   { _glDetachShader(program, shader); }

// Cleanup
void   glDeleteVertexArrays(GLsizei n, const GLuint *arrays)                           { _glDeleteVertexArrays(n, arrays); }
void   glDeleteBuffers(GLsizei n, const GLuint *buffers)                               { _glDeleteBuffers(n, buffers); }

// Multi-draw indirect
void   glMultiDrawElementsIndirect(GLenum mode, GLenum type, const void *indirect, GLsizei drawcount, GLsizei stride) { _glMultiDrawElementsIndirect(mode, type, indirect, drawcount, stride); }

// ---------------------------------------------------------------------------
// Shader/program convenience helpers — Mara's binding layer can't easily pass
// `const char* const*` for glShaderSource, and the compile/link error-check
// dance is the same for every shader anyway. These wrappers do the verbose
// part and report errors via printf so callers see compile/link diagnostics
// immediately. Return 0 on failure, matching how OpenGL signals invalid
// object names.
// ---------------------------------------------------------------------------

#define GL_COMPILE_STATUS 0x8B81
#define GL_LINK_STATUS    0x8B82

GLuint gl_compile_shader(GLenum type, const char *src) {
    GLuint shader = _glCreateShader(type);
    const char *sources[1] = { src };
    _glShaderSource(shader, 1, sources, NULL);
    _glCompileShader(shader);
    GLint status = 0;
    _glGetShaderiv(shader, GL_COMPILE_STATUS, &status);
    if (!status) {
        char log[1024];
        _glGetShaderInfoLog(shader, sizeof(log), NULL, log);
        printf("[gl] shader compile error: %s\n", log);
        _glDeleteShader(shader);
        return 0;
    }
    return shader;
}

GLuint gl_link_program(GLuint vs, GLuint fs) {
    GLuint program = _glCreateProgram();
    _glAttachShader(program, vs);
    _glAttachShader(program, fs);
    _glLinkProgram(program);
    GLint status = 0;
    _glGetProgramiv(program, GL_LINK_STATUS, &status);
    if (!status) {
        char log[1024];
        _glGetProgramInfoLog(program, sizeof(log), NULL, log);
        printf("[gl] program link error: %s\n", log);
        _glDeleteProgram(program);
        return 0;
    }
    return program;
}
