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
typedef unsigned long long GLuint64;   // a bindless texture's handle
typedef unsigned char GLubyte;

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
typedef void   (*PFN_glUniform4f)(GLint location, GLfloat v0, GLfloat v1, GLfloat v2, GLfloat v3);
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
typedef void   (*PFN_glCompressedTexImage2D)(GLenum target, GLint level, GLenum internalformat, GLsizei width, GLsizei height, GLint border, GLsizei imageSize, const void *data);
typedef void   (*PFN_glCompressedTexImage3D)(GLenum target, GLint level, GLenum internalformat, GLsizei width, GLsizei height, GLsizei depth, GLint border, GLsizei imageSize, const void *data);
typedef void   (*PFN_glCompressedTexSubImage3D)(GLenum target, GLint level, GLint xoffset, GLint yoffset, GLint zoffset, GLsizei width, GLsizei height, GLsizei depth, GLenum format, GLsizei imageSize, const void *data);
typedef void   (*PFN_glTexStorage2D)(GLenum target, GLsizei levels, GLenum internalformat, GLsizei width, GLsizei height);
typedef void   (*PFN_glTexStorage3D)(GLenum target, GLsizei levels, GLenum internalformat, GLsizei width, GLsizei height, GLsizei depth);
typedef void   (*PFN_glBindBufferBase)(GLenum target, GLuint index, GLuint buffer);
typedef const GLubyte *(*PFN_glGetStringi)(GLenum name, GLuint index);
typedef GLuint64 (*PFN_glGetTextureHandleARB)(GLuint texture);
typedef void   (*PFN_glMakeTextureHandleResidentARB)(GLuint64 handle);
typedef void   (*PFN_glMakeTextureHandleNonResidentARB)(GLuint64 handle);
typedef void   (*PFN_glUniformHandleui64ARB)(GLint location, GLuint64 value);
typedef void   (*PFN_glGenFramebuffers)(GLsizei n, GLuint *framebuffers);
typedef void   (*PFN_glDeleteFramebuffers)(GLsizei n, const GLuint *framebuffers);
typedef void   (*PFN_glBindFramebuffer)(GLenum target, GLuint framebuffer);
typedef void   (*PFN_glFramebufferTexture2D)(GLenum target, GLenum attachment, GLenum textarget, GLuint texture, GLint level);
typedef void   (*PFN_glFramebufferTextureLayer)(GLenum target, GLenum attachment, GLuint texture, GLint level, GLint layer);
typedef GLenum (*PFN_glCheckFramebufferStatus)(GLenum target);
typedef void   (*PFN_glGenRenderbuffers)(GLsizei n, GLuint *renderbuffers);
typedef void   (*PFN_glDeleteRenderbuffers)(GLsizei n, const GLuint *renderbuffers);
typedef void   (*PFN_glBindRenderbuffer)(GLenum target, GLuint renderbuffer);
typedef void   (*PFN_glRenderbufferStorage)(GLenum target, GLenum internalformat, GLsizei width, GLsizei height);
typedef void   (*PFN_glFramebufferRenderbuffer)(GLenum target, GLenum attachment, GLenum renderbuffertarget, GLuint renderbuffer);
typedef void   (*PFN_glDrawBuffers)(GLsizei n, const GLenum *bufs);
typedef void   (*PFN_glBlitFramebuffer)(GLint srcX0, GLint srcY0, GLint srcX1, GLint srcY1, GLint dstX0, GLint dstY0, GLint dstX1, GLint dstY1, GLbitfield mask, GLenum filter);
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
static PFN_glUniform4f                _glUniform4f;
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
static PFN_glCompressedTexImage2D     _glCompressedTexImage2D;
static PFN_glCompressedTexImage3D     _glCompressedTexImage3D;
static PFN_glCompressedTexSubImage3D  _glCompressedTexSubImage3D;
static PFN_glTexStorage2D             _glTexStorage2D;
static PFN_glTexStorage3D             _glTexStorage3D;
static PFN_glBindBufferBase           _glBindBufferBase;
static PFN_glGetStringi               _glGetStringi;
static PFN_glGetTextureHandleARB      _glGetTextureHandleARB;
static PFN_glMakeTextureHandleResidentARB    _glMakeTextureHandleResidentARB;
static PFN_glMakeTextureHandleNonResidentARB _glMakeTextureHandleNonResidentARB;
static PFN_glUniformHandleui64ARB    _glUniformHandleui64ARB;
static PFN_glGenFramebuffers          _glGenFramebuffers;
static PFN_glDeleteFramebuffers       _glDeleteFramebuffers;
static PFN_glBindFramebuffer          _glBindFramebuffer;
static PFN_glFramebufferTexture2D     _glFramebufferTexture2D;
static PFN_glFramebufferTextureLayer  _glFramebufferTextureLayer;
static PFN_glCheckFramebufferStatus   _glCheckFramebufferStatus;
static PFN_glGenRenderbuffers         _glGenRenderbuffers;
static PFN_glDeleteRenderbuffers      _glDeleteRenderbuffers;
static PFN_glBindRenderbuffer         _glBindRenderbuffer;
static PFN_glRenderbufferStorage      _glRenderbufferStorage;
static PFN_glFramebufferRenderbuffer  _glFramebufferRenderbuffer;
static PFN_glDrawBuffers              _glDrawBuffers;
static PFN_glBlitFramebuffer          _glBlitFramebuffer;
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
// The functions open_gl.c loads, each its name and its pointer. gl_load
// (open_gl.mara's) asks the platform's proc-address function for each by
// name once a context is current, and sets it here: NULL for one the
// driver hasn't (an extension's, ARB_bindless_texture's: gl_has_extension).
// ---------------------------------------------------------------------------
typedef struct { const char *name; void **at; } Gl_Proc;

static Gl_Proc gl_procs[] = {
    {"glCreateShader",                    (void **)&_glCreateShader},
    {"glShaderSource",                    (void **)&_glShaderSource},
    {"glCompileShader",                   (void **)&_glCompileShader},
    {"glDeleteShader",                    (void **)&_glDeleteShader},
    {"glCreateProgram",                   (void **)&_glCreateProgram},
    {"glAttachShader",                    (void **)&_glAttachShader},
    {"glLinkProgram",                     (void **)&_glLinkProgram},
    {"glDeleteProgram",                   (void **)&_glDeleteProgram},
    {"glUseProgram",                      (void **)&_glUseProgram},
    {"glGetUniformLocation",              (void **)&_glGetUniformLocation},
    {"glUniform1f",                       (void **)&_glUniform1f},
    {"glUniform1i",                       (void **)&_glUniform1i},
    {"glUniform2f",                       (void **)&_glUniform2f},
    {"glUniform3f",                       (void **)&_glUniform3f},
    {"glUniform4f",                       (void **)&_glUniform4f},
    {"glUniformMatrix4fv",                (void **)&_glUniformMatrix4fv},
    {"glGenVertexArrays",                 (void **)&_glGenVertexArrays},
    {"glBindVertexArray",                 (void **)&_glBindVertexArray},
    {"glGenBuffers",                      (void **)&_glGenBuffers},
    {"glBindBuffer",                      (void **)&_glBindBuffer},
    {"glBufferData",                      (void **)&_glBufferData},
    {"glBufferSubData",                   (void **)&_glBufferSubData},
    {"glEnableVertexAttribArray",         (void **)&_glEnableVertexAttribArray},
    {"glVertexAttribPointer",             (void **)&_glVertexAttribPointer},
    {"glVertexAttribIPointer",            (void **)&_glVertexAttribIPointer},
    {"glVertexAttribDivisor",             (void **)&_glVertexAttribDivisor},
    {"glActiveTexture",                   (void **)&_glActiveTexture},
    {"glTexImage3D",                      (void **)&_glTexImage3D},
    {"glTexSubImage3D",                   (void **)&_glTexSubImage3D},
    {"glGenerateMipmap",                  (void **)&_glGenerateMipmap},
    {"glCompressedTexImage2D",            (void **)&_glCompressedTexImage2D},
    {"glCompressedTexImage3D",            (void **)&_glCompressedTexImage3D},
    {"glCompressedTexSubImage3D",         (void **)&_glCompressedTexSubImage3D},
    {"glTexStorage2D",                    (void **)&_glTexStorage2D},
    {"glTexStorage3D",                    (void **)&_glTexStorage3D},
    {"glBindBufferBase",                  (void **)&_glBindBufferBase},
    {"glGetStringi",                      (void **)&_glGetStringi},
    {"glGetTextureHandleARB",             (void **)&_glGetTextureHandleARB},
    {"glMakeTextureHandleResidentARB",    (void **)&_glMakeTextureHandleResidentARB},
    {"glMakeTextureHandleNonResidentARB", (void **)&_glMakeTextureHandleNonResidentARB},
    {"glUniformHandleui64ARB",            (void **)&_glUniformHandleui64ARB},
    {"glGenFramebuffers",                 (void **)&_glGenFramebuffers},
    {"glDeleteFramebuffers",              (void **)&_glDeleteFramebuffers},
    {"glBindFramebuffer",                 (void **)&_glBindFramebuffer},
    {"glFramebufferTexture2D",            (void **)&_glFramebufferTexture2D},
    {"glFramebufferTextureLayer",         (void **)&_glFramebufferTextureLayer},
    {"glCheckFramebufferStatus",          (void **)&_glCheckFramebufferStatus},
    {"glGenRenderbuffers",                (void **)&_glGenRenderbuffers},
    {"glDeleteRenderbuffers",             (void **)&_glDeleteRenderbuffers},
    {"glBindRenderbuffer",                (void **)&_glBindRenderbuffer},
    {"glRenderbufferStorage",             (void **)&_glRenderbufferStorage},
    {"glFramebufferRenderbuffer",         (void **)&_glFramebufferRenderbuffer},
    {"glDrawBuffers",                     (void **)&_glDrawBuffers},
    {"glBlitFramebuffer",                 (void **)&_glBlitFramebuffer},
    {"glGetShaderiv",                     (void **)&_glGetShaderiv},
    {"glGetShaderInfoLog",                (void **)&_glGetShaderInfoLog},
    {"glGetProgramiv",                    (void **)&_glGetProgramiv},
    {"glGetProgramInfoLog",               (void **)&_glGetProgramInfoLog},
    {"glMultiDrawElementsIndirect",       (void **)&_glMultiDrawElementsIndirect},
    {"glDetachShader",                    (void **)&_glDetachShader},
    {"glDeleteVertexArrays",              (void **)&_glDeleteVertexArrays},
    {"glDeleteBuffers",                   (void **)&_glDeleteBuffers},
};

int         mara_gl_proc_count(void)              { return (int)(sizeof(gl_procs) / sizeof(gl_procs[0])); }
const char *mara_gl_proc_name(int i)              { return gl_procs[i].name; }
void        mara_gl_proc_set(int i, void *address) { *gl_procs[i].at = address; }

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
void   glUniform4f(GLint location, GLfloat v0, GLfloat v1, GLfloat v2, GLfloat v3)    { _glUniform4f(location, v0, v1, v2, v3); }
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
void   glBindBufferBase(GLenum target, GLuint index, GLuint buffer)                   { _glBindBufferBase(target, index, buffer); }

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
void   glCompressedTexImage2D(GLenum target, GLint level, GLenum internalformat, GLsizei width, GLsizei height, GLint border, GLsizei imageSize, const void *data) { _glCompressedTexImage2D(target, level, internalformat, width, height, border, imageSize, data); }
void   glCompressedTexImage3D(GLenum target, GLint level, GLenum internalformat, GLsizei width, GLsizei height, GLsizei depth, GLint border, GLsizei imageSize, const void *data) { _glCompressedTexImage3D(target, level, internalformat, width, height, depth, border, imageSize, data); }
void   glCompressedTexSubImage3D(GLenum target, GLint level, GLint xoffset, GLint yoffset, GLint zoffset, GLsizei width, GLsizei height, GLsizei depth, GLenum format, GLsizei imageSize, const void *data) { _glCompressedTexSubImage3D(target, level, xoffset, yoffset, zoffset, width, height, depth, format, imageSize, data); }
void   glTexStorage2D(GLenum target, GLsizei levels, GLenum internalformat, GLsizei width, GLsizei height) { _glTexStorage2D(target, levels, internalformat, width, height); }
void   glTexStorage3D(GLenum target, GLsizei levels, GLenum internalformat, GLsizei width, GLsizei height, GLsizei depth) { _glTexStorage3D(target, levels, internalformat, width, height, depth); }

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

// Framebuffers and renderbuffers
void   glGenFramebuffers(GLsizei n, GLuint *framebuffers) { _glGenFramebuffers(n, framebuffers); }
void   glDeleteFramebuffers(GLsizei n, const GLuint *framebuffers) { _glDeleteFramebuffers(n, framebuffers); }
void   glBindFramebuffer(GLenum target, GLuint framebuffer) { _glBindFramebuffer(target, framebuffer); }
void   glFramebufferTexture2D(GLenum target, GLenum attachment, GLenum textarget, GLuint texture, GLint level) { _glFramebufferTexture2D(target, attachment, textarget, texture, level); }
void   glFramebufferTextureLayer(GLenum target, GLenum attachment, GLuint texture, GLint level, GLint layer) { _glFramebufferTextureLayer(target, attachment, texture, level, layer); }
GLenum glCheckFramebufferStatus(GLenum target) { return _glCheckFramebufferStatus(target); }
void   glGenRenderbuffers(GLsizei n, GLuint *renderbuffers) { _glGenRenderbuffers(n, renderbuffers); }
void   glDeleteRenderbuffers(GLsizei n, const GLuint *renderbuffers) { _glDeleteRenderbuffers(n, renderbuffers); }
void   glBindRenderbuffer(GLenum target, GLuint renderbuffer) { _glBindRenderbuffer(target, renderbuffer); }
void   glRenderbufferStorage(GLenum target, GLenum internalformat, GLsizei width, GLsizei height) { _glRenderbufferStorage(target, internalformat, width, height); }
void   glFramebufferRenderbuffer(GLenum target, GLenum attachment, GLenum renderbuffertarget, GLuint renderbuffer) { _glFramebufferRenderbuffer(target, attachment, renderbuffertarget, renderbuffer); }
void   glDrawBuffers(GLsizei n, const GLenum *bufs) { _glDrawBuffers(n, bufs); }
void   glBlitFramebuffer(GLint srcX0, GLint srcY0, GLint srcX1, GLint srcY1, GLint dstX0, GLint dstY0, GLint dstX1, GLint dstY1, GLbitfield mask, GLenum filter) { _glBlitFramebuffer(srcX0, srcY0, srcX1, srcY1, dstX0, dstY0, dstX1, dstY1, mask, filter); }

// Bindless textures (ARB_bindless_texture)
GLuint64 glGetTextureHandleARB(GLuint texture)                                        { return _glGetTextureHandleARB(texture); }
void   glMakeTextureHandleResidentARB(GLuint64 handle)                                { _glMakeTextureHandleResidentARB(handle); }
void   glMakeTextureHandleNonResidentARB(GLuint64 handle)                             { _glMakeTextureHandleNonResidentARB(handle); }
void   glUniformHandleui64ARB(GLint location, GLuint64 value)                         { _glUniformHandleui64ARB(location, value); }

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
#define GL_EXTENSIONS     0x1F03
#define GL_NUM_EXTENSIONS 0x821D

extern void glGetIntegerv(GLenum pname, GLint *data);   // GL 1.1, opengl32

// 1 when the context's driver has the extension `name`
// ("GL_ARB_bindless_texture"), else 0: its functions are there to call only
// then. Asks GL for its extensions one at a time (GL 3.0).
GLboolean mara_gl_has_extension(const char *name) {
    if (!_glGetStringi) return 0;
    GLint count = 0;
    glGetIntegerv(GL_NUM_EXTENSIONS, &count);
    for (GLint i = 0; i < count; i++) {
        const GLubyte *ext = _glGetStringi(GL_EXTENSIONS, (GLuint)i);
        if (!ext) continue;
        int k = 0;
        while (name[k] && (GLubyte)name[k] == ext[k]) k++;
        if (!name[k] && !ext[k]) return 1;
    }
    return 0;
}

GLuint mara_gl_compile_shader(GLenum type, const char *src) {
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

GLuint mara_gl_link_program(GLuint vs, GLuint fs) {
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
