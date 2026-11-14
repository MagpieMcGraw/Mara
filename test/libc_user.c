// A C function that calls the C library: no_crt_c_neg's.
extern int printf(const char *format, ...);

int libc_user(int x) {
    printf("%d\n", x);
    return x;
}
