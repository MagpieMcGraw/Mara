// The release workflow's check of a Mara library (tlib.mara) called from
// four threads at once, each with an arena of its own: every call's result
// must be right. An Arena_Basic here is as mara.memory lays it out.
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct { long long len, cap; unsigned char* ptr; long long capacity, current_mark; } Arena_Basic;
long long tlib_fill_sum(Arena_Basic* a, long long n);

static int wrong[4];

static void* work(void* mine) {
    Arena_Basic a = {0, 1 << 20, malloc(1 << 20), 1 << 20, -1};
    for (int i = 0; i < 20000; i++) {
        long long n = 3000 + (i % 1000);
        if (tlib_fill_sum(&a, n) != n * (n - 1) / 2 + n) *(int*)mine += 1;
    }
    return NULL;
}

int main(void) {
    pthread_t t[4];
    for (int i = 0; i < 4; i++) pthread_create(&t[i], NULL, work, &wrong[i]);
    int total = 0;
    for (int i = 0; i < 4; i++) { pthread_join(t[i], NULL); total += wrong[i]; }
    printf("wrong results: %d\n", total);
    return total != 0;
}
