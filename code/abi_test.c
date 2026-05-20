#include <stdint.h>

// Test fixture for Mara's .C calling convention codegen.
// Exercises three lowering shapes:
//   - primitive scalar (int → register)
//   - small struct (Color is 4 bytes → Direct as i32 on Win64 and SysV)
//   - 12-byte struct (Vec3 → Indirect on Win64; Direct {<2 x float>, float}
//     across two XMMs on SysV)
//
// Each function does a trivial transform so Mara can verify the round-trip.

typedef struct { float x, y, z; } AbiVec3;
typedef struct { unsigned char r, g, b, a; } AbiColor;

int abi_test_int(int x) {
    return x * 2;
}

AbiColor abi_test_color(AbiColor c) {
    AbiColor out;
    out.r = (unsigned char)(c.r + 1);
    out.g = (unsigned char)(c.g + 1);
    out.b = (unsigned char)(c.b + 1);
    out.a = (unsigned char)(c.a + 1);
    return out;
}

AbiVec3 abi_test_vec3(AbiVec3 v) {
    AbiVec3 out;
    out.x = v.x * 2.0f;
    out.y = v.y * 2.0f;
    out.z = v.z * 2.0f;
    return out;
}
