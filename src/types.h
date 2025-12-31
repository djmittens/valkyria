#pragma once

#include <stddef.h>
#include <stdint.h>
_Static_assert(sizeof(size_t) == 8, "This codebase supports 64-bit systems only");

// Portable fixed-width types with consistent format specifiers

typedef unsigned long long u64;
typedef signed long long   i64;
typedef unsigned int       u32;
typedef signed int         i32;
typedef unsigned short     u16;
typedef signed short       i16;
typedef unsigned char      u8;
typedef signed char        i8;

typedef float  f32;
typedef double f64;

typedef uintptr_t uptr;
typedef intptr_t  iptr;

typedef size_t sz;

// Format specifier reminders:
// u64/i64: %llu / %lld
// u32/i32: %u / %d
// u16/i16: %hu / %hd
// u8/i8:   %hhu / %hhd
// f32/f64: %f / %lf (or %g / %lg)
// sz:      %zu
