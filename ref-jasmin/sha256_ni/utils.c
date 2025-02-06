#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

__m128i u128_from_two_u64(uint64_t hi, uint64_t lo) { return _mm_set_epi64x(hi, lo); }