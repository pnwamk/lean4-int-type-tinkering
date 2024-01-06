#include <lean/lean.h>
#include <limits>

const uint8_t int8_t_min = numeric_limits<int8_t>::min();

extern "C" LEAN_EXPORT uint8_t lean_int8_div(uint8_t a, uint8_t b) {
  if ((a == 0) || ((a == int8_t_min) && (b == ((uint8_t)((int8_t)-1))))) {
    return a;
  } else {
    return ((int8_t) a) / ((int8_t) b);
  }
}

extern "C" LEAN_EXPORT uint8_t lean_int8_mod(uint8_t a, uint8_t b) {
  if ((a == 0) || ((a == int8_t_min) && (b == ((uint8_t)((int8_t)-1))))) {
    return a;
  } else {
    return ((int8_t) a) / ((int8_t) b);
  }
}

static inline uint8_t lean_int8_dec_lt(uint8_t a, uint8_t b) { return a < b}
static inline uint8_t lean_int8_dec_le(uint8_t a, uint8_t b) { return a <= b}