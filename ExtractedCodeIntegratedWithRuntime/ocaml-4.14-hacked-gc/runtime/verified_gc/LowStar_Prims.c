#include "internal/LowStar_Prims.h"

// NOTE: Handwritten
// TODO: Not doing any checked arithmetics
extern krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x,
                                               krml_checked_int_t y) {
  return x - y;
}

extern krml_checked_int_t Prims_op_Addition(krml_checked_int_t x,
                                            krml_checked_int_t y) {
  return x + y;
}

extern bool Prims_op_GreaterThan(krml_checked_int_t x0, krml_checked_int_t x1) {
  return x0 > x1;
}

extern bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x0,
                                        krml_checked_int_t x1) {
  return x0 >= x1;
}
