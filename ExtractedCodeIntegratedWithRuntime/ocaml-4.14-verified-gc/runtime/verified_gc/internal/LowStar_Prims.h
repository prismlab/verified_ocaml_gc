#ifndef __internal_LowStar_Prims_H
#define __internal_LowStar_Prims_H

#include "alias.h"
#include <stdint.h>

extern krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x,
                                               krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Addition(krml_checked_int_t x,
                                            krml_checked_int_t y);

extern bool Prims_op_GreaterThan(krml_checked_int_t x0, krml_checked_int_t x1);

extern bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x0,
                                        krml_checked_int_t x1);

#define __internal_LowStar_Prims_H_DEFINED
#endif
