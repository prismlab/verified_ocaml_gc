#ifndef __internal_FStar_H
#define __internal_FStar_H

#include "alias.h"
#include <stdint.h>

// NOTE: This is handwrittten as well. Defined this macros to be
// no-op(handwritten again), in the LowStar code, there's a lot of back and
// forth from these integer types. However, we don't want it for 64 bit
// architectures, we want everything to be 64 bit. Hence we do this.

#define FStar_UInt32_v(x) x

#define FStar_UInt32_uint_to_t(x) x

#define FStar_UInt64_v(x) x

#define FStar_UInt64_uint_to_t(x) x

#define __internal_FStar_H_DEFINED
#endif
