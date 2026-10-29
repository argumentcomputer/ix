#ifndef IX_GNARK_H
#define IX_GNARK_H
#include <stddef.h>
#include <stdint.h>
typedef struct { const uint8_t *data; size_t len; } ix_gnark_view;
typedef struct {
 uint8_t *data; size_t len;
 uint8_t *solidity; size_t solidity_len;
 uint8_t *error; size_t error_len;
 uintptr_t handle;
} ix_gnark_result;
typedef struct { uint32_t cuda; int32_t device; uint64_t memory_bytes; uint32_t mask_msm; } ix_gnark_backend;
typedef struct { uint32_t cuda; int32_t device; ix_gnark_view library; } ix_gnark_groth16_backend;
#endif
