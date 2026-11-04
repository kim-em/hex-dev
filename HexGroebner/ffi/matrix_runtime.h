/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifndef HEX_GROEBNER_MATRIX_RUNTIME_H
#define HEX_GROEBNER_MATRIX_RUNTIME_H
#include <lean/lean.h>
#include <stdint.h>

extern lean_obj_res lean_hex_scan_transition(uint64_t,b_lean_obj_arg,b_lean_obj_arg,
    lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,uint8_t);
extern lean_obj_res lean_hex_dense_transition(uint64_t,b_lean_obj_arg,b_lean_obj_arg,
    b_lean_obj_arg,lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,uint8_t);
extern lean_obj_res lean_hex_prepare_dense(uint64_t,b_lean_obj_arg,b_lean_obj_arg,
    b_lean_obj_arg,b_lean_obj_arg);
extern lean_obj_res lean_hex_gather(uint64_t,lean_obj_arg,b_lean_obj_arg,
    b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,uint64_t);
extern lean_obj_res lean_hex_matrix_validate(uint64_t,b_lean_obj_arg,
    b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg,b_lean_obj_arg);
extern lean_obj_res lean_hex_matrix_zeros(b_lean_obj_arg);
#endif
