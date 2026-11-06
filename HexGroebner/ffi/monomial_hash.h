/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
#ifndef HEX_GROEBNER_MONOMIAL_HASH_H
#define HEX_GROEBNER_MONOMIAL_HASH_H
#include <stdint.h>
/* Additive semantic hashes use deterministic SplitMix64 coordinate weights.
   This native table only avoids recomputing the first 64 pure weights. Exact
   exponent comparison, never hash equality, establishes monomial equality. */
static inline uint64_t monomial_weight(uint64_t index) {
    static const uint64_t first[64]={
        UINT64_C(0x2cb0f69f4abea221),UINT64_C(0x9417034723148989),UINT64_C(0xdd555950609dfe03),UINT64_C(0xdbafb150deb12800),
        UINT64_C(0x7e789b2e6c442cb6),UINT64_C(0xf41e5636c7e4f8c4),UINT64_C(0x0959d150f8fba7e4),UINT64_C(0xa97316f13cdb9eea),
        UINT64_C(0x74cd8258f9520068),UINT64_C(0x55c74a62e116868b),UINT64_C(0xd2f4c799a2023cbd),UINT64_C(0xdf98cb79a37b51b9),
        UINT64_C(0x396f5885524f3905),UINT64_C(0xaf1d56386ca3b276),UINT64_C(0xa9ffbe6b5104e85a),UINT64_C(0x6bd0c51b9fd533b3),
        UINT64_C(0x980ce91c50ab4b56),UINT64_C(0x28ac395780fe62c5),UINT64_C(0x768912e3a6bcedc7),UINT64_C(0x50b3e8c9332c7c88),
        UINT64_C(0xce3bbfe520bd47da),UINT64_C(0xcba6c8e8e0bb7c4f),UINT64_C(0xbf194db8434a346d),UINT64_C(0x7d8f2a7b60416d7f),
        UINT64_C(0x0849d1f6e0e10a5e),UINT64_C(0x7654b590d064e22f),UINT64_C(0x16d1da9507df3af2),UINT64_C(0xf63aef1089ea30e4),
        UINT64_C(0x9ade6673cc6c522b),UINT64_C(0x4c75bc274e37087c),UINT64_C(0xd35e12b49f51f27b),UINT64_C(0x22ddf2ffcee481ea),
        UINT64_C(0x06007fb13c59a1f1),UINT64_C(0x8966a38c651ea4da),UINT64_C(0x25242f018fc01ac6),UINT64_C(0xa73ec74fa31b717c),
        UINT64_C(0x7ee0abdd9797d3a2),UINT64_C(0x5c06ff7dc4ac1880),UINT64_C(0x8434e41042c28a7d),UINT64_C(0x770a372d64327351),
        UINT64_C(0xeed940dad9e9c06d),UINT64_C(0x8977e93646524825),UINT64_C(0xa9897f0a62a51616),UINT64_C(0xa35d4250c53f2b3a),
        UINT64_C(0x4072542a94b9c33e),UINT64_C(0x3154a7a62447e8ab),UINT64_C(0x686865712a1a245e),UINT64_C(0x0fba67727d7b3b98),
        UINT64_C(0x0634e2024536912f),UINT64_C(0xd9ff52a26cf9881a),UINT64_C(0x9435dc0399f932da),UINT64_C(0x18d39fc1af93e7f0),
        UINT64_C(0x12f7147c1e7f46ab),UINT64_C(0xdedf66783eddb4a0),UINT64_C(0x6f75480614554798),UINT64_C(0xe40e95e8ef84bde2),
        UINT64_C(0xbb41fe601fefb566),UINT64_C(0x5c3702e4c7bf19f1),UINT64_C(0x8c7d1d0d3d4a8ec5),UINT64_C(0xee779996ba62dccb),
        UINT64_C(0x80ccb15bf530844b),UINT64_C(0xdf56e7dc4d57959c),UINT64_C(0x9eb86a81fe90b68e),UINT64_C(0x6a25741fa696fbd3),
    };
    if(index<64) return first[index];
    uint64_t z=UINT64_C(0x243f6a8885a308d3)+(index+1)*UINT64_C(0x9e3779b97f4a7c15);
    z=(z^(z>>30))*UINT64_C(0xbf58476d1ce4e5b9);
    z=(z^(z>>27))*UINT64_C(0x94d049bb133111eb);
    return z^(z>>31);
}
#endif
