.arch armv8.5-a+sve2
.text
.global k_neon_full
.type k_neon_full, %function
.p2align 6
k_neon_full:
  stp d8, d9, [sp, #-64]!
  stp d10, d11, [sp, #16]
  stp d12, d13, [sp, #32]
  stp d14, d15, [sp, #48]
  mov x1, x0
1:
  add v0.4s, v0.4s, v1.4s
  add w2, w2, w6
  add v4.4s, v4.4s, v5.4s
  add w3, w3, w7
  add v16.4s, v16.4s, v17.4s
  add w4, w4, w8
  add v20.4s, v20.4s, v21.4s
  add w5, w5, w9
  add v24.4s, v24.4s, v25.4s
  eor w14, w14, w2
  ror w14, w14, #16
  add v28.4s, v28.4s, v29.4s
  eor w15, w15, w3
  ror w15, w15, #16
  eor v31.16b, v3.16b, v0.16b
  rev32 v3.8h, v31.8h
  eor w16, w16, w4
  ror w16, w16, #16
  eor v31.16b, v7.16b, v4.16b
  rev32 v7.8h, v31.8h
  eor w17, w17, w5
  ror w17, w17, #16
  eor v31.16b, v19.16b, v16.16b
  rev32 v19.8h, v31.8h
  add w10, w10, w14
  eor v31.16b, v23.16b, v20.16b
  rev32 v23.8h, v31.8h
  add w11, w11, w15
  eor v31.16b, v27.16b, v24.16b
  rev32 v27.8h, v31.8h
  add w12, w12, w16
  eor v31.16b, v9.16b, v28.16b
  rev32 v9.8h, v31.8h
  add w13, w13, w17
  add v2.4s, v2.4s, v3.4s
  eor w6, w6, w10
  ror w6, w6, #20
  add v6.4s, v6.4s, v7.4s
  eor w7, w7, w11
  ror w7, w7, #20
  add v18.4s, v18.4s, v19.4s
  eor w8, w8, w12
  ror w8, w8, #20
  add v22.4s, v22.4s, v23.4s
  eor w9, w9, w13
  ror w9, w9, #20
  add v26.4s, v26.4s, v27.4s
  add w2, w2, w6
  add v8.4s, v8.4s, v9.4s
  add w3, w3, w7
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #20
  sli v1.4s, v31.4s, #12
  add w4, w4, w8
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #20
  sli v5.4s, v31.4s, #12
  add w5, w5, w9
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #20
  sli v17.4s, v31.4s, #12
  eor w14, w14, w2
  ror w14, w14, #24
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #20
  sli v21.4s, v31.4s, #12
  eor w15, w15, w3
  ror w15, w15, #24
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #20
  sli v25.4s, v31.4s, #12
  eor w16, w16, w4
  ror w16, w16, #24
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #20
  sli v29.4s, v31.4s, #12
  eor w17, w17, w5
  ror w17, w17, #24
  add v0.4s, v0.4s, v1.4s
  add w10, w10, w14
  add v4.4s, v4.4s, v5.4s
  add w11, w11, w15
  add v16.4s, v16.4s, v17.4s
  add w12, w12, w16
  add v20.4s, v20.4s, v21.4s
  add w13, w13, w17
  add v24.4s, v24.4s, v25.4s
  eor w6, w6, w10
  ror w6, w6, #25
  add v28.4s, v28.4s, v29.4s
  eor w7, w7, w11
  ror w7, w7, #25
  eor v31.16b, v3.16b, v0.16b
  tbl v3.16b, {v31.16b}, v30.16b
  eor w8, w8, w12
  ror w8, w8, #25
  eor v31.16b, v7.16b, v4.16b
  tbl v7.16b, {v31.16b}, v30.16b
  eor w9, w9, w13
  ror w9, w9, #25
  eor v31.16b, v19.16b, v16.16b
  tbl v19.16b, {v31.16b}, v30.16b
  add w2, w2, w7
  eor v31.16b, v23.16b, v20.16b
  tbl v23.16b, {v31.16b}, v30.16b
  add w3, w3, w8
  eor v31.16b, v27.16b, v24.16b
  tbl v27.16b, {v31.16b}, v30.16b
  add w4, w4, w9
  eor v31.16b, v9.16b, v28.16b
  tbl v9.16b, {v31.16b}, v30.16b
  add w5, w5, w6
  add v2.4s, v2.4s, v3.4s
  eor w17, w17, w2
  ror w17, w17, #16
  add v6.4s, v6.4s, v7.4s
  eor w14, w14, w3
  ror w14, w14, #16
  add v18.4s, v18.4s, v19.4s
  eor w15, w15, w4
  ror w15, w15, #16
  add v22.4s, v22.4s, v23.4s
  eor w16, w16, w5
  ror w16, w16, #16
  add v26.4s, v26.4s, v27.4s
  add w12, w12, w17
  add v8.4s, v8.4s, v9.4s
  add w13, w13, w14
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #25
  sli v1.4s, v31.4s, #7
  add w10, w10, w15
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #25
  sli v5.4s, v31.4s, #7
  add w11, w11, w16
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #25
  sli v17.4s, v31.4s, #7
  eor w7, w7, w12
  ror w7, w7, #20
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #25
  sli v21.4s, v31.4s, #7
  eor w8, w8, w13
  ror w8, w8, #20
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #25
  sli v25.4s, v31.4s, #7
  eor w9, w9, w10
  ror w9, w9, #20
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #25
  sli v29.4s, v31.4s, #7
  eor w6, w6, w11
  ror w6, w6, #20
  ext v1.16b, v1.16b, v1.16b, #4
  add w2, w2, w7
  ext v5.16b, v5.16b, v5.16b, #4
  add w3, w3, w8
  ext v17.16b, v17.16b, v17.16b, #4
  add w4, w4, w9
  ext v21.16b, v21.16b, v21.16b, #4
  add w5, w5, w6
  ext v25.16b, v25.16b, v25.16b, #4
  eor w17, w17, w2
  ror w17, w17, #24
  ext v29.16b, v29.16b, v29.16b, #4
  eor w14, w14, w3
  ror w14, w14, #24
  ext v2.16b, v2.16b, v2.16b, #8
  eor w15, w15, w4
  ror w15, w15, #24
  ext v6.16b, v6.16b, v6.16b, #8
  eor w16, w16, w5
  ror w16, w16, #24
  ext v18.16b, v18.16b, v18.16b, #8
  add w12, w12, w17
  ext v22.16b, v22.16b, v22.16b, #8
  add w13, w13, w14
  ext v26.16b, v26.16b, v26.16b, #8
  add w10, w10, w15
  ext v8.16b, v8.16b, v8.16b, #8
  add w11, w11, w16
  ext v3.16b, v3.16b, v3.16b, #12
  eor w7, w7, w12
  ror w7, w7, #25
  ext v7.16b, v7.16b, v7.16b, #12
  eor w8, w8, w13
  ror w8, w8, #25
  ext v19.16b, v19.16b, v19.16b, #12
  eor w9, w9, w10
  ror w9, w9, #25
  ext v23.16b, v23.16b, v23.16b, #12
  eor w6, w6, w11
  ror w6, w6, #25
  ext v27.16b, v27.16b, v27.16b, #12
  add w2, w2, w6
  ext v9.16b, v9.16b, v9.16b, #12
  add w3, w3, w7
  add v0.4s, v0.4s, v1.4s
  add w4, w4, w8
  add v4.4s, v4.4s, v5.4s
  add w5, w5, w9
  add v16.4s, v16.4s, v17.4s
  eor w14, w14, w2
  ror w14, w14, #16
  add v20.4s, v20.4s, v21.4s
  eor w15, w15, w3
  ror w15, w15, #16
  add v24.4s, v24.4s, v25.4s
  eor w16, w16, w4
  ror w16, w16, #16
  add v28.4s, v28.4s, v29.4s
  eor w17, w17, w5
  ror w17, w17, #16
  eor v31.16b, v3.16b, v0.16b
  rev32 v3.8h, v31.8h
  add w10, w10, w14
  eor v31.16b, v7.16b, v4.16b
  rev32 v7.8h, v31.8h
  add w11, w11, w15
  eor v31.16b, v19.16b, v16.16b
  rev32 v19.8h, v31.8h
  add w12, w12, w16
  eor v31.16b, v23.16b, v20.16b
  rev32 v23.8h, v31.8h
  add w13, w13, w17
  eor v31.16b, v27.16b, v24.16b
  rev32 v27.8h, v31.8h
  eor w6, w6, w10
  ror w6, w6, #20
  eor v31.16b, v9.16b, v28.16b
  rev32 v9.8h, v31.8h
  eor w7, w7, w11
  ror w7, w7, #20
  add v2.4s, v2.4s, v3.4s
  eor w8, w8, w12
  ror w8, w8, #20
  add v6.4s, v6.4s, v7.4s
  eor w9, w9, w13
  ror w9, w9, #20
  add v18.4s, v18.4s, v19.4s
  add w2, w2, w6
  add v22.4s, v22.4s, v23.4s
  add w3, w3, w7
  add v26.4s, v26.4s, v27.4s
  add w4, w4, w8
  add v8.4s, v8.4s, v9.4s
  add w5, w5, w9
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #20
  sli v1.4s, v31.4s, #12
  eor w14, w14, w2
  ror w14, w14, #24
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #20
  sli v5.4s, v31.4s, #12
  eor w15, w15, w3
  ror w15, w15, #24
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #20
  sli v17.4s, v31.4s, #12
  eor w16, w16, w4
  ror w16, w16, #24
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #20
  sli v21.4s, v31.4s, #12
  eor w17, w17, w5
  ror w17, w17, #24
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #20
  sli v25.4s, v31.4s, #12
  add w10, w10, w14
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #20
  sli v29.4s, v31.4s, #12
  add w11, w11, w15
  add v0.4s, v0.4s, v1.4s
  add w12, w12, w16
  add v4.4s, v4.4s, v5.4s
  add w13, w13, w17
  add v16.4s, v16.4s, v17.4s
  eor w6, w6, w10
  ror w6, w6, #25
  add v20.4s, v20.4s, v21.4s
  eor w7, w7, w11
  ror w7, w7, #25
  add v24.4s, v24.4s, v25.4s
  eor w8, w8, w12
  ror w8, w8, #25
  add v28.4s, v28.4s, v29.4s
  eor w9, w9, w13
  ror w9, w9, #25
  eor v31.16b, v3.16b, v0.16b
  tbl v3.16b, {v31.16b}, v30.16b
  add w2, w2, w7
  eor v31.16b, v7.16b, v4.16b
  tbl v7.16b, {v31.16b}, v30.16b
  add w3, w3, w8
  eor v31.16b, v19.16b, v16.16b
  tbl v19.16b, {v31.16b}, v30.16b
  add w4, w4, w9
  eor v31.16b, v23.16b, v20.16b
  tbl v23.16b, {v31.16b}, v30.16b
  add w5, w5, w6
  eor v31.16b, v27.16b, v24.16b
  tbl v27.16b, {v31.16b}, v30.16b
  eor w17, w17, w2
  ror w17, w17, #16
  eor v31.16b, v9.16b, v28.16b
  tbl v9.16b, {v31.16b}, v30.16b
  eor w14, w14, w3
  ror w14, w14, #16
  add v2.4s, v2.4s, v3.4s
  eor w15, w15, w4
  ror w15, w15, #16
  add v6.4s, v6.4s, v7.4s
  eor w16, w16, w5
  ror w16, w16, #16
  add v18.4s, v18.4s, v19.4s
  add w12, w12, w17
  add v22.4s, v22.4s, v23.4s
  add w13, w13, w14
  add v26.4s, v26.4s, v27.4s
  add w10, w10, w15
  add v8.4s, v8.4s, v9.4s
  add w11, w11, w16
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #25
  sli v1.4s, v31.4s, #7
  eor w7, w7, w12
  ror w7, w7, #20
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #25
  sli v5.4s, v31.4s, #7
  eor w8, w8, w13
  ror w8, w8, #20
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #25
  sli v17.4s, v31.4s, #7
  eor w9, w9, w10
  ror w9, w9, #20
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #25
  sli v21.4s, v31.4s, #7
  eor w6, w6, w11
  ror w6, w6, #20
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #25
  sli v25.4s, v31.4s, #7
  add w2, w2, w7
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #25
  sli v29.4s, v31.4s, #7
  add w3, w3, w8
  ext v1.16b, v1.16b, v1.16b, #12
  add w4, w4, w9
  ext v5.16b, v5.16b, v5.16b, #12
  add w5, w5, w6
  ext v17.16b, v17.16b, v17.16b, #12
  eor w17, w17, w2
  ror w17, w17, #24
  ext v21.16b, v21.16b, v21.16b, #12
  eor w14, w14, w3
  ror w14, w14, #24
  ext v25.16b, v25.16b, v25.16b, #12
  eor w15, w15, w4
  ror w15, w15, #24
  ext v29.16b, v29.16b, v29.16b, #12
  eor w16, w16, w5
  ror w16, w16, #24
  ext v2.16b, v2.16b, v2.16b, #8
  add w12, w12, w17
  ext v6.16b, v6.16b, v6.16b, #8
  add w13, w13, w14
  ext v18.16b, v18.16b, v18.16b, #8
  add w10, w10, w15
  ext v22.16b, v22.16b, v22.16b, #8
  add w11, w11, w16
  ext v26.16b, v26.16b, v26.16b, #8
  eor w7, w7, w12
  ror w7, w7, #25
  ext v8.16b, v8.16b, v8.16b, #8
  eor w8, w8, w13
  ror w8, w8, #25
  ext v3.16b, v3.16b, v3.16b, #4
  eor w9, w9, w10
  ror w9, w9, #25
  ext v7.16b, v7.16b, v7.16b, #4
  eor w6, w6, w11
  ror w6, w6, #25
  ext v19.16b, v19.16b, v19.16b, #4
  ext v23.16b, v23.16b, v23.16b, #4
  ext v27.16b, v27.16b, v27.16b, #4
  ext v9.16b, v9.16b, v9.16b, #4
  sub x1, x1, #1
  cbnz x1, 1b
  ldp d10, d11, [sp, #16]
  ldp d12, d13, [sp, #32]
  ldp d14, d15, [sp, #48]
  ldp d8, d9, [sp], #64
  ret
.global k_sve_full
.type k_sve_full, %function
.p2align 6
k_sve_full:
  stp d8, d9, [sp, #-64]!
  stp d10, d11, [sp, #16]
  stp d12, d13, [sp, #32]
  stp d14, d15, [sp, #48]
  mov x1, x0
1:
  add v0.4s, v0.4s, v1.4s
  add w2, w2, w6
  add v4.4s, v4.4s, v5.4s
  add w3, w3, w7
  add v16.4s, v16.4s, v17.4s
  add w4, w4, w8
  add v20.4s, v20.4s, v21.4s
  add w5, w5, w9
  add v24.4s, v24.4s, v25.4s
  eor w14, w14, w2
  ror w14, w14, #16
  add v28.4s, v28.4s, v29.4s
  eor w15, w15, w3
  ror w15, w15, #16
  xar z3.s, z3.s, z0.s, #16
  eor w16, w16, w4
  ror w16, w16, #16
  xar z7.s, z7.s, z4.s, #16
  eor w17, w17, w5
  ror w17, w17, #16
  xar z19.s, z19.s, z16.s, #16
  add w10, w10, w14
  xar z23.s, z23.s, z20.s, #16
  add w11, w11, w15
  xar z27.s, z27.s, z24.s, #16
  add w12, w12, w16
  xar z9.s, z9.s, z28.s, #16
  add w13, w13, w17
  add v2.4s, v2.4s, v3.4s
  eor w6, w6, w10
  ror w6, w6, #20
  add v6.4s, v6.4s, v7.4s
  eor w7, w7, w11
  ror w7, w7, #20
  add v18.4s, v18.4s, v19.4s
  eor w8, w8, w12
  ror w8, w8, #20
  add v22.4s, v22.4s, v23.4s
  eor w9, w9, w13
  ror w9, w9, #20
  add v26.4s, v26.4s, v27.4s
  add w2, w2, w6
  add v8.4s, v8.4s, v9.4s
  add w3, w3, w7
  xar z1.s, z1.s, z2.s, #20
  add w4, w4, w8
  xar z5.s, z5.s, z6.s, #20
  add w5, w5, w9
  xar z17.s, z17.s, z18.s, #20
  eor w14, w14, w2
  ror w14, w14, #24
  xar z21.s, z21.s, z22.s, #20
  eor w15, w15, w3
  ror w15, w15, #24
  xar z25.s, z25.s, z26.s, #20
  eor w16, w16, w4
  ror w16, w16, #24
  xar z29.s, z29.s, z8.s, #20
  eor w17, w17, w5
  ror w17, w17, #24
  add v0.4s, v0.4s, v1.4s
  add w10, w10, w14
  add v4.4s, v4.4s, v5.4s
  add w11, w11, w15
  add v16.4s, v16.4s, v17.4s
  add w12, w12, w16
  add v20.4s, v20.4s, v21.4s
  add w13, w13, w17
  add v24.4s, v24.4s, v25.4s
  eor w6, w6, w10
  ror w6, w6, #25
  add v28.4s, v28.4s, v29.4s
  eor w7, w7, w11
  ror w7, w7, #25
  tbl v3.16b, {v31.16b}, v30.16b
  eor w8, w8, w12
  ror w8, w8, #25
  tbl v7.16b, {v31.16b}, v30.16b
  eor w9, w9, w13
  ror w9, w9, #25
  tbl v19.16b, {v31.16b}, v30.16b
  add w2, w2, w7
  tbl v23.16b, {v31.16b}, v30.16b
  add w3, w3, w8
  tbl v27.16b, {v31.16b}, v30.16b
  add w4, w4, w9
  tbl v9.16b, {v31.16b}, v30.16b
  add w5, w5, w6
  add v2.4s, v2.4s, v3.4s
  eor w17, w17, w2
  ror w17, w17, #16
  add v6.4s, v6.4s, v7.4s
  eor w14, w14, w3
  ror w14, w14, #16
  add v18.4s, v18.4s, v19.4s
  eor w15, w15, w4
  ror w15, w15, #16
  add v22.4s, v22.4s, v23.4s
  eor w16, w16, w5
  ror w16, w16, #16
  add v26.4s, v26.4s, v27.4s
  add w12, w12, w17
  add v8.4s, v8.4s, v9.4s
  add w13, w13, w14
  xar z1.s, z1.s, z2.s, #25
  add w10, w10, w15
  xar z5.s, z5.s, z6.s, #25
  add w11, w11, w16
  xar z17.s, z17.s, z18.s, #25
  eor w7, w7, w12
  ror w7, w7, #20
  xar z21.s, z21.s, z22.s, #25
  eor w8, w8, w13
  ror w8, w8, #20
  xar z25.s, z25.s, z26.s, #25
  eor w9, w9, w10
  ror w9, w9, #20
  xar z29.s, z29.s, z8.s, #25
  eor w6, w6, w11
  ror w6, w6, #20
  ext v1.16b, v1.16b, v1.16b, #4
  add w2, w2, w7
  ext v5.16b, v5.16b, v5.16b, #4
  add w3, w3, w8
  ext v17.16b, v17.16b, v17.16b, #4
  add w4, w4, w9
  ext v21.16b, v21.16b, v21.16b, #4
  add w5, w5, w6
  ext v25.16b, v25.16b, v25.16b, #4
  eor w17, w17, w2
  ror w17, w17, #24
  ext v29.16b, v29.16b, v29.16b, #4
  eor w14, w14, w3
  ror w14, w14, #24
  ext v2.16b, v2.16b, v2.16b, #8
  eor w15, w15, w4
  ror w15, w15, #24
  ext v6.16b, v6.16b, v6.16b, #8
  eor w16, w16, w5
  ror w16, w16, #24
  ext v18.16b, v18.16b, v18.16b, #8
  add w12, w12, w17
  ext v22.16b, v22.16b, v22.16b, #8
  add w13, w13, w14
  ext v26.16b, v26.16b, v26.16b, #8
  add w10, w10, w15
  ext v8.16b, v8.16b, v8.16b, #8
  add w11, w11, w16
  ext v3.16b, v3.16b, v3.16b, #12
  eor w7, w7, w12
  ror w7, w7, #25
  ext v7.16b, v7.16b, v7.16b, #12
  eor w8, w8, w13
  ror w8, w8, #25
  ext v19.16b, v19.16b, v19.16b, #12
  eor w9, w9, w10
  ror w9, w9, #25
  ext v23.16b, v23.16b, v23.16b, #12
  eor w6, w6, w11
  ror w6, w6, #25
  ext v27.16b, v27.16b, v27.16b, #12
  add w2, w2, w6
  ext v9.16b, v9.16b, v9.16b, #12
  add w3, w3, w7
  add v0.4s, v0.4s, v1.4s
  add w4, w4, w8
  add v4.4s, v4.4s, v5.4s
  add w5, w5, w9
  add v16.4s, v16.4s, v17.4s
  eor w14, w14, w2
  ror w14, w14, #16
  add v20.4s, v20.4s, v21.4s
  eor w15, w15, w3
  ror w15, w15, #16
  add v24.4s, v24.4s, v25.4s
  eor w16, w16, w4
  ror w16, w16, #16
  add v28.4s, v28.4s, v29.4s
  eor w17, w17, w5
  ror w17, w17, #16
  xar z3.s, z3.s, z0.s, #16
  add w10, w10, w14
  xar z7.s, z7.s, z4.s, #16
  add w11, w11, w15
  xar z19.s, z19.s, z16.s, #16
  add w12, w12, w16
  xar z23.s, z23.s, z20.s, #16
  add w13, w13, w17
  xar z27.s, z27.s, z24.s, #16
  eor w6, w6, w10
  ror w6, w6, #20
  xar z9.s, z9.s, z28.s, #16
  eor w7, w7, w11
  ror w7, w7, #20
  add v2.4s, v2.4s, v3.4s
  eor w8, w8, w12
  ror w8, w8, #20
  add v6.4s, v6.4s, v7.4s
  eor w9, w9, w13
  ror w9, w9, #20
  add v18.4s, v18.4s, v19.4s
  add w2, w2, w6
  add v22.4s, v22.4s, v23.4s
  add w3, w3, w7
  add v26.4s, v26.4s, v27.4s
  add w4, w4, w8
  add v8.4s, v8.4s, v9.4s
  add w5, w5, w9
  xar z1.s, z1.s, z2.s, #20
  eor w14, w14, w2
  ror w14, w14, #24
  xar z5.s, z5.s, z6.s, #20
  eor w15, w15, w3
  ror w15, w15, #24
  xar z17.s, z17.s, z18.s, #20
  eor w16, w16, w4
  ror w16, w16, #24
  xar z21.s, z21.s, z22.s, #20
  eor w17, w17, w5
  ror w17, w17, #24
  xar z25.s, z25.s, z26.s, #20
  add w10, w10, w14
  xar z29.s, z29.s, z8.s, #20
  add w11, w11, w15
  add v0.4s, v0.4s, v1.4s
  add w12, w12, w16
  add v4.4s, v4.4s, v5.4s
  add w13, w13, w17
  add v16.4s, v16.4s, v17.4s
  eor w6, w6, w10
  ror w6, w6, #25
  add v20.4s, v20.4s, v21.4s
  eor w7, w7, w11
  ror w7, w7, #25
  add v24.4s, v24.4s, v25.4s
  eor w8, w8, w12
  ror w8, w8, #25
  add v28.4s, v28.4s, v29.4s
  eor w9, w9, w13
  ror w9, w9, #25
  tbl v3.16b, {v31.16b}, v30.16b
  add w2, w2, w7
  tbl v7.16b, {v31.16b}, v30.16b
  add w3, w3, w8
  tbl v19.16b, {v31.16b}, v30.16b
  add w4, w4, w9
  tbl v23.16b, {v31.16b}, v30.16b
  add w5, w5, w6
  tbl v27.16b, {v31.16b}, v30.16b
  eor w17, w17, w2
  ror w17, w17, #16
  tbl v9.16b, {v31.16b}, v30.16b
  eor w14, w14, w3
  ror w14, w14, #16
  add v2.4s, v2.4s, v3.4s
  eor w15, w15, w4
  ror w15, w15, #16
  add v6.4s, v6.4s, v7.4s
  eor w16, w16, w5
  ror w16, w16, #16
  add v18.4s, v18.4s, v19.4s
  add w12, w12, w17
  add v22.4s, v22.4s, v23.4s
  add w13, w13, w14
  add v26.4s, v26.4s, v27.4s
  add w10, w10, w15
  add v8.4s, v8.4s, v9.4s
  add w11, w11, w16
  xar z1.s, z1.s, z2.s, #25
  eor w7, w7, w12
  ror w7, w7, #20
  xar z5.s, z5.s, z6.s, #25
  eor w8, w8, w13
  ror w8, w8, #20
  xar z17.s, z17.s, z18.s, #25
  eor w9, w9, w10
  ror w9, w9, #20
  xar z21.s, z21.s, z22.s, #25
  eor w6, w6, w11
  ror w6, w6, #20
  xar z25.s, z25.s, z26.s, #25
  add w2, w2, w7
  xar z29.s, z29.s, z8.s, #25
  add w3, w3, w8
  ext v1.16b, v1.16b, v1.16b, #12
  add w4, w4, w9
  ext v5.16b, v5.16b, v5.16b, #12
  add w5, w5, w6
  ext v17.16b, v17.16b, v17.16b, #12
  eor w17, w17, w2
  ror w17, w17, #24
  ext v21.16b, v21.16b, v21.16b, #12
  eor w14, w14, w3
  ror w14, w14, #24
  ext v25.16b, v25.16b, v25.16b, #12
  eor w15, w15, w4
  ror w15, w15, #24
  ext v29.16b, v29.16b, v29.16b, #12
  eor w16, w16, w5
  ror w16, w16, #24
  ext v2.16b, v2.16b, v2.16b, #8
  add w12, w12, w17
  ext v6.16b, v6.16b, v6.16b, #8
  add w13, w13, w14
  ext v18.16b, v18.16b, v18.16b, #8
  add w10, w10, w15
  ext v22.16b, v22.16b, v22.16b, #8
  add w11, w11, w16
  ext v26.16b, v26.16b, v26.16b, #8
  eor w7, w7, w12
  ror w7, w7, #25
  ext v8.16b, v8.16b, v8.16b, #8
  eor w8, w8, w13
  ror w8, w8, #25
  ext v3.16b, v3.16b, v3.16b, #4
  eor w9, w9, w10
  ror w9, w9, #25
  ext v7.16b, v7.16b, v7.16b, #4
  eor w6, w6, w11
  ror w6, w6, #25
  ext v19.16b, v19.16b, v19.16b, #4
  ext v23.16b, v23.16b, v23.16b, #4
  ext v27.16b, v27.16b, v27.16b, #4
  ext v9.16b, v9.16b, v9.16b, #4
  sub x1, x1, #1
  cbnz x1, 1b
  ldp d10, d11, [sp, #16]
  ldp d12, d13, [sp, #32]
  ldp d14, d15, [sp, #48]
  ldp d8, d9, [sp], #64
  ret
.global k_neon_vec
.type k_neon_vec, %function
.p2align 6
k_neon_vec:
  stp d8, d9, [sp, #-64]!
  stp d10, d11, [sp, #16]
  stp d12, d13, [sp, #32]
  stp d14, d15, [sp, #48]
  mov x1, x0
1:
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  eor v31.16b, v3.16b, v0.16b
  rev32 v3.8h, v31.8h
  eor v31.16b, v7.16b, v4.16b
  rev32 v7.8h, v31.8h
  eor v31.16b, v19.16b, v16.16b
  rev32 v19.8h, v31.8h
  eor v31.16b, v23.16b, v20.16b
  rev32 v23.8h, v31.8h
  eor v31.16b, v27.16b, v24.16b
  rev32 v27.8h, v31.8h
  eor v31.16b, v9.16b, v28.16b
  rev32 v9.8h, v31.8h
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #20
  sli v1.4s, v31.4s, #12
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #20
  sli v5.4s, v31.4s, #12
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #20
  sli v17.4s, v31.4s, #12
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #20
  sli v21.4s, v31.4s, #12
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #20
  sli v25.4s, v31.4s, #12
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #20
  sli v29.4s, v31.4s, #12
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  eor v31.16b, v3.16b, v0.16b
  tbl v3.16b, {v31.16b}, v30.16b
  eor v31.16b, v7.16b, v4.16b
  tbl v7.16b, {v31.16b}, v30.16b
  eor v31.16b, v19.16b, v16.16b
  tbl v19.16b, {v31.16b}, v30.16b
  eor v31.16b, v23.16b, v20.16b
  tbl v23.16b, {v31.16b}, v30.16b
  eor v31.16b, v27.16b, v24.16b
  tbl v27.16b, {v31.16b}, v30.16b
  eor v31.16b, v9.16b, v28.16b
  tbl v9.16b, {v31.16b}, v30.16b
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #25
  sli v1.4s, v31.4s, #7
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #25
  sli v5.4s, v31.4s, #7
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #25
  sli v17.4s, v31.4s, #7
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #25
  sli v21.4s, v31.4s, #7
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #25
  sli v25.4s, v31.4s, #7
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #25
  sli v29.4s, v31.4s, #7
  ext v1.16b, v1.16b, v1.16b, #4
  ext v5.16b, v5.16b, v5.16b, #4
  ext v17.16b, v17.16b, v17.16b, #4
  ext v21.16b, v21.16b, v21.16b, #4
  ext v25.16b, v25.16b, v25.16b, #4
  ext v29.16b, v29.16b, v29.16b, #4
  ext v2.16b, v2.16b, v2.16b, #8
  ext v6.16b, v6.16b, v6.16b, #8
  ext v18.16b, v18.16b, v18.16b, #8
  ext v22.16b, v22.16b, v22.16b, #8
  ext v26.16b, v26.16b, v26.16b, #8
  ext v8.16b, v8.16b, v8.16b, #8
  ext v3.16b, v3.16b, v3.16b, #12
  ext v7.16b, v7.16b, v7.16b, #12
  ext v19.16b, v19.16b, v19.16b, #12
  ext v23.16b, v23.16b, v23.16b, #12
  ext v27.16b, v27.16b, v27.16b, #12
  ext v9.16b, v9.16b, v9.16b, #12
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  eor v31.16b, v3.16b, v0.16b
  rev32 v3.8h, v31.8h
  eor v31.16b, v7.16b, v4.16b
  rev32 v7.8h, v31.8h
  eor v31.16b, v19.16b, v16.16b
  rev32 v19.8h, v31.8h
  eor v31.16b, v23.16b, v20.16b
  rev32 v23.8h, v31.8h
  eor v31.16b, v27.16b, v24.16b
  rev32 v27.8h, v31.8h
  eor v31.16b, v9.16b, v28.16b
  rev32 v9.8h, v31.8h
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #20
  sli v1.4s, v31.4s, #12
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #20
  sli v5.4s, v31.4s, #12
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #20
  sli v17.4s, v31.4s, #12
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #20
  sli v21.4s, v31.4s, #12
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #20
  sli v25.4s, v31.4s, #12
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #20
  sli v29.4s, v31.4s, #12
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  eor v31.16b, v3.16b, v0.16b
  tbl v3.16b, {v31.16b}, v30.16b
  eor v31.16b, v7.16b, v4.16b
  tbl v7.16b, {v31.16b}, v30.16b
  eor v31.16b, v19.16b, v16.16b
  tbl v19.16b, {v31.16b}, v30.16b
  eor v31.16b, v23.16b, v20.16b
  tbl v23.16b, {v31.16b}, v30.16b
  eor v31.16b, v27.16b, v24.16b
  tbl v27.16b, {v31.16b}, v30.16b
  eor v31.16b, v9.16b, v28.16b
  tbl v9.16b, {v31.16b}, v30.16b
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  eor v31.16b, v1.16b, v2.16b
  ushr v1.4s, v31.4s, #25
  sli v1.4s, v31.4s, #7
  eor v31.16b, v5.16b, v6.16b
  ushr v5.4s, v31.4s, #25
  sli v5.4s, v31.4s, #7
  eor v31.16b, v17.16b, v18.16b
  ushr v17.4s, v31.4s, #25
  sli v17.4s, v31.4s, #7
  eor v31.16b, v21.16b, v22.16b
  ushr v21.4s, v31.4s, #25
  sli v21.4s, v31.4s, #7
  eor v31.16b, v25.16b, v26.16b
  ushr v25.4s, v31.4s, #25
  sli v25.4s, v31.4s, #7
  eor v31.16b, v29.16b, v8.16b
  ushr v29.4s, v31.4s, #25
  sli v29.4s, v31.4s, #7
  ext v1.16b, v1.16b, v1.16b, #12
  ext v5.16b, v5.16b, v5.16b, #12
  ext v17.16b, v17.16b, v17.16b, #12
  ext v21.16b, v21.16b, v21.16b, #12
  ext v25.16b, v25.16b, v25.16b, #12
  ext v29.16b, v29.16b, v29.16b, #12
  ext v2.16b, v2.16b, v2.16b, #8
  ext v6.16b, v6.16b, v6.16b, #8
  ext v18.16b, v18.16b, v18.16b, #8
  ext v22.16b, v22.16b, v22.16b, #8
  ext v26.16b, v26.16b, v26.16b, #8
  ext v8.16b, v8.16b, v8.16b, #8
  ext v3.16b, v3.16b, v3.16b, #4
  ext v7.16b, v7.16b, v7.16b, #4
  ext v19.16b, v19.16b, v19.16b, #4
  ext v23.16b, v23.16b, v23.16b, #4
  ext v27.16b, v27.16b, v27.16b, #4
  ext v9.16b, v9.16b, v9.16b, #4
  sub x1, x1, #1
  cbnz x1, 1b
  ldp d10, d11, [sp, #16]
  ldp d12, d13, [sp, #32]
  ldp d14, d15, [sp, #48]
  ldp d8, d9, [sp], #64
  ret
.global k_sve_vec
.type k_sve_vec, %function
.p2align 6
k_sve_vec:
  stp d8, d9, [sp, #-64]!
  stp d10, d11, [sp, #16]
  stp d12, d13, [sp, #32]
  stp d14, d15, [sp, #48]
  mov x1, x0
1:
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  xar z3.s, z3.s, z0.s, #16
  xar z7.s, z7.s, z4.s, #16
  xar z19.s, z19.s, z16.s, #16
  xar z23.s, z23.s, z20.s, #16
  xar z27.s, z27.s, z24.s, #16
  xar z9.s, z9.s, z28.s, #16
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  xar z1.s, z1.s, z2.s, #20
  xar z5.s, z5.s, z6.s, #20
  xar z17.s, z17.s, z18.s, #20
  xar z21.s, z21.s, z22.s, #20
  xar z25.s, z25.s, z26.s, #20
  xar z29.s, z29.s, z8.s, #20
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  tbl v3.16b, {v31.16b}, v30.16b
  tbl v7.16b, {v31.16b}, v30.16b
  tbl v19.16b, {v31.16b}, v30.16b
  tbl v23.16b, {v31.16b}, v30.16b
  tbl v27.16b, {v31.16b}, v30.16b
  tbl v9.16b, {v31.16b}, v30.16b
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  xar z1.s, z1.s, z2.s, #25
  xar z5.s, z5.s, z6.s, #25
  xar z17.s, z17.s, z18.s, #25
  xar z21.s, z21.s, z22.s, #25
  xar z25.s, z25.s, z26.s, #25
  xar z29.s, z29.s, z8.s, #25
  ext v1.16b, v1.16b, v1.16b, #4
  ext v5.16b, v5.16b, v5.16b, #4
  ext v17.16b, v17.16b, v17.16b, #4
  ext v21.16b, v21.16b, v21.16b, #4
  ext v25.16b, v25.16b, v25.16b, #4
  ext v29.16b, v29.16b, v29.16b, #4
  ext v2.16b, v2.16b, v2.16b, #8
  ext v6.16b, v6.16b, v6.16b, #8
  ext v18.16b, v18.16b, v18.16b, #8
  ext v22.16b, v22.16b, v22.16b, #8
  ext v26.16b, v26.16b, v26.16b, #8
  ext v8.16b, v8.16b, v8.16b, #8
  ext v3.16b, v3.16b, v3.16b, #12
  ext v7.16b, v7.16b, v7.16b, #12
  ext v19.16b, v19.16b, v19.16b, #12
  ext v23.16b, v23.16b, v23.16b, #12
  ext v27.16b, v27.16b, v27.16b, #12
  ext v9.16b, v9.16b, v9.16b, #12
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  xar z3.s, z3.s, z0.s, #16
  xar z7.s, z7.s, z4.s, #16
  xar z19.s, z19.s, z16.s, #16
  xar z23.s, z23.s, z20.s, #16
  xar z27.s, z27.s, z24.s, #16
  xar z9.s, z9.s, z28.s, #16
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  xar z1.s, z1.s, z2.s, #20
  xar z5.s, z5.s, z6.s, #20
  xar z17.s, z17.s, z18.s, #20
  xar z21.s, z21.s, z22.s, #20
  xar z25.s, z25.s, z26.s, #20
  xar z29.s, z29.s, z8.s, #20
  add v0.4s, v0.4s, v1.4s
  add v4.4s, v4.4s, v5.4s
  add v16.4s, v16.4s, v17.4s
  add v20.4s, v20.4s, v21.4s
  add v24.4s, v24.4s, v25.4s
  add v28.4s, v28.4s, v29.4s
  tbl v3.16b, {v31.16b}, v30.16b
  tbl v7.16b, {v31.16b}, v30.16b
  tbl v19.16b, {v31.16b}, v30.16b
  tbl v23.16b, {v31.16b}, v30.16b
  tbl v27.16b, {v31.16b}, v30.16b
  tbl v9.16b, {v31.16b}, v30.16b
  add v2.4s, v2.4s, v3.4s
  add v6.4s, v6.4s, v7.4s
  add v18.4s, v18.4s, v19.4s
  add v22.4s, v22.4s, v23.4s
  add v26.4s, v26.4s, v27.4s
  add v8.4s, v8.4s, v9.4s
  xar z1.s, z1.s, z2.s, #25
  xar z5.s, z5.s, z6.s, #25
  xar z17.s, z17.s, z18.s, #25
  xar z21.s, z21.s, z22.s, #25
  xar z25.s, z25.s, z26.s, #25
  xar z29.s, z29.s, z8.s, #25
  ext v1.16b, v1.16b, v1.16b, #12
  ext v5.16b, v5.16b, v5.16b, #12
  ext v17.16b, v17.16b, v17.16b, #12
  ext v21.16b, v21.16b, v21.16b, #12
  ext v25.16b, v25.16b, v25.16b, #12
  ext v29.16b, v29.16b, v29.16b, #12
  ext v2.16b, v2.16b, v2.16b, #8
  ext v6.16b, v6.16b, v6.16b, #8
  ext v18.16b, v18.16b, v18.16b, #8
  ext v22.16b, v22.16b, v22.16b, #8
  ext v26.16b, v26.16b, v26.16b, #8
  ext v8.16b, v8.16b, v8.16b, #8
  ext v3.16b, v3.16b, v3.16b, #4
  ext v7.16b, v7.16b, v7.16b, #4
  ext v19.16b, v19.16b, v19.16b, #4
  ext v23.16b, v23.16b, v23.16b, #4
  ext v27.16b, v27.16b, v27.16b, #4
  ext v9.16b, v9.16b, v9.16b, #4
  sub x1, x1, #1
  cbnz x1, 1b
  ldp d10, d11, [sp, #16]
  ldp d12, d13, [sp, #32]
  ldp d14, d15, [sp, #48]
  ldp d8, d9, [sp], #64
  ret
.global k_scalar
.type k_scalar, %function
.p2align 6
k_scalar:
  stp d8, d9, [sp, #-64]!
  stp d10, d11, [sp, #16]
  stp d12, d13, [sp, #32]
  stp d14, d15, [sp, #48]
  mov x1, x0
1:
  add w2, w2, w6
  add w3, w3, w7
  add w4, w4, w8
  add w5, w5, w9
  eor w14, w14, w2
  ror w14, w14, #16
  eor w15, w15, w3
  ror w15, w15, #16
  eor w16, w16, w4
  ror w16, w16, #16
  eor w17, w17, w5
  ror w17, w17, #16
  add w10, w10, w14
  add w11, w11, w15
  add w12, w12, w16
  add w13, w13, w17
  eor w6, w6, w10
  ror w6, w6, #20
  eor w7, w7, w11
  ror w7, w7, #20
  eor w8, w8, w12
  ror w8, w8, #20
  eor w9, w9, w13
  ror w9, w9, #20
  add w2, w2, w6
  add w3, w3, w7
  add w4, w4, w8
  add w5, w5, w9
  eor w14, w14, w2
  ror w14, w14, #24
  eor w15, w15, w3
  ror w15, w15, #24
  eor w16, w16, w4
  ror w16, w16, #24
  eor w17, w17, w5
  ror w17, w17, #24
  add w10, w10, w14
  add w11, w11, w15
  add w12, w12, w16
  add w13, w13, w17
  eor w6, w6, w10
  ror w6, w6, #25
  eor w7, w7, w11
  ror w7, w7, #25
  eor w8, w8, w12
  ror w8, w8, #25
  eor w9, w9, w13
  ror w9, w9, #25
  add w2, w2, w7
  add w3, w3, w8
  add w4, w4, w9
  add w5, w5, w6
  eor w17, w17, w2
  ror w17, w17, #16
  eor w14, w14, w3
  ror w14, w14, #16
  eor w15, w15, w4
  ror w15, w15, #16
  eor w16, w16, w5
  ror w16, w16, #16
  add w12, w12, w17
  add w13, w13, w14
  add w10, w10, w15
  add w11, w11, w16
  eor w7, w7, w12
  ror w7, w7, #20
  eor w8, w8, w13
  ror w8, w8, #20
  eor w9, w9, w10
  ror w9, w9, #20
  eor w6, w6, w11
  ror w6, w6, #20
  add w2, w2, w7
  add w3, w3, w8
  add w4, w4, w9
  add w5, w5, w6
  eor w17, w17, w2
  ror w17, w17, #24
  eor w14, w14, w3
  ror w14, w14, #24
  eor w15, w15, w4
  ror w15, w15, #24
  eor w16, w16, w5
  ror w16, w16, #24
  add w12, w12, w17
  add w13, w13, w14
  add w10, w10, w15
  add w11, w11, w16
  eor w7, w7, w12
  ror w7, w7, #25
  eor w8, w8, w13
  ror w8, w8, #25
  eor w9, w9, w10
  ror w9, w9, #25
  eor w6, w6, w11
  ror w6, w6, #25
  add w2, w2, w6
  add w3, w3, w7
  add w4, w4, w8
  add w5, w5, w9
  eor w14, w14, w2
  ror w14, w14, #16
  eor w15, w15, w3
  ror w15, w15, #16
  eor w16, w16, w4
  ror w16, w16, #16
  eor w17, w17, w5
  ror w17, w17, #16
  add w10, w10, w14
  add w11, w11, w15
  add w12, w12, w16
  add w13, w13, w17
  eor w6, w6, w10
  ror w6, w6, #20
  eor w7, w7, w11
  ror w7, w7, #20
  eor w8, w8, w12
  ror w8, w8, #20
  eor w9, w9, w13
  ror w9, w9, #20
  add w2, w2, w6
  add w3, w3, w7
  add w4, w4, w8
  add w5, w5, w9
  eor w14, w14, w2
  ror w14, w14, #24
  eor w15, w15, w3
  ror w15, w15, #24
  eor w16, w16, w4
  ror w16, w16, #24
  eor w17, w17, w5
  ror w17, w17, #24
  add w10, w10, w14
  add w11, w11, w15
  add w12, w12, w16
  add w13, w13, w17
  eor w6, w6, w10
  ror w6, w6, #25
  eor w7, w7, w11
  ror w7, w7, #25
  eor w8, w8, w12
  ror w8, w8, #25
  eor w9, w9, w13
  ror w9, w9, #25
  add w2, w2, w7
  add w3, w3, w8
  add w4, w4, w9
  add w5, w5, w6
  eor w17, w17, w2
  ror w17, w17, #16
  eor w14, w14, w3
  ror w14, w14, #16
  eor w15, w15, w4
  ror w15, w15, #16
  eor w16, w16, w5
  ror w16, w16, #16
  add w12, w12, w17
  add w13, w13, w14
  add w10, w10, w15
  add w11, w11, w16
  eor w7, w7, w12
  ror w7, w7, #20
  eor w8, w8, w13
  ror w8, w8, #20
  eor w9, w9, w10
  ror w9, w9, #20
  eor w6, w6, w11
  ror w6, w6, #20
  add w2, w2, w7
  add w3, w3, w8
  add w4, w4, w9
  add w5, w5, w6
  eor w17, w17, w2
  ror w17, w17, #24
  eor w14, w14, w3
  ror w14, w14, #24
  eor w15, w15, w4
  ror w15, w15, #24
  eor w16, w16, w5
  ror w16, w16, #24
  add w12, w12, w17
  add w13, w13, w14
  add w10, w10, w15
  add w11, w11, w16
  eor w7, w7, w12
  ror w7, w7, #25
  eor w8, w8, w13
  ror w8, w8, #25
  eor w9, w9, w10
  ror w9, w9, #25
  eor w6, w6, w11
  ror w6, w6, #25
  sub x1, x1, #1
  cbnz x1, 1b
  ldp d10, d11, [sp, #16]
  ldp d12, d13, [sp, #32]
  ldp d14, d15, [sp, #48]
  ldp d8, d9, [sp], #64
  ret
