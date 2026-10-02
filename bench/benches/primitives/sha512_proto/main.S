.arch_extension sha3
cbz x2, 20f
22:
ldr q0, [x0, #0]
ldr q1, [x0, #16]
ldr q2, [x0, #32]
ldr q3, [x0, #48]
mov v24.16b, v0.16b
mov v25.16b, v1.16b
mov v26.16b, v2.16b
mov v27.16b, v3.16b
ldr q16, [x1, #0]
rev64 v16.16b, v16.16b
movz x4, #44578, lsl #0
movk x4, #55080, lsl #16
movk x4, #12184, lsl #32
movk x4, #17034, lsl #48
dup v4.2d, x4
movz x4, #26061, lsl #0
movk x4, #9199, lsl #16
movk x4, #17553, lsl #32
movk x4, #28983, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q17, [x1, #16]
rev64 v17.16b, v17.16b
movz x4, #15151, lsl #0
movk x4, #60493, lsl #16
movk x4, #64463, lsl #32
movk x4, #46528, lsl #48
dup v4.2d, x4
movz x4, #56252, lsl #0
movk x4, #33161, lsl #16
movk x4, #56229, lsl #32
movk x4, #59829, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q18, [x1, #32]
rev64 v18.16b, v18.16b
movz x4, #46392, lsl #0
movk x4, #62280, lsl #16
movk x4, #49755, lsl #32
movk x4, #14678, lsl #48
dup v4.2d, x4
movz x4, #53273, lsl #0
movk x4, #46597, lsl #16
movk x4, #4593, lsl #32
movk x4, #23025, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q19, [x1, #48]
rev64 v19.16b, v19.16b
movz x4, #20379, lsl #0
movk x4, #44825, lsl #16
movk x4, #33444, lsl #32
movk x4, #37439, lsl #48
dup v4.2d, x4
movz x4, #33048, lsl #0
movk x4, #55917, lsl #16
movk x4, #24277, lsl #32
movk x4, #43804, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q20, [x1, #64]
rev64 v20.16b, v20.16b
movz x4, #578, lsl #0
movk x4, #41731, lsl #16
movk x4, #43672, lsl #32
movk x4, #55303, lsl #48
dup v4.2d, x4
movz x4, #28606, lsl #0
movk x4, #17776, lsl #16
movk x4, #23297, lsl #32
movk x4, #4739, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q21, [x1, #80]
rev64 v21.16b, v21.16b
movz x4, #45708, lsl #0
movk x4, #20196, lsl #16
movk x4, #34238, lsl #32
movk x4, #9265, lsl #48
dup v4.2d, x4
movz x4, #46306, lsl #0
movk x4, #54783, lsl #16
movk x4, #32195, lsl #32
movk x4, #21772, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q22, [x1, #96]
rev64 v22.16b, v22.16b
movz x4, #35183, lsl #0
movk x4, #62075, lsl #16
movk x4, #23924, lsl #32
movk x4, #29374, lsl #48
dup v4.2d, x4
movz x4, #38577, lsl #0
movk x4, #15126, lsl #16
movk x4, #45566, lsl #32
movk x4, #32990, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ldr q23, [x1, #112]
rev64 v23.16b, v23.16b
movz x4, #4661, lsl #0
movk x4, #9671, lsl #16
movk x4, #1703, lsl #32
movk x4, #39900, lsl #48
dup v4.2d, x4
movz x4, #9876, lsl #0
movk x4, #53097, lsl #16
movk x4, #61812, lsl #32
movk x4, #49563, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #19154, lsl #0
movk x4, #40689, lsl #16
movk x4, #27073, lsl #32
movk x4, #58523, lsl #48
dup v4.2d, x4
movz x4, #9699, lsl #0
movk x4, #14415, lsl #16
movk x4, #18310, lsl #32
movk x4, #61374, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #54709, lsl #0
movk x4, #35724, lsl #16
movk x4, #40390, lsl #32
movk x4, #4033, lsl #48
dup v4.2d, x4
movz x4, #40037, lsl #0
movk x4, #30636, lsl #16
movk x4, #41420, lsl #32
movk x4, #9228, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #629, lsl #0
movk x4, #22827, lsl #16
movk x4, #11375, lsl #32
movk x4, #11753, lsl #48
dup v4.2d, x4
movz x4, #58499, lsl #0
movk x4, #28326, lsl #16
movk x4, #33962, lsl #32
movk x4, #19060, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #64468, lsl #0
movk x4, #48449, lsl #16
movk x4, #43484, lsl #32
movk x4, #23728, lsl #48
dup v4.2d, x4
movz x4, #21429, lsl #0
movk x4, #33553, lsl #16
movk x4, #35034, lsl #32
movk x4, #30457, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #57259, lsl #0
movk x4, #61030, lsl #16
movk x4, #20818, lsl #32
movk x4, #38974, lsl #48
dup v4.2d, x4
movz x4, #12816, lsl #0
movk x4, #11700, lsl #16
movk x4, #50797, lsl #32
movk x4, #43057, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #8511, lsl #0
movk x4, #39163, lsl #16
movk x4, #10184, lsl #32
movk x4, #45059, lsl #48
dup v4.2d, x4
movz x4, #3812, lsl #0
movk x4, #48879, lsl #16
movk x4, #32711, lsl #32
movk x4, #48985, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #36802, lsl #0
movk x4, #15784, lsl #16
movk x4, #3059, lsl #32
movk x4, #50912, lsl #48
dup v4.2d, x4
movz x4, #42789, lsl #0
movk x4, #37642, lsl #16
movk x4, #37191, lsl #32
movk x4, #54695, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #33391, lsl #0
movk x4, #57347, lsl #16
movk x4, #25425, lsl #32
movk x4, #1738, lsl #48
dup v4.2d, x4
movz x4, #28272, lsl #0
movk x4, #2574, lsl #16
movk x4, #10599, lsl #32
movk x4, #5161, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #12284, lsl #0
movk x4, #18130, lsl #16
movk x4, #2693, lsl #32
movk x4, #10167, lsl #48
dup v4.2d, x4
movz x4, #51494, lsl #0
movk x4, #23590, lsl #16
movk x4, #8504, lsl #32
movk x4, #11803, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #10989, lsl #0
movk x4, #23236, lsl #16
movk x4, #28156, lsl #32
movk x4, #19756, lsl #48
dup v4.2d, x4
movz x4, #46047, lsl #0
movk x4, #40341, lsl #16
movk x4, #3347, lsl #32
movk x4, #21304, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #25566, lsl #0
movk x4, #35759, lsl #16
movk x4, #29524, lsl #32
movk x4, #25866, lsl #48
dup v4.2d, x4
movz x4, #45736, lsl #0
movk x4, #15479, lsl #16
movk x4, #2747, lsl #32
movk x4, #30314, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #44774, lsl #0
movk x4, #18413, lsl #16
movk x4, #51502, lsl #32
movk x4, #33218, lsl #48
dup v4.2d, x4
movz x4, #13627, lsl #0
movk x4, #5250, lsl #16
movk x4, #11397, lsl #32
movk x4, #37490, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #868, lsl #0
movk x4, #19697, lsl #16
movk x4, #59553, lsl #32
movk x4, #41663, lsl #48
dup v4.2d, x4
movz x4, #12289, lsl #0
movk x4, #48194, lsl #16
movk x4, #26187, lsl #32
movk x4, #43034, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #38801, lsl #0
movk x4, #53496, lsl #16
movk x4, #35696, lsl #32
movk x4, #49739, lsl #48
dup v4.2d, x4
movz x4, #48688, lsl #0
movk x4, #1620, lsl #16
movk x4, #20899, lsl #32
movk x4, #51052, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #21016, lsl #0
movk x4, #55023, lsl #16
movk x4, #59417, lsl #32
movk x4, #53650, lsl #48
dup v4.2d, x4
movz x4, #43280, lsl #0
movk x4, #21861, lsl #16
movk x4, #1572, lsl #32
movk x4, #54937, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #8234, lsl #0
movk x4, #22385, lsl #16
movk x4, #13701, lsl #32
movk x4, #62478, lsl #48
dup v4.2d, x4
movz x4, #53688, lsl #0
movk x4, #12987, lsl #16
movk x4, #41072, lsl #32
movk x4, #4202, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #53448, lsl #0
movk x4, #47314, lsl #16
movk x4, #49430, lsl #32
movk x4, #6564, lsl #48
dup v4.2d, x4
movz x4, #43859, lsl #0
movk x4, #20801, lsl #16
movk x4, #27656, lsl #32
movk x4, #7735, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #60313, lsl #0
movk x4, #57230, lsl #16
movk x4, #30540, lsl #32
movk x4, #10056, lsl #48
dup v4.2d, x4
movz x4, #18600, lsl #0
movk x4, #57755, lsl #16
movk x4, #48309, lsl #32
movk x4, #13488, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #23139, lsl #0
movk x4, #50633, lsl #16
movk x4, #3251, lsl #32
movk x4, #14620, lsl #48
dup v4.2d, x4
movz x4, #35531, lsl #0
movk x4, #58177, lsl #16
movk x4, #43594, lsl #32
movk x4, #20184, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #58227, lsl #0
movk x4, #30563, lsl #16
movk x4, #51791, lsl #32
movk x4, #23452, lsl #48
dup v4.2d, x4
movz x4, #47267, lsl #0
movk x4, #54962, lsl #16
movk x4, #28659, lsl #32
movk x4, #26670, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #45820, lsl #0
movk x4, #24047, lsl #16
movk x4, #33518, lsl #32
movk x4, #29839, lsl #48
dup v4.2d, x4
movz x4, #12128, lsl #0
movk x4, #17175, lsl #16
movk x4, #25455, lsl #32
movk x4, #30885, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #43890, lsl #0
movk x4, #41456, lsl #16
movk x4, #30740, lsl #32
movk x4, #33992, lsl #48
dup v4.2d, x4
movz x4, #14828, lsl #0
movk x4, #6756, lsl #16
movk x4, #520, lsl #32
movk x4, #36039, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #7720, lsl #0
movk x4, #9059, lsl #16
movk x4, #65530, lsl #32
movk x4, #37054, lsl #48
dup v4.2d, x4
movz x4, #48617, lsl #0
movk x4, #56962, lsl #16
movk x4, #27883, lsl #32
movk x4, #42064, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #30997, lsl #0
movk x4, #45766, lsl #16
movk x4, #41975, lsl #32
movk x4, #48889, lsl #48
dup v4.2d, x4
movz x4, #21291, lsl #0
movk x4, #58226, lsl #16
movk x4, #30962, lsl #32
movk x4, #50801, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #24988, lsl #0
movk x4, #59942, lsl #16
movk x4, #16078, lsl #32
movk x4, #51751, lsl #48
dup v4.2d, x4
movz x4, #49671, lsl #0
movk x4, #8640, lsl #16
movk x4, #47303, lsl #32
movk x4, #53638, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #60190, lsl #0
movk x4, #52704, lsl #16
movk x4, #32214, lsl #32
movk x4, #60122, lsl #48
dup v4.2d, x4
movz x4, #53624, lsl #0
movk x4, #61038, lsl #16
movk x4, #20351, lsl #32
movk x4, #62845, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #28602, lsl #0
movk x4, #29207, lsl #16
movk x4, #26538, lsl #32
movk x4, #1776, lsl #48
dup v4.2d, x4
movz x4, #39078, lsl #0
movk x4, #41672, lsl #16
movk x4, #32197, lsl #32
movk x4, #2659, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #3502, lsl #0
movk x4, #48889, lsl #16
movk x4, #38916, lsl #32
movk x4, #4415, lsl #48
dup v4.2d, x4
movz x4, #18203, lsl #0
movk x4, #4892, lsl #16
movk x4, #2869, lsl #32
movk x4, #7025, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #32132, lsl #0
movk x4, #8964, lsl #16
movk x4, #30709, lsl #32
movk x4, #10459, lsl #48
dup v4.2d, x4
movz x4, #9363, lsl #0
movk x4, #16583, lsl #16
movk x4, #43899, lsl #32
movk x4, #13002, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #48828, lsl #0
movk x4, #5577, lsl #16
movk x4, #48650, lsl #32
movk x4, #15518, lsl #48
dup v4.2d, x4
movz x4, #3404, lsl #0
movk x4, #39952, lsl #16
movk x4, #26564, lsl #32
movk x4, #17181, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #17078, lsl #0
movk x4, #52030, lsl #16
movk x4, #54462, lsl #32
movk x4, #19653, lsl #48
dup v4.2d, x4
movz x4, #32298, lsl #0
movk x4, #64613, lsl #16
movk x4, #10652, lsl #32
movk x4, #22911, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #64236, lsl #0
movk x4, #15062, lsl #16
movk x4, #28587, lsl #32
movk x4, #24523, lsl #48
dup v4.2d, x4
movz x4, #22551, lsl #0
movk x4, #19015, lsl #16
movk x4, #6540, lsl #32
movk x4, #27716, lsl #48
mov v4.d[1], x4
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
ext v5.16b, v2.16b, v3.16b, #8
ext v6.16b, v1.16b, v2.16b, #8
sha512h q4, q5, v6.2d
add v5.2d, v1.2d, v4.2d
sha512h2 q4, q1, v0.2d
mov v3.16b, v2.16b
mov v1.16b, v0.16b
mov v0.16b, v4.16b
mov v2.16b, v5.16b
add v0.2d, v0.2d, v24.2d
add v1.2d, v1.2d, v25.2d
add v2.2d, v2.2d, v26.2d
add v3.2d, v3.2d, v27.2d
str q0, [x0, #0]
str q1, [x0, #16]
str q2, [x0, #32]
str q3, [x0, #48]
add x1, x1, #128
sub x2, x2, #1
cbnz x2, 22b
b 21f
20:
21:
ret
