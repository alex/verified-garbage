.arch_extension sha3
cbz x2, 20f
movi v31.2d, #0
ldr q24, [x0, #0]
ldr q25, [x0, #16]
ldr q26, [x0, #32]
ldr q27, [x0, #48]
mov v0.16b, v24.16b
mov v1.16b, v25.16b
mov v2.16b, v26.16b
mov v3.16b, v27.16b
movz x4, #44578, lsl #0
movk x4, #55080, lsl #16
movk x4, #12184, lsl #32
movk x4, #17034, lsl #48
str x4, [x3, #0]
movz x5, #26061, lsl #0
movk x5, #9199, lsl #16
movk x5, #17553, lsl #32
movk x5, #28983, lsl #48
str x5, [x3, #8]
movz x4, #15151, lsl #0
movk x4, #60493, lsl #16
movk x4, #64463, lsl #32
movk x4, #46528, lsl #48
str x4, [x3, #16]
movz x5, #56252, lsl #0
movk x5, #33161, lsl #16
movk x5, #56229, lsl #32
movk x5, #59829, lsl #48
str x5, [x3, #24]
movz x4, #46392, lsl #0
movk x4, #62280, lsl #16
movk x4, #49755, lsl #32
movk x4, #14678, lsl #48
str x4, [x3, #32]
movz x5, #53273, lsl #0
movk x5, #46597, lsl #16
movk x5, #4593, lsl #32
movk x5, #23025, lsl #48
str x5, [x3, #40]
movz x4, #20379, lsl #0
movk x4, #44825, lsl #16
movk x4, #33444, lsl #32
movk x4, #37439, lsl #48
str x4, [x3, #48]
movz x5, #33048, lsl #0
movk x5, #55917, lsl #16
movk x5, #24277, lsl #32
movk x5, #43804, lsl #48
str x5, [x3, #56]
movz x4, #578, lsl #0
movk x4, #41731, lsl #16
movk x4, #43672, lsl #32
movk x4, #55303, lsl #48
str x4, [x3, #64]
movz x5, #28606, lsl #0
movk x5, #17776, lsl #16
movk x5, #23297, lsl #32
movk x5, #4739, lsl #48
str x5, [x3, #72]
movz x4, #45708, lsl #0
movk x4, #20196, lsl #16
movk x4, #34238, lsl #32
movk x4, #9265, lsl #48
str x4, [x3, #80]
movz x5, #46306, lsl #0
movk x5, #54783, lsl #16
movk x5, #32195, lsl #32
movk x5, #21772, lsl #48
str x5, [x3, #88]
movz x4, #35183, lsl #0
movk x4, #62075, lsl #16
movk x4, #23924, lsl #32
movk x4, #29374, lsl #48
str x4, [x3, #96]
movz x5, #38577, lsl #0
movk x5, #15126, lsl #16
movk x5, #45566, lsl #32
movk x5, #32990, lsl #48
str x5, [x3, #104]
movz x4, #4661, lsl #0
movk x4, #9671, lsl #16
movk x4, #1703, lsl #32
movk x4, #39900, lsl #48
str x4, [x3, #112]
movz x5, #9876, lsl #0
movk x5, #53097, lsl #16
movk x5, #61812, lsl #32
movk x5, #49563, lsl #48
str x5, [x3, #120]
ldr q16, [x1, #0]
rev64 v16.16b, v16.16b
movz x4, #19154, lsl #0
movk x4, #40689, lsl #16
movk x4, #27073, lsl #32
movk x4, #58523, lsl #48
str x4, [x3, #128]
movz x5, #9699, lsl #0
movk x5, #14415, lsl #16
movk x5, #18310, lsl #32
movk x5, #61374, lsl #48
str x5, [x3, #136]
ldr q4, [x3, #0]
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ldr q17, [x1, #16]
rev64 v17.16b, v17.16b
movz x4, #54709, lsl #0
movk x4, #35724, lsl #16
movk x4, #40390, lsl #32
movk x4, #4033, lsl #48
str x4, [x3, #144]
movz x5, #40037, lsl #0
movk x5, #30636, lsl #16
movk x5, #41420, lsl #32
movk x5, #9228, lsl #48
str x5, [x3, #152]
ldr q1, [x3, #16]
add v1.2d, v1.2d, v17.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ldr q18, [x1, #32]
rev64 v18.16b, v18.16b
movz x4, #629, lsl #0
movk x4, #22827, lsl #16
movk x4, #11375, lsl #32
movk x4, #11753, lsl #48
str x4, [x3, #160]
movz x5, #58499, lsl #0
movk x5, #28326, lsl #16
movk x5, #33962, lsl #32
movk x5, #19060, lsl #48
str x5, [x3, #168]
ldr q0, [x3, #32]
add v0.2d, v0.2d, v18.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ldr q19, [x1, #48]
rev64 v19.16b, v19.16b
movz x4, #64468, lsl #0
movk x4, #48449, lsl #16
movk x4, #43484, lsl #32
movk x4, #23728, lsl #48
str x4, [x3, #176]
movz x5, #21429, lsl #0
movk x5, #33553, lsl #16
movk x5, #35034, lsl #32
movk x5, #30457, lsl #48
str x5, [x3, #184]
ldr q4, [x3, #48]
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ldr q20, [x1, #64]
rev64 v20.16b, v20.16b
movz x4, #57259, lsl #0
movk x4, #61030, lsl #16
movk x4, #20818, lsl #32
movk x4, #38974, lsl #48
str x4, [x3, #192]
movz x5, #12816, lsl #0
movk x5, #11700, lsl #16
movk x5, #50797, lsl #32
movk x5, #43057, lsl #48
str x5, [x3, #200]
ldr q1, [x3, #64]
add v1.2d, v1.2d, v20.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ldr q21, [x1, #80]
rev64 v21.16b, v21.16b
movz x4, #8511, lsl #0
movk x4, #39163, lsl #16
movk x4, #10184, lsl #32
movk x4, #45059, lsl #48
str x4, [x3, #208]
movz x5, #3812, lsl #0
movk x5, #48879, lsl #16
movk x5, #32711, lsl #32
movk x5, #48985, lsl #48
str x5, [x3, #216]
ldr q0, [x3, #80]
add v0.2d, v0.2d, v21.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ldr q22, [x1, #96]
rev64 v22.16b, v22.16b
movz x4, #36802, lsl #0
movk x4, #15784, lsl #16
movk x4, #3059, lsl #32
movk x4, #50912, lsl #48
str x4, [x3, #224]
movz x5, #42789, lsl #0
movk x5, #37642, lsl #16
movk x5, #37191, lsl #32
movk x5, #54695, lsl #48
str x5, [x3, #232]
ldr q4, [x3, #96]
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ldr q23, [x1, #112]
rev64 v23.16b, v23.16b
movz x4, #33391, lsl #0
movk x4, #57347, lsl #16
movk x4, #25425, lsl #32
movk x4, #1738, lsl #48
str x4, [x3, #240]
movz x5, #28272, lsl #0
movk x5, #2574, lsl #16
movk x5, #10599, lsl #32
movk x5, #5161, lsl #48
str x5, [x3, #248]
ldr q1, [x3, #112]
add v1.2d, v1.2d, v23.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #12284, lsl #0
movk x4, #18130, lsl #16
movk x4, #2693, lsl #32
movk x4, #10167, lsl #48
str x4, [x3, #256]
movz x5, #51494, lsl #0
movk x5, #23590, lsl #16
movk x5, #8504, lsl #32
movk x5, #11803, lsl #48
str x5, [x3, #264]
ldr q0, [x3, #128]
add v0.2d, v0.2d, v16.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #10989, lsl #0
movk x4, #23236, lsl #16
movk x4, #28156, lsl #32
movk x4, #19756, lsl #48
str x4, [x3, #272]
movz x5, #46047, lsl #0
movk x5, #40341, lsl #16
movk x5, #3347, lsl #32
movk x5, #21304, lsl #48
str x5, [x3, #280]
ldr q4, [x3, #144]
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #25566, lsl #0
movk x4, #35759, lsl #16
movk x4, #29524, lsl #32
movk x4, #25866, lsl #48
str x4, [x3, #288]
movz x5, #45736, lsl #0
movk x5, #15479, lsl #16
movk x5, #2747, lsl #32
movk x5, #30314, lsl #48
str x5, [x3, #296]
ldr q1, [x3, #160]
add v1.2d, v1.2d, v18.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #44774, lsl #0
movk x4, #18413, lsl #16
movk x4, #51502, lsl #32
movk x4, #33218, lsl #48
str x4, [x3, #304]
movz x5, #13627, lsl #0
movk x5, #5250, lsl #16
movk x5, #11397, lsl #32
movk x5, #37490, lsl #48
str x5, [x3, #312]
ldr q0, [x3, #176]
add v0.2d, v0.2d, v19.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #868, lsl #0
movk x4, #19697, lsl #16
movk x4, #59553, lsl #32
movk x4, #41663, lsl #48
str x4, [x3, #320]
movz x5, #12289, lsl #0
movk x5, #48194, lsl #16
movk x5, #26187, lsl #32
movk x5, #43034, lsl #48
str x5, [x3, #328]
ldr q4, [x3, #192]
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #38801, lsl #0
movk x4, #53496, lsl #16
movk x4, #35696, lsl #32
movk x4, #49739, lsl #48
str x4, [x3, #336]
movz x5, #48688, lsl #0
movk x5, #1620, lsl #16
movk x5, #20899, lsl #32
movk x5, #51052, lsl #48
str x5, [x3, #344]
ldr q1, [x3, #208]
add v1.2d, v1.2d, v21.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #21016, lsl #0
movk x4, #55023, lsl #16
movk x4, #59417, lsl #32
movk x4, #53650, lsl #48
str x4, [x3, #352]
movz x5, #43280, lsl #0
movk x5, #21861, lsl #16
movk x5, #1572, lsl #32
movk x5, #54937, lsl #48
str x5, [x3, #360]
ldr q0, [x3, #224]
add v0.2d, v0.2d, v22.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #8234, lsl #0
movk x4, #22385, lsl #16
movk x4, #13701, lsl #32
movk x4, #62478, lsl #48
str x4, [x3, #368]
movz x5, #53688, lsl #0
movk x5, #12987, lsl #16
movk x5, #41072, lsl #32
movk x5, #4202, lsl #48
str x5, [x3, #376]
ldr q4, [x3, #240]
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #53448, lsl #0
movk x4, #47314, lsl #16
movk x4, #49430, lsl #32
movk x4, #6564, lsl #48
str x4, [x3, #384]
movz x5, #43859, lsl #0
movk x5, #20801, lsl #16
movk x5, #27656, lsl #32
movk x5, #7735, lsl #48
str x5, [x3, #392]
ldr q1, [x3, #256]
add v1.2d, v1.2d, v16.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #60313, lsl #0
movk x4, #57230, lsl #16
movk x4, #30540, lsl #32
movk x4, #10056, lsl #48
str x4, [x3, #400]
movz x5, #18600, lsl #0
movk x5, #57755, lsl #16
movk x5, #48309, lsl #32
movk x5, #13488, lsl #48
str x5, [x3, #408]
ldr q0, [x3, #272]
add v0.2d, v0.2d, v17.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #23139, lsl #0
movk x4, #50633, lsl #16
movk x4, #3251, lsl #32
movk x4, #14620, lsl #48
str x4, [x3, #416]
movz x5, #35531, lsl #0
movk x5, #58177, lsl #16
movk x5, #43594, lsl #32
movk x5, #20184, lsl #48
str x5, [x3, #424]
ldr q4, [x3, #288]
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #58227, lsl #0
movk x4, #30563, lsl #16
movk x4, #51791, lsl #32
movk x4, #23452, lsl #48
str x4, [x3, #432]
movz x5, #47267, lsl #0
movk x5, #54962, lsl #16
movk x5, #28659, lsl #32
movk x5, #26670, lsl #48
str x5, [x3, #440]
ldr q1, [x3, #304]
add v1.2d, v1.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #45820, lsl #0
movk x4, #24047, lsl #16
movk x4, #33518, lsl #32
movk x4, #29839, lsl #48
str x4, [x3, #448]
movz x5, #12128, lsl #0
movk x5, #17175, lsl #16
movk x5, #25455, lsl #32
movk x5, #30885, lsl #48
str x5, [x3, #456]
ldr q0, [x3, #320]
add v0.2d, v0.2d, v20.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #43890, lsl #0
movk x4, #41456, lsl #16
movk x4, #30740, lsl #32
movk x4, #33992, lsl #48
str x4, [x3, #464]
movz x5, #14828, lsl #0
movk x5, #6756, lsl #16
movk x5, #520, lsl #32
movk x5, #36039, lsl #48
str x5, [x3, #472]
ldr q4, [x3, #336]
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #7720, lsl #0
movk x4, #9059, lsl #16
movk x4, #65530, lsl #32
movk x4, #37054, lsl #48
str x4, [x3, #480]
movz x5, #48617, lsl #0
movk x5, #56962, lsl #16
movk x5, #27883, lsl #32
movk x5, #42064, lsl #48
str x5, [x3, #488]
ldr q1, [x3, #352]
add v1.2d, v1.2d, v22.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #30997, lsl #0
movk x4, #45766, lsl #16
movk x4, #41975, lsl #32
movk x4, #48889, lsl #48
str x4, [x3, #496]
movz x5, #21291, lsl #0
movk x5, #58226, lsl #16
movk x5, #30962, lsl #32
movk x5, #50801, lsl #48
str x5, [x3, #504]
ldr q0, [x3, #368]
add v0.2d, v0.2d, v23.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
movz x4, #24988, lsl #0
movk x4, #59942, lsl #16
movk x4, #16078, lsl #32
movk x4, #51751, lsl #48
str x4, [x3, #512]
movz x5, #49671, lsl #0
movk x5, #8640, lsl #16
movk x5, #47303, lsl #32
movk x5, #53638, lsl #48
str x5, [x3, #520]
ldr q4, [x3, #384]
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
movz x4, #60190, lsl #0
movk x4, #52704, lsl #16
movk x4, #32214, lsl #32
movk x4, #60122, lsl #48
str x4, [x3, #528]
movz x5, #53624, lsl #0
movk x5, #61038, lsl #16
movk x5, #20351, lsl #32
movk x5, #62845, lsl #48
str x5, [x3, #536]
ldr q1, [x3, #400]
add v1.2d, v1.2d, v17.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
movz x4, #28602, lsl #0
movk x4, #29207, lsl #16
movk x4, #26538, lsl #32
movk x4, #1776, lsl #48
str x4, [x3, #544]
movz x5, #39078, lsl #0
movk x5, #41672, lsl #16
movk x5, #32197, lsl #32
movk x5, #2659, lsl #48
str x5, [x3, #552]
ldr q0, [x3, #416]
add v0.2d, v0.2d, v18.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
movz x4, #3502, lsl #0
movk x4, #48889, lsl #16
movk x4, #38916, lsl #32
movk x4, #4415, lsl #48
str x4, [x3, #560]
movz x5, #18203, lsl #0
movk x5, #4892, lsl #16
movk x5, #2869, lsl #32
movk x5, #7025, lsl #48
str x5, [x3, #568]
ldr q4, [x3, #432]
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
movz x4, #32132, lsl #0
movk x4, #8964, lsl #16
movk x4, #30709, lsl #32
movk x4, #10459, lsl #48
str x4, [x3, #576]
movz x5, #9363, lsl #0
movk x5, #16583, lsl #16
movk x5, #43899, lsl #32
movk x5, #13002, lsl #48
str x5, [x3, #584]
ldr q1, [x3, #448]
add v1.2d, v1.2d, v20.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
movz x4, #48828, lsl #0
movk x4, #5577, lsl #16
movk x4, #48650, lsl #32
movk x4, #15518, lsl #48
str x4, [x3, #592]
movz x5, #3404, lsl #0
movk x5, #39952, lsl #16
movk x5, #26564, lsl #32
movk x5, #17181, lsl #48
str x5, [x3, #600]
ldr q0, [x3, #464]
add v0.2d, v0.2d, v21.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
movz x4, #17078, lsl #0
movk x4, #52030, lsl #16
movk x4, #54462, lsl #32
movk x4, #19653, lsl #48
str x4, [x3, #608]
movz x5, #32298, lsl #0
movk x5, #64613, lsl #16
movk x5, #10652, lsl #32
movk x5, #22911, lsl #48
str x5, [x3, #616]
ldr q4, [x3, #480]
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
movz x4, #64236, lsl #0
movk x4, #15062, lsl #16
movk x4, #28587, lsl #32
movk x4, #24523, lsl #48
str x4, [x3, #624]
movz x5, #22551, lsl #0
movk x5, #19015, lsl #16
movk x5, #6540, lsl #32
movk x5, #27716, lsl #48
str x5, [x3, #632]
ldr q1, [x3, #496]
add v1.2d, v1.2d, v23.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
ldr q0, [x3, #512]
add v0.2d, v0.2d, v16.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
ldr q4, [x3, #528]
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
ldr q1, [x3, #544]
add v1.2d, v1.2d, v18.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
ldr q0, [x3, #560]
add v0.2d, v0.2d, v19.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
ldr q4, [x3, #576]
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
ldr q1, [x3, #592]
add v1.2d, v1.2d, v21.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
ldr q0, [x3, #608]
add v0.2d, v0.2d, v22.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
ldr q4, [x3, #624]
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
add v24.2d, v4.2d, v24.2d
add v25.2d, v0.2d, v25.2d
add v26.2d, v5.2d, v26.2d
add v27.2d, v2.2d, v27.2d
str q24, [x0, #0]
str q25, [x0, #16]
str q26, [x0, #32]
str q27, [x0, #48]
add x1, x1, #128
sub x2, x2, #1
cbz x2, 20f
22:
mov v0.16b, v24.16b
mov v1.16b, v25.16b
mov v2.16b, v26.16b
mov v3.16b, v27.16b
ldr q16, [x1, #0]
rev64 v16.16b, v16.16b
ldr q4, [x3, #0]
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ldr q17, [x1, #16]
rev64 v17.16b, v17.16b
ldr q1, [x3, #16]
add v1.2d, v1.2d, v17.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ldr q18, [x1, #32]
rev64 v18.16b, v18.16b
ldr q0, [x3, #32]
add v0.2d, v0.2d, v18.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ldr q19, [x1, #48]
rev64 v19.16b, v19.16b
ldr q4, [x3, #48]
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ldr q20, [x1, #64]
rev64 v20.16b, v20.16b
ldr q1, [x3, #64]
add v1.2d, v1.2d, v20.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ldr q21, [x1, #80]
rev64 v21.16b, v21.16b
ldr q0, [x3, #80]
add v0.2d, v0.2d, v21.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ldr q22, [x1, #96]
rev64 v22.16b, v22.16b
ldr q4, [x3, #96]
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ldr q23, [x1, #112]
rev64 v23.16b, v23.16b
ldr q1, [x3, #112]
add v1.2d, v1.2d, v23.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
ldr q0, [x3, #128]
add v0.2d, v0.2d, v16.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
ldr q4, [x3, #144]
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
ldr q1, [x3, #160]
add v1.2d, v1.2d, v18.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
ldr q0, [x3, #176]
add v0.2d, v0.2d, v19.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
ldr q4, [x3, #192]
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
ldr q1, [x3, #208]
add v1.2d, v1.2d, v21.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
ldr q0, [x3, #224]
add v0.2d, v0.2d, v22.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
ldr q4, [x3, #240]
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
ldr q1, [x3, #256]
add v1.2d, v1.2d, v16.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
ldr q0, [x3, #272]
add v0.2d, v0.2d, v17.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
ldr q4, [x3, #288]
add v4.2d, v4.2d, v18.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
ldr q1, [x3, #304]
add v1.2d, v1.2d, v19.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
ldr q0, [x3, #320]
add v0.2d, v0.2d, v20.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
ldr q4, [x3, #336]
add v4.2d, v4.2d, v21.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
ldr q1, [x3, #352]
add v1.2d, v1.2d, v22.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
ldr q0, [x3, #368]
add v0.2d, v0.2d, v23.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
ldr q4, [x3, #384]
add v4.2d, v4.2d, v16.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
ldr q1, [x3, #400]
add v1.2d, v1.2d, v17.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
ldr q0, [x3, #416]
add v0.2d, v0.2d, v18.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
ldr q4, [x3, #432]
add v4.2d, v4.2d, v19.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
ldr q1, [x3, #448]
add v1.2d, v1.2d, v20.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
ldr q0, [x3, #464]
add v0.2d, v0.2d, v21.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
ldr q4, [x3, #480]
add v4.2d, v4.2d, v22.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
ldr q1, [x3, #496]
add v1.2d, v1.2d, v23.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v20.16b, v21.16b, #8
sha512su0 v16.2d, v17.2d
sha512su1 v16.2d, v23.2d, v6.2d
ldr q0, [x3, #512]
add v0.2d, v0.2d, v16.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v21.16b, v22.16b, #8
sha512su0 v17.2d, v18.2d
sha512su1 v17.2d, v16.2d, v6.2d
ldr q4, [x3, #528]
add v4.2d, v4.2d, v17.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v22.16b, v23.16b, #8
sha512su0 v18.2d, v19.2d
sha512su1 v18.2d, v17.2d, v6.2d
ldr q1, [x3, #544]
add v1.2d, v1.2d, v18.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v23.16b, v16.16b, #8
sha512su0 v19.2d, v20.2d
sha512su1 v19.2d, v18.2d, v6.2d
ldr q0, [x3, #560]
add v0.2d, v0.2d, v19.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v16.16b, v17.16b, #8
sha512su0 v20.2d, v21.2d
sha512su1 v20.2d, v19.2d, v6.2d
ldr q4, [x3, #576]
add v4.2d, v4.2d, v20.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
ext v6.16b, v17.16b, v18.16b, #8
sha512su0 v21.2d, v22.2d
sha512su1 v21.2d, v20.2d, v6.2d
ldr q1, [x3, #592]
add v1.2d, v1.2d, v21.2d
ext v1.16b, v1.16b, v1.16b, #8
add v1.2d, v1.2d, v2.2d
add v3.2d, v1.2d, v0.2d
ext v6.16b, v5.16b, v2.16b, #8
ext v7.16b, v31.16b, v5.16b, #8
ext v28.16b, v0.16b, v5.16b, #8
sha512h q3, q6, v7.2d
sha512h q1, q6, v28.2d
sha512h2 q1, q0, v4.2d
ext v6.16b, v18.16b, v19.16b, #8
sha512su0 v22.2d, v23.2d
sha512su1 v22.2d, v21.2d, v6.2d
ldr q0, [x3, #608]
add v0.2d, v0.2d, v22.2d
ext v0.16b, v0.16b, v0.16b, #8
add v0.2d, v0.2d, v5.2d
add v2.2d, v0.2d, v4.2d
ext v6.16b, v3.16b, v5.16b, #8
ext v7.16b, v31.16b, v3.16b, #8
ext v28.16b, v4.16b, v3.16b, #8
sha512h q2, q6, v7.2d
sha512h q0, q6, v28.2d
sha512h2 q0, q4, v1.2d
ext v6.16b, v19.16b, v20.16b, #8
sha512su0 v23.2d, v16.2d
sha512su1 v23.2d, v22.2d, v6.2d
ldr q4, [x3, #624]
add v4.2d, v4.2d, v23.2d
ext v4.16b, v4.16b, v4.16b, #8
add v4.2d, v4.2d, v3.2d
add v5.2d, v4.2d, v1.2d
ext v6.16b, v2.16b, v3.16b, #8
ext v7.16b, v31.16b, v2.16b, #8
ext v28.16b, v1.16b, v2.16b, #8
sha512h q5, q6, v7.2d
sha512h q4, q6, v28.2d
sha512h2 q4, q1, v0.2d
add v24.2d, v4.2d, v24.2d
add v25.2d, v0.2d, v25.2d
add v26.2d, v5.2d, v26.2d
add v27.2d, v2.2d, v27.2d
str q24, [x0, #0]
str q25, [x0, #16]
str q26, [x0, #32]
str q27, [x0, #48]
add x1, x1, #128
sub x2, x2, #1
cbnz x2, 22b
20:
ret
