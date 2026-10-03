import VerifiedGarbageTest.AArch64Simd

/-!
# Semantics tests for SVE2 XAR (`xarS`)

Each expected value was computed by the same instruction, in inline assembly
exactly as the printer prints it (checked below), in a program compiled with
GCC 13.3 (`-march=armv8.5-a+sve2`) and run on GitHub's `ubuntu-24.04-arm`
runner: an Arm Neoverse N2 (MIDR part `0xd49`) whose `/proc/cpuinfo` lists
`sve2`, with a vector length of 128 bits (`cntb` returned 16). Before each
instruction the program loaded `v0`–`v2` from the inputs of
`AArch64Simd.lean`'s two runs, and afterwards stored `v0` (the low 128 bits
of `z0`). The rotations include ChaCha20's (16, 20, 24 and 25, rotating
right) and both ends of the encodable range (1 and 32), and the forms whose
second source is the destination, which give zero.
-/

namespace VG.Test.AArch64SveXar

open AArch64
open VG.Test.AArch64Simd (vrun)

#guard vrun 0 (.xarS .v0 .v1 1) == some 0xc906e210938e056722b611220fd4f569#128
#guard vrun 0 (.xarS .v0 .v1 7) == some 0x43241b889e4e3815888ad844a43f53d5#128
#guard vrun 0 (.xarS .v0 .v1 8) == some 0x21920dc4cf271c0a44456c22d21fa9ea#128
#guard vrun 0 (.xarS .v0 .v1 12) == some 0x421920dcacf271c0244456c2ad21fa9e#128
#guard vrun 0 (.xarS .v0 .v1 16) == some 0xc421920d0acf271c2244456cead21fa9#128
#guard vrun 0 (.xarS .v0 .v1 20) == some 0xdc421920c0acf271c22444569ead21fa#128
#guard vrun 0 (.xarS .v0 .v1 24) == some 0x0dc421921c0acf276c224445a9ead21f#128
#guard vrun 0 (.xarS .v0 .v1 25) == some 0x06e210c98e056793b6112222d4f5690f#128
#guard vrun 0 (.xarS .v0 .v1 31) == some 0x241b88434e38159e8ad844883f53d5a4#128
#guard vrun 0 (.xarS .v0 .v1 32) == some 0x920dc421271c0acf456c22441fa9ead2#128
#guard vrun 0 (.xarS .v0 .v2 1) == some 0xafc2f3780a7dd3b7dd30478bd3ea592f#128
#guard vrun 0 (.xarS .v0 .v2 7) == some 0xe2bf0bcddc29f74e2f74c11ebf4fa964#128
#guard vrun 0 (.xarS .v0 .v2 8) == some 0xf15f85e66e14fba717ba608f5fa7d4b2#128
#guard vrun 0 (.xarS .v0 .v2 12) == some 0x6f15f85e76e14fbaf17ba60825fa7d4b#128
#guard vrun 0 (.xarS .v0 .v2 16) == some 0xe6f15f85a76e14fb8f17ba60b25fa7d4#128
#guard vrun 0 (.xarS .v0 .v2 20) == some 0x5e6f15f8ba76e14f08f17ba64b25fa7d#128
#guard vrun 0 (.xarS .v0 .v2 24) == some 0x85e6f15ffba76e14608f17bad4b25fa7#128
#guard vrun 0 (.xarS .v0 .v2 25) == some 0xc2f378af7dd3b70a30478bddea592fd3#128
#guard vrun 0 (.xarS .v0 .v2 31) == some 0xbf0bcde229f74edc74c11e2f4fa964bf#128
#guard vrun 0 (.xarS .v0 .v2 32) == some 0x5f85e6f114fba76eba608f17a7d4b25f#128
#guard vrun 1 (.xarS .v0 .v1 1) == some 0x47660a80e1c908beeb26031aee146ed5#128
#guard vrun 1 (.xarS .v0 .v1 7) == some 0x011d982afb8724226bac980c57b851bb#128
#guard vrun 1 (.xarS .v0 .v1 8) == some 0x008ecc157dc3921135d64c06abdc28dd#128
#guard vrun 1 (.xarS .v0 .v1 12) == some 0x5008ecc117dc3921635d64c0dabdc28d#128
#guard vrun 1 (.xarS .v0 .v1 16) == some 0x15008ecc117dc3920635d64cddabdc28#128
#guard vrun 1 (.xarS .v0 .v1 20) == some 0xc15008ec2117dc39c0635d648ddabdc2#128
#guard vrun 1 (.xarS .v0 .v1 24) == some 0xcc15008e92117dc34c0635d628ddabdc#128
#guard vrun 1 (.xarS .v0 .v1 25) == some 0x660a8047c908bee126031aeb146ed5ee#128
#guard vrun 1 (.xarS .v0 .v1 31) == some 0x1d982a01872422fbac980c6bb851bb57#128
#guard vrun 1 (.xarS .v0 .v1 32) == some 0x8ecc1500c392117dd64c0635dc28ddab#128
#guard vrun 1 (.xarS .v0 .v2 1) == some 0xb6d05d1b6d90e74c539dcfea826798c1#128
#guard vrun 1 (.xarS .v0 .v2 7) == some 0x6edb417431b6439da94e773f06099e63#128
#guard vrun 1 (.xarS .v0 .v2 8) == some 0x376da0ba98db21ced4a73b9f8304cf31#128
#guard vrun 1 (.xarS .v0 .v2 12) == some 0xa376da0be98db21cfd4a73b918304cf3#128
#guard vrun 1 (.xarS .v0 .v2 16) == some 0xba376da0ce98db219fd4a73b318304cf#128
#guard vrun 1 (.xarS .v0 .v2 20) == some 0x0ba376da1ce98db2b9fd4a73f318304c#128
#guard vrun 1 (.xarS .v0 .v2 24) == some 0xa0ba376d21ce98db3b9fd4a7cf318304#128
#guard vrun 1 (.xarS .v0 .v2 25) == some 0xd05d1bb690e74c6d9dcfea536798c182#128
#guard vrun 1 (.xarS .v0 .v2 31) == some 0xdb41746eb6439d314e773fa9099e6306#128
#guard vrun 1 (.xarS .v0 .v2 32) == some 0x6da0ba37db21ce98a73b9fd404cf3183#128
#guard vrun 0 (.xarS .v0 .v0 1) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 7) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 8) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 12) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 16) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 20) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 24) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 25) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 31) == some 0#128
#guard vrun 0 (.xarS .v0 .v0 32) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 1) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 7) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 8) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 12) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 16) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 20) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 24) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 25) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 31) == some 0#128
#guard vrun 1 (.xarS .v0 .v0 32) == some 0#128

-- Rotations outside 1–32 are not encodable, and the model faults.
#guard vrun 0 (.xarS .v0 .v1 0) == none
#guard vrun 0 (.xarS .v0 .v1 33) == none

#guard printer.instr (.vop (.xarS .v0 .v1 16)) == ["xar z0.s, z0.s, z1.s, #16"]
#guard printer.instr (.vop (.xarS .v31 .v7 25)) == ["xar z31.s, z31.s, z7.s, #25"]
#guard isa.requires (.vop (.xarS .v0 .v1 16)) == ["sve2"]

end VG.Test.AArch64SveXar
