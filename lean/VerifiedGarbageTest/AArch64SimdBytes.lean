import VerifiedGarbage.TCB.AArch64.Print

/-!
# Semantics tests for AArch64 byte-lane AdvSIMD instructions

Tests the AdvSIMD forms added for table lookups in registers: the `.16b`
arrangement of ADD, SUB, DUP (general), INS (general), the shifts and the
permutations; DUP (element) and INS (element); CMEQ (register); BSL, BIT
and BIF; SSHR; and TBL and TBX of one to four registers.

Each expected value was computed by the same instruction, in inline
assembly exactly as the printer prints it (checked below), in a program
compiled with Apple clang 21 and run on an Apple M1 Max (natively, not under
emulation). Before each instruction the program loaded `v0`–`v7`, `v30`,
`v31` and `x1` from the inputs below (pseudorandom values of a fixed seed;
`v3` agrees with `v1` in about half its bytes, in a whole word and a whole
doubleword, so that CMEQ sees equal and unequal lanes; `v7`'s bytes are
below 80, so that a table of one to four registers sees indices both inside
and outside it), and afterwards stored the destination. The tables
starting at `v30` wrap around to `v0`.
-/

namespace VG.Test.AArch64SimdBytes

open AArch64

/-- The vector inputs of run 0. -/
def vin0 : VReg → BitVec 128
  | .v0 => 0x01434be3ebf87ed69c1bbf9c0735c9c9#128
  | .v1 => 0xd77a0cb424b63937ea0cf04256be1d97#128
  | .v2 => 0x1b5a878b864b214d49d773ab7f6f0e52#128
  | .v3 => 0xd77a0cb424b63937eaa67b4256be1d97#128
  | .v4 => 0x4c55a76c841f30cf632003f79ec97f27#128
  | .v5 => 0x79e011a8aa14971704afe3150d0631f9#128
  | .v6 => 0x1fc93d1bcae69e40f86ef6f36072281a#128
  | .v7 => 0x0445420f171f2719422712332842101b#128
  | .v30 => 0x20890445c1b3c37ae04cbc47a24877d3#128
  | .v31 => 0x0e841b5c82fa89e89ea9a660d3e62d19#128
  | _ => 0

/-- The vector inputs of run 1. -/
def vin1 : VReg → BitVec 128
  | .v0 => 0x6c9795af2d54593abfa72e0e834dc28b#128
  | .v1 => 0xd07d4e60f85a7d5d4ec96513022a0a2d#128
  | .v2 => 0xb15de273ec11202507f5b2dcc2734420#128
  | .v3 => 0xd07d6660f8ddbc5d4ec9651302640a2d#128
  | .v4 => 0xdf7a7aabe8b27f353d5b70ba39c96754#128
  | .v5 => 0xce6dbc6eb3824bc1b9ef941a8cfe7ea8#128
  | .v6 => 0xc6d98aa97ff9d999a6021dba17749e69#128
  | .v7 => 0x11242917191e2d2a1f07193e32420a17#128
  | .v30 => 0xcc00595469747cafbf1b722f0a8e5044#128
  | .v31 => 0xbe80b9348534c2f4803f6d3f7e619e27#128
  | _ => 0

/-- The state before run `k`: its inputs in the vector registers and `x1`,
`0xdeadbeefdeadbeef` in the other general-purpose registers. -/
def s (k : Nat) : State :=
  { gpr := fun r => if r = .x1 then (if k = 0 then 0x1429c1e08c15d86f#64 else 0x50e15c6afca3cdb2#64)
      else 0xdeadbeefdeadbeef
    sp := 0x1000
    v := if k = 0 then vin0 else vin1
    mem := fun _ => 0
    rd := []
    wr := [] }

/-- The destination `d` after `op` in run `k`. -/
def vrun (k : Nat) (op : VOp) (d : VReg := .v0) : Option (BitVec 128) :=
  (exec (.vop op) (s k)).map (·.v d)

#guard vrun 0 (.dupE .b16 .v0 .v1 0) == some 0x97979797979797979797979797979797#128
#guard vrun 0 (.dupE .b16 .v0 .v1 5) == some 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#128
#guard vrun 0 (.dupE .b16 .v0 .v1 15) == some 0xd7d7d7d7d7d7d7d7d7d7d7d7d7d7d7d7#128
#guard vrun 0 (.dupE .s4 .v0 .v1 2) == some 0x24b6393724b6393724b6393724b63937#128
#guard vrun 0 (.dupE .d2 .v0 .v1 1) == some 0xd77a0cb424b63937d77a0cb424b63937#128
#guard vrun 0 (.dupE .b16 .v0 .v0 9) == some 0x7e7e7e7e7e7e7e7e7e7e7e7e7e7e7e7e#128
#guard vrun 0 (.insE .b16 .v0 3 .v1 12) == some 0x01434be3ebf87ed69c1bbf9cb435c9c9#128
#guard vrun 0 (.insE .b16 .v0 0 .v1 0) == some 0x01434be3ebf87ed69c1bbf9c0735c997#128
#guard vrun 0 (.insE .b16 .v0 15 .v1 7) == some 0xea434be3ebf87ed69c1bbf9c0735c9c9#128
#guard vrun 0 (.insE .b16 .v0 2 .v0 14) == some 0x01434be3ebf87ed69c1bbf9c0743c9c9#128
#guard vrun 0 (.insE .s4 .v0 1 .v1 3) == some 0x01434be3ebf87ed6d77a0cb40735c9c9#128
#guard vrun 0 (.insE .d2 .v0 0 .v1 1) == some 0x01434be3ebf87ed6d77a0cb424b63937#128
#guard vrun 0 (.dup .b16 .v0 .x1) == some 0x6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f6f#128
#guard vrun 0 (.ins .b16 .v0 0 .x1) == some 0x01434be3ebf87ed69c1bbf9c0735c96f#128
#guard vrun 0 (.ins .b16 .v0 6 .x1) == some 0x01434be3ebf87ed69c6fbf9c0735c9c9#128
#guard vrun 0 (.ins .b16 .v0 15 .x1) == some 0x6f434be3ebf87ed69c1bbf9c0735c9c9#128
#guard vrun 0 (.cmeq .b16 .v0 .v1 .v3) == some 0xffffffffffffffffff0000ffffffffff#128
#guard vrun 0 (.add .b16 .v0 .v1 .v2) == some 0xf2d4933faa015a8433e363edd52d2be9#128
#guard vrun 0 (.sub .b16 .v0 .v1 .v2) == some 0xbc2085299e6b18eaa1357d97d74f0f45#128
#guard vrun 0 (.cmeq .s4 .v0 .v1 .v3) == some 0xffffffffffffffff00000000ffffffff#128
#guard vrun 0 (.cmeq .d2 .v0 .v1 .v3) == some 0xffffffffffffffff0000000000000000#128
#guard vrun 0 (.cmeq .b16 .v0 .v0 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.bsel .bsl .v0 .v1 .v2) == some 0x1b5a8ca824b3391fc9ccf0237e7e0f93#128
#guard vrun 0 (.bsel .bsl .v0 .v0 .v2) == some 0x1b5bcfebeffb7fdfdddfffbf7f7fcfdb#128
#guard vrun 0 (.bsel .bit .v0 .v1 .v2) == some 0x135b4ce06db27f97dc0cfc16563ecd9b#128
#guard vrun 0 (.bsel .bit .v0 .v0 .v2) == some 0x01434be3ebf87ed69c1bbf9c0735c9c9#128
#guard vrun 0 (.bsel .bif .v0 .v1 .v2) == some 0xc5620bb7a2fc3876aa1bb3c807b519c5#128
#guard vrun 0 (.bsel .bif .v0 .v0 .v2) == some 0x01434be3ebf87ed69c1bbf9c0735c9c9#128
#guard vrun 0 (.shift .sshr .b16 .v0 .v6 1) == some 0x0fe41e0de5f3cf20fc37fbf93039140d#128
#guard vrun 0 (.shift .sshr .b16 .v0 .v6 3) == some 0x03f90703f9fcf308ff0dfefe0c0e0503#128
#guard vrun 0 (.shift .sshr .b16 .v0 .v6 8) == some 0x00ff0000ffffff00ff00ffff00000000#128
#guard vrun 0 (.shift .sshr .s4 .v0 .v6 1) == some 0x0fe49e8de5734f20fc377b793039140d#128
#guard vrun 0 (.shift .sshr .s4 .v0 .v6 7) == some 0x003f927aff95cd3cfff0dded00c0e450#128
#guard vrun 0 (.shift .sshr .s4 .v0 .v6 32) == some 0x00000000ffffffffffffffff00000000#128
#guard vrun 0 (.shift .sshr .d2 .v0 .v6 1) == some 0x0fe49e8de5734f20fc377b79b039140d#128
#guard vrun 0 (.shift .sshr .d2 .v0 .v6 31) == some 0x000000003f927a37fffffffff0ddede6#128
#guard vrun 0 (.shift .sshr .d2 .v0 .v6 63) == some 0x0000000000000000ffffffffffffffff#128
#guard vrun 0 (.shift .sshr .d2 .v0 .v6 64) == some 0x0000000000000000ffffffffffffffff#128
#guard vrun 0 (.shift .shl .b16 .v0 .v1 0) == some 0xd77a0cb424b63937ea0cf04256be1d97#128
#guard vrun 0 (.shift .shl .b16 .v0 .v1 3) == some 0xb8d060a020b0c8b850608010b0f0e8b8#128
#guard vrun 0 (.shift .shl .b16 .v0 .v1 7) == some 0x80000000000080800000000000008080#128
#guard vrun 0 (.shift .ushr .b16 .v0 .v1 1) == some 0x6b3d065a125b1c1b750678212b5f0e4b#128
#guard vrun 0 (.shift .ushr .b16 .v0 .v1 8) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.shift .sri .b16 .v0 .v1 3) == some 0x1a4f41f6e4f667c69d01be880a37c3d2#128
#guard vrun 0 (.shift .sli .b16 .v0 .v1 5) == some 0xe1438b838bd83ef65c9b1f5cc7d5a9e9#128
#guard vrun 0 (.perm .zip1 .b16 .v0 .v1 .v2) == some 0x49ead70c73f0ab427f566fbe0e1d5297#128
#guard vrun 0 (.perm .zip2 .b16 .v0 .v1 .v2) == some 0x1bd75a7a870c8bb486244bb621394d37#128
#guard vrun 0 (.perm .trn1 .b16 .v0 .v1 .v2) == some 0x5a7a8bb44bb64d37d70cab426fbe5297#128
#guard vrun 0 (.perm .trn2 .b16 .v0 .v1 .v2) == some 0x1bd7870c8624213949ea73f07f560e1d#128
#guard vrun 0 (.perm .uzp1 .b16 .v0 .v1 .v2) == some 0x5a8b4b4dd7ab6f527ab4b6370c42be97#128
#guard vrun 0 (.perm .uzp2 .b16 .v0 .v1 .v2) == some 0x1b87862149737f0ed70c2439eaf0561d#128
#guard vrun 0 (.tblN false 1 .v0 .v1 .v7) == some 0x420000d7000000000000000000000000#128
#guard vrun 0 (.tblN false 2 .v0 .v1 .v7) == some 0x420000d7491b002100006f0000005286#128
#guard vrun 0 (.tblN false 3 .v0 .v1 .v7) == some 0x420000d7491bea2100ea6f0037005286#128
#guard vrun 0 (.tblN false 4 .v0 .v1 .v7) == some 0x420000d7491bea2100ea6f9e37005286#128
#guard vrun 0 (.tblN false 4 .v0 .v30 .v7) == some 0x470000209e0e9c89009ce656d6001982#128
#guard vrun 0 (.tblN false 2 .v0 .v0 .v7) == some 0x9c000001ead700390000be0000009724#128
#guard vrun 0 (.tblN false 1 .v7 .v1 .v7) .v7 == some 0x420000d7000000000000000000000000#128
#guard vrun 0 (.tblN true 1 .v0 .v1 .v7) == some 0x42434bd7ebf87ed69c1bbf9c0735c9c9#128
#guard vrun 0 (.tblN true 2 .v0 .v1 .v7) == some 0x42434bd7491b7e219c1b6f9c07355286#128
#guard vrun 0 (.tblN true 3 .v0 .v1 .v7) == some 0x42434bd7491bea219cea6f9c37355286#128
#guard vrun 0 (.tblN true 4 .v0 .v1 .v7) == some 0x42434bd7491bea219cea6f9e37355286#128
#guard vrun 0 (.tblN true 4 .v0 .v30 .v7) == some 0x47434b209e0e9c899c9ce656d6351982#128
#guard vrun 0 (.tblN true 2 .v0 .v0 .v7) == some 0x9c434b01ead77e399c1bbe9c07359724#128
#guard vrun 0 (.tblN true 1 .v7 .v1 .v7) .v7 == some 0x424542d7171f2719422712332842101b#128

#guard vrun 1 (.dupE .b16 .v0 .v1 0) == some 0x2d2d2d2d2d2d2d2d2d2d2d2d2d2d2d2d#128
#guard vrun 1 (.dupE .b16 .v0 .v1 5) == some 0x65656565656565656565656565656565#128
#guard vrun 1 (.dupE .b16 .v0 .v1 15) == some 0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0#128
#guard vrun 1 (.dupE .s4 .v0 .v1 2) == some 0xf85a7d5df85a7d5df85a7d5df85a7d5d#128
#guard vrun 1 (.dupE .d2 .v0 .v1 1) == some 0xd07d4e60f85a7d5dd07d4e60f85a7d5d#128
#guard vrun 1 (.dupE .b16 .v0 .v0 9) == some 0x59595959595959595959595959595959#128
#guard vrun 1 (.insE .b16 .v0 3 .v1 12) == some 0x6c9795af2d54593abfa72e0e604dc28b#128
#guard vrun 1 (.insE .b16 .v0 0 .v1 0) == some 0x6c9795af2d54593abfa72e0e834dc22d#128
#guard vrun 1 (.insE .b16 .v0 15 .v1 7) == some 0x4e9795af2d54593abfa72e0e834dc28b#128
#guard vrun 1 (.insE .b16 .v0 2 .v0 14) == some 0x6c9795af2d54593abfa72e0e8397c28b#128
#guard vrun 1 (.insE .s4 .v0 1 .v1 3) == some 0x6c9795af2d54593ad07d4e60834dc28b#128
#guard vrun 1 (.insE .d2 .v0 0 .v1 1) == some 0x6c9795af2d54593ad07d4e60f85a7d5d#128
#guard vrun 1 (.dup .b16 .v0 .x1) == some 0xb2b2b2b2b2b2b2b2b2b2b2b2b2b2b2b2#128
#guard vrun 1 (.ins .b16 .v0 0 .x1) == some 0x6c9795af2d54593abfa72e0e834dc2b2#128
#guard vrun 1 (.ins .b16 .v0 6 .x1) == some 0x6c9795af2d54593abfb22e0e834dc28b#128
#guard vrun 1 (.ins .b16 .v0 15 .x1) == some 0xb29795af2d54593abfa72e0e834dc28b#128
#guard vrun 1 (.cmeq .b16 .v0 .v1 .v3) == some 0xffff00ffff0000ffffffffffff00ffff#128
#guard vrun 1 (.add .b16 .v0 .v1 .v2) == some 0x81da30d3e46b9d8255be17efc49d4e4d#128
#guard vrun 1 (.sub .b16 .v0 .v1 .v2) == some 0x1f206ced0c495d3847d4b33740b7c60d#128
#guard vrun 1 (.cmeq .s4 .v0 .v1 .v3) == some 0x0000000000000000ffffffff00000000#128
#guard vrun 1 (.cmeq .d2 .v0 .v1 .v3) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.cmeq .b16 .v0 .v0 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.bsel .bsl .v0 .v1 .v2) == some 0xd15d6670e851791d0ed1b4d2423a0629#128
#guard vrun 1 (.bsel .bsl .v0 .v0 .v2) == some 0xfddff7ffed55793fbff7bedec37fc6ab#128
#guard vrun 1 (.bsel .bit .v0 .v1 .v2) == some 0xdcdf57ece954791fbec32c12032e82ab#128
#guard vrun 1 (.bsel .bit .v0 .v0 .v2) == some 0x6c9795af2d54593abfa72e0e834dc28b#128
#guard vrun 1 (.bsel .bif .v0 .v1 .v2) == some 0x60358c233c5a5d784fad670f82494a0d#128
#guard vrun 1 (.bsel .bif .v0 .v0 .v2) == some 0x6c9795af2d54593abfa72e0e834dc28b#128
#guard vrun 1 (.shift .sshr .b16 .v0 .v6 1) == some 0xe3ecc5d43ffcecccd3010edd0b3acf34#128
#guard vrun 1 (.shift .sshr .b16 .v0 .v6 3) == some 0xf8fbf1f50ffffbf3f40003f7020ef30d#128
#guard vrun 1 (.shift .sshr .b16 .v0 .v6 8) == some 0xffffffff00ffffffff0000ff0000ff00#128
#guard vrun 1 (.shift .sshr .s4 .v0 .v6 1) == some 0xe36cc5543ffcecccd3010edd0bba4f34#128
#guard vrun 1 (.shift .sshr .s4 .v0 .v6 7) == some 0xff8db31500fff3b3ff4c043b002ee93c#128
#guard vrun 1 (.shift .sshr .s4 .v0 .v6 32) == some 0xffffffff00000000ffffffff00000000#128
#guard vrun 1 (.shift .sshr .d2 .v0 .v6 1) == some 0xe36cc554bffcecccd3010edd0bba4f34#128
#guard vrun 1 (.shift .sshr .d2 .v0 .v6 31) == some 0xffffffff8db31552ffffffff4c043b74#128
#guard vrun 1 (.shift .sshr .d2 .v0 .v6 63) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.shift .sshr .d2 .v0 .v6 64) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.shift .shl .b16 .v0 .v1 0) == some 0xd07d4e60f85a7d5d4ec96513022a0a2d#128
#guard vrun 1 (.shift .shl .b16 .v0 .v1 3) == some 0x80e87000c0d0e8e87048289810505068#128
#guard vrun 1 (.shift .shl .b16 .v0 .v1 7) == some 0x00800000000080800080808000000080#128
#guard vrun 1 (.shift .ushr .b16 .v0 .v1 1) == some 0x683e27307c2d3e2e2764320901150516#128
#guard vrun 1 (.shift .ushr .b16 .v0 .v1 8) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.shift .sri .b16 .v0 .v1 3) == some 0x7a8f89ac3f4b4f2ba9b92c028045c185#128
#guard vrun 1 (.shift .sli .b16 .v0 .v1 5) == some 0x0cb7d50f0d54b9badf27ae6e434d42ab#128
#guard vrun 1 (.perm .zip1 .b16 .v0 .v1 .v2) == some 0x074ef5c9b265dc13c202732a440a202d#128
#guard vrun 1 (.perm .zip2 .b16 .v0 .v1 .v2) == some 0xb1d05d7de24e7360ecf8115a207d255d#128
#guard vrun 1 (.perm .trn1 .b16 .v0 .v1 .v2) == some 0x5d7d7360115a255df5c9dc13732a202d#128
#guard vrun 1 (.perm .trn2 .b16 .v0 .v1 .v2) == some 0xb1d0e24eecf8207d074eb265c202440a#128
#guard vrun 1 (.perm .uzp1 .b16 .v0 .v1 .v2) == some 0x5d731125f5dc73207d605a5dc9132a2d#128
#guard vrun 1 (.perm .uzp2 .b16 .v0 .v1 .v2) == some 0xb1e2ec2007b2c244d04ef87d4e65020a#128
#guard vrun 1 (.tblN false 1 .v0 .v1 .v7) == some 0x0000000000000000004e000000005a00#128
#guard vrun 1 (.tblN false 2 .v0 .v1 .v7) == some 0x44000007205d0000b14e200000005a07#128
#guard vrun 1 (.tblN false 3 .v0 .v1 .v7) == some 0x4413bc07205d66ddb14e200000005a07#128
#guard vrun 1 (.tblN false 4 .v0 .v1 .v7) == some 0x4413bc07205d66ddb14e207ac9005a07#128
#guard vrun 1 (.tblN false 4 .v0 .v30 .v7) == some 0x9e0e5980c2809554bebfc27d2a007480#128
#guard vrun 1 (.tblN false 2 .v0 .v0 .v7) == some 0x0a00004e7d7d0000d0bf7d000000544e#128
#guard vrun 1 (.tblN false 1 .v7 .v1 .v7) .v7 == some 0x0000000000000000004e000000005a00#128
#guard vrun 1 (.tblN true 1 .v0 .v1 .v7) == some 0x6c9795af2d54593abf4e2e0e834d5a8b#128
#guard vrun 1 (.tblN true 2 .v0 .v1 .v7) == some 0x44979507205d593ab14e200e834d5a07#128
#guard vrun 1 (.tblN true 3 .v0 .v1 .v7) == some 0x4413bc07205d66ddb14e200e834d5a07#128
#guard vrun 1 (.tblN true 4 .v0 .v1 .v7) == some 0x4413bc07205d66ddb14e207ac94d5a07#128
#guard vrun 1 (.tblN true 4 .v0 .v30 .v7) == some 0x9e0e5980c2809554bebfc27d2a4d7480#128
#guard vrun 1 (.tblN true 2 .v0 .v0 .v7) == some 0x0a97954e7d7d593ad0bf7d0e834d544e#128
#guard vrun 1 (.tblN true 1 .v7 .v1 .v7) .v7 == some 0x11242917191e2d2a1f4e193e32425a17#128

-- The printed syntax, which the expected values were computed with.
#guard printer.instr (.vop (.dupE .b16 .v0 .v1 0)) == ["dup v0.16b, v1.b[0]"]
#guard printer.instr (.vop (.dupE .b16 .v0 .v1 5)) == ["dup v0.16b, v1.b[5]"]
#guard printer.instr (.vop (.dupE .b16 .v0 .v1 15)) == ["dup v0.16b, v1.b[15]"]
#guard printer.instr (.vop (.dupE .s4 .v0 .v1 2)) == ["dup v0.4s, v1.s[2]"]
#guard printer.instr (.vop (.dupE .d2 .v0 .v1 1)) == ["dup v0.2d, v1.d[1]"]
#guard printer.instr (.vop (.dupE .b16 .v0 .v0 9)) == ["dup v0.16b, v0.b[9]"]
#guard printer.instr (.vop (.insE .b16 .v0 3 .v1 12)) == ["mov v0.b[3], v1.b[12]"]
#guard printer.instr (.vop (.insE .b16 .v0 0 .v1 0)) == ["mov v0.b[0], v1.b[0]"]
#guard printer.instr (.vop (.insE .b16 .v0 15 .v1 7)) == ["mov v0.b[15], v1.b[7]"]
#guard printer.instr (.vop (.insE .b16 .v0 2 .v0 14)) == ["mov v0.b[2], v0.b[14]"]
#guard printer.instr (.vop (.insE .s4 .v0 1 .v1 3)) == ["mov v0.s[1], v1.s[3]"]
#guard printer.instr (.vop (.insE .d2 .v0 0 .v1 1)) == ["mov v0.d[0], v1.d[1]"]
#guard printer.instr (.vop (.dup .b16 .v0 .x1)) == ["dup v0.16b, w1"]
#guard printer.instr (.vop (.ins .b16 .v0 0 .x1)) == ["mov v0.b[0], w1"]
#guard printer.instr (.vop (.ins .b16 .v0 6 .x1)) == ["mov v0.b[6], w1"]
#guard printer.instr (.vop (.ins .b16 .v0 15 .x1)) == ["mov v0.b[15], w1"]
#guard printer.instr (.vop (.cmeq .b16 .v0 .v1 .v3)) == ["cmeq v0.16b, v1.16b, v3.16b"]
#guard printer.instr (.vop (.add .b16 .v0 .v1 .v2)) == ["add v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.sub .b16 .v0 .v1 .v2)) == ["sub v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.cmeq .s4 .v0 .v1 .v3)) == ["cmeq v0.4s, v1.4s, v3.4s"]
#guard printer.instr (.vop (.cmeq .d2 .v0 .v1 .v3)) == ["cmeq v0.2d, v1.2d, v3.2d"]
#guard printer.instr (.vop (.cmeq .b16 .v0 .v0 .v1)) == ["cmeq v0.16b, v0.16b, v1.16b"]
#guard printer.instr (.vop (.bsel .bsl .v0 .v1 .v2)) == ["bsl v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.bsel .bsl .v0 .v0 .v2)) == ["bsl v0.16b, v0.16b, v2.16b"]
#guard printer.instr (.vop (.bsel .bit .v0 .v1 .v2)) == ["bit v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.bsel .bit .v0 .v0 .v2)) == ["bit v0.16b, v0.16b, v2.16b"]
#guard printer.instr (.vop (.bsel .bif .v0 .v1 .v2)) == ["bif v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.bsel .bif .v0 .v0 .v2)) == ["bif v0.16b, v0.16b, v2.16b"]
#guard printer.instr (.vop (.shift .sshr .b16 .v0 .v6 1)) == ["sshr v0.16b, v6.16b, #1"]
#guard printer.instr (.vop (.shift .sshr .b16 .v0 .v6 3)) == ["sshr v0.16b, v6.16b, #3"]
#guard printer.instr (.vop (.shift .sshr .b16 .v0 .v6 8)) == ["sshr v0.16b, v6.16b, #8"]
#guard printer.instr (.vop (.shift .sshr .s4 .v0 .v6 1)) == ["sshr v0.4s, v6.4s, #1"]
#guard printer.instr (.vop (.shift .sshr .s4 .v0 .v6 7)) == ["sshr v0.4s, v6.4s, #7"]
#guard printer.instr (.vop (.shift .sshr .s4 .v0 .v6 32)) == ["sshr v0.4s, v6.4s, #32"]
#guard printer.instr (.vop (.shift .sshr .d2 .v0 .v6 1)) == ["sshr v0.2d, v6.2d, #1"]
#guard printer.instr (.vop (.shift .sshr .d2 .v0 .v6 31)) == ["sshr v0.2d, v6.2d, #31"]
#guard printer.instr (.vop (.shift .sshr .d2 .v0 .v6 63)) == ["sshr v0.2d, v6.2d, #63"]
#guard printer.instr (.vop (.shift .sshr .d2 .v0 .v6 64)) == ["sshr v0.2d, v6.2d, #64"]
#guard printer.instr (.vop (.shift .shl .b16 .v0 .v1 0)) == ["shl v0.16b, v1.16b, #0"]
#guard printer.instr (.vop (.shift .shl .b16 .v0 .v1 3)) == ["shl v0.16b, v1.16b, #3"]
#guard printer.instr (.vop (.shift .shl .b16 .v0 .v1 7)) == ["shl v0.16b, v1.16b, #7"]
#guard printer.instr (.vop (.shift .ushr .b16 .v0 .v1 1)) == ["ushr v0.16b, v1.16b, #1"]
#guard printer.instr (.vop (.shift .ushr .b16 .v0 .v1 8)) == ["ushr v0.16b, v1.16b, #8"]
#guard printer.instr (.vop (.shift .sri .b16 .v0 .v1 3)) == ["sri v0.16b, v1.16b, #3"]
#guard printer.instr (.vop (.shift .sli .b16 .v0 .v1 5)) == ["sli v0.16b, v1.16b, #5"]
#guard printer.instr (.vop (.perm .zip1 .b16 .v0 .v1 .v2)) == ["zip1 v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.perm .zip2 .b16 .v0 .v1 .v2)) == ["zip2 v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.perm .trn1 .b16 .v0 .v1 .v2)) == ["trn1 v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.perm .trn2 .b16 .v0 .v1 .v2)) == ["trn2 v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.perm .uzp1 .b16 .v0 .v1 .v2)) == ["uzp1 v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.perm .uzp2 .b16 .v0 .v1 .v2)) == ["uzp2 v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.tblN false 1 .v0 .v1 .v7)) == ["tbl v0.16b, {v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN false 2 .v0 .v1 .v7)) == ["tbl v0.16b, {v1.16b, v2.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN false 3 .v0 .v1 .v7)) == ["tbl v0.16b, {v1.16b, v2.16b, v3.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN false 4 .v0 .v1 .v7)) == ["tbl v0.16b, {v1.16b, v2.16b, v3.16b, v4.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN false 4 .v0 .v30 .v7)) == ["tbl v0.16b, {v30.16b, v31.16b, v0.16b, v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN false 2 .v0 .v0 .v7)) == ["tbl v0.16b, {v0.16b, v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN false 1 .v7 .v1 .v7)) == ["tbl v7.16b, {v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 1 .v0 .v1 .v7)) == ["tbx v0.16b, {v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 2 .v0 .v1 .v7)) == ["tbx v0.16b, {v1.16b, v2.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 3 .v0 .v1 .v7)) == ["tbx v0.16b, {v1.16b, v2.16b, v3.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 4 .v0 .v1 .v7)) == ["tbx v0.16b, {v1.16b, v2.16b, v3.16b, v4.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 4 .v0 .v30 .v7)) == ["tbx v0.16b, {v30.16b, v31.16b, v0.16b, v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 2 .v0 .v0 .v7)) == ["tbx v0.16b, {v0.16b, v1.16b}, v7.16b"]
#guard printer.instr (.vop (.tblN true 1 .v7 .v1 .v7)) == ["tbx v7.16b, {v1.16b}, v7.16b"]

-- Immediates out of range fault.
#guard vrun 0 (.dupE .b16 .v0 .v1 16) == none
#guard vrun 0 (.dupE .s4 .v0 .v1 4) == none
#guard vrun 0 (.dupE .d2 .v0 .v1 2) == none
#guard vrun 0 (.insE .b16 .v0 16 .v1 0) == none
#guard vrun 0 (.insE .b16 .v0 0 .v1 16) == none
#guard vrun 0 (.insE .d2 .v0 0 .v1 2) == none
#guard vrun 0 (.ins .b16 .v0 16 .x1) == none
#guard vrun 0 (.shift .sshr .b16 .v0 .v6 0) == none
#guard vrun 0 (.shift .sshr .b16 .v0 .v6 9) == none
#guard vrun 0 (.shift .sshr .d2 .v0 .v6 65) == none
#guard vrun 0 (.shift .shl .b16 .v0 .v1 8) == none
#guard vrun 0 (.tblN false 0 .v0 .v1 .v7) == none
#guard vrun 0 (.tblN true 5 .v0 .v1 .v7) == none

-- None of them needs a CPU feature beyond the baseline.
#guard isa.requires (.vop (.dupE .b16 .v0 .v1 0)) == []
#guard isa.requires (.vop (.insE .b16 .v0 0 .v1 0)) == []
#guard isa.requires (.vop (.cmeq .b16 .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.bsel .bit .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.shift .sshr .d2 .v0 .v1 1)) == []
#guard isa.requires (.vop (.tblN true 4 .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.dup .b16 .v0 .x1)) == []
#guard isa.requires (.vop (.add .b16 .v0 .v1 .v2)) == []

end VG.Test.AArch64SimdBytes
