import VerifiedGarbage.TCB.AArch64.Print

/-!
# Semantics tests for the AArch64 AdvSIMD and cryptographic instructions

Each expected value was computed by the same instruction, in inline assembly
exactly as the printer prints it (checked below), in a program
cross-compiled with `aarch64-linux-gnu-gcc -march=armv8.4-a+crypto+sha3`
and run under `qemu-aarch64 -cpu max`'s emulation of an AArch64 CPU with
every feature, not on Arm hardware. Before each instruction the program
loaded `v0`–`v3`, `x1` and `x0` from the inputs below (the pseudorandom
values of a fixed seed; `v3`'s bytes are below 32, so that `tbl` sees
indices both inside and outside its table) and `0xdeadbeefdeadbeef`, and
afterwards stored `v0` (or `x0`, for `umov`). The instructions include forms
whose destination is also a source. This tests the transcription of the Arm
ARM's pseudocode (which lane is which, the operand roles of the SHA
instructions, the zeroing by a scalar write), which review of the TCB would
otherwise have to catch by eye.
-/

namespace VG.Test.AArch64Simd

open AArch64

/-- The inputs: `v0`, `v1`, `v2`, `v3`, `x1` for each of the two runs. -/
def input0 : BitVec 128 × BitVec 128 × BitVec 128 × BitVec 128 × BitVec 64 :=
  (0x47be5543e684460b8caafc59aff91663#128, 0xd5b39162c1984cc4c9c6de1db050fcb1#128,
    0x183bb3b2f27fe16536ca734e082da43c#128, 0x1e0f01110c03061910011d02150c161c#128, 0x9696613da12809ec#64)
def input1 : BitVec 128 × BitVec 128 × BitVec 128 × BitVec 128 × BitVec 64 :=
  (0x55eadb18f6d1d81649d2bf3ef06dbe6f#128, 0xdb26ce183543c96b9f9eb90b2c4563c4#128,
    0x384a612f2df0168eeee920eaf4a28fec#128, 0x1b1b1e000f0e031600001b10160a0f06#128, 0xd55f2bbb042e967b#64)

/-- The inputs of run `k`. -/
def input (k : Nat) : BitVec 128 × BitVec 128 × BitVec 128 × BitVec 128 × BitVec 64 :=
  if k = 0 then input0 else input1

/-- The state before run `k`: its inputs in `v0`–`v3` and `x1`,
`0xdeadbeefdeadbeef` in `x0`, and 32 bytes `17 i + 3` at `0x100`, readable
and writable. -/
def s (k : Nat) : State :=
  let (a, b, c, d, g) := input k
  { gpr := fun r => if r = .x1 then g else if r = .x2 then 0x100 else 0xdeadbeefdeadbeef
    sp := 0x1000
    v := fun r => if r = .v0 then a else if r = .v1 then b else if r = .v2 then c
      else if r = .v3 then d else 0
    mem := fun addr => if 0x100 ≤ addr.toNat ∧ addr.toNat < 0x120 then
      BitVec.ofNat 8 (17 * (addr.toNat - 0x100) + 3) else 0
    rd := []
    wr := [⟨0x100, 32⟩] }

/-- `v0` after `op` in run `k`. -/
def vrun (k : Nat) (op : VOp) : Option (BitVec 128) := (exec (.vop op) (s k)).map (·.v .v0)

/-- `x0` after `i` in run `k`. -/
def xrun (k : Nat) (i : Instr) : Option (BitVec 64) := (exec i (s k)).map (·.gpr .x0)

#guard vrun 0 (.mov .v0 .v1) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.movi0 .v0) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.dup .s4 .v0 .x1) == some 0xa12809eca12809eca12809eca12809ec#128
#guard vrun 0 (.dup .d2 .v0 .x1) == some 0x9696613da12809ec9696613da12809ec#128
#guard vrun 0 (.ins .s4 .v0 0 .x1) == some 0x47be5543e684460b8caafc59a12809ec#128
#guard vrun 0 (.ins .s4 .v0 1 .x1) == some 0x47be5543e684460ba12809ecaff91663#128
#guard vrun 0 (.ins .s4 .v0 2 .x1) == some 0x47be5543a12809ec8caafc59aff91663#128
#guard vrun 0 (.ins .s4 .v0 3 .x1) == some 0xa12809ece684460b8caafc59aff91663#128
#guard vrun 0 (.ins .d2 .v0 0 .x1) == some 0x47be5543e684460b9696613da12809ec#128
#guard vrun 0 (.ins .d2 .v0 1 .x1) == some 0x9696613da12809ec8caafc59aff91663#128
#guard vrun 0 (.dupS .v0 .v1 0) == some 0x000000000000000000000000b050fcb1#128
#guard vrun 0 (.dupS .v0 .v1 1) == some 0x000000000000000000000000c9c6de1d#128
#guard vrun 0 (.dupS .v0 .v1 2) == some 0x000000000000000000000000c1984cc4#128
#guard vrun 0 (.dupS .v0 .v1 3) == some 0x000000000000000000000000d5b39162#128
#guard vrun 0 (.logic .and .v0 .v1 .v2) == some 0x10339122c018404400c2520c0000a430#128
#guard vrun 0 (.logic .orr .v0 .v1 .v2) == some 0xddbbb3f2f3ffede5ffceff5fb87dfcbd#128
#guard vrun 0 (.logic .eor .v0 .v1 .v2) == some 0xcd8822d033e7ada1ff0cad53b87d588d#128
#guard vrun 0 (.logic .bic .v0 .v1 .v2) == some 0xc580004001800c80c9048c11b0505881#128
#guard vrun 0 (.logic .orn .v0 .v1 .v2) == some 0xf7f7dd6fcd985edec9f7debdf7d2fff3#128
#guard vrun 0 (.not .v0 .v1) == some 0x2a4c6e9d3e67b33b363921e24faf034e#128
#guard vrun 0 (.add .s4 .v0 .v1 .v2) == some 0xedef4514b4182e290091516bb87ea0ed#128
#guard vrun 0 (.sub .s4 .v0 .v1 .v2) == some 0xbd77ddb0cf186b5f92fc6acfa8235875#128
#guard vrun 0 (.shift .shl .s4 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .shl .s4 .v0 .v1 7) == some 0xd9c8b100cc266200e36f0e80287e5880#128
#guard vrun 0 (.shift .shl .s4 .v0 .v1 31) == some 0x00000000000000008000000080000000#128
#guard vrun 0 (.shift .sli .s4 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .sli .s4 .v0 .v1 7) == some 0xd9c8b143cc26620be36f0ed9287e58e3#128
#guard vrun 0 (.shift .sli .s4 .v0 .v1 31) == some 0x47be55436684460b8caafc59aff91663#128
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 1) == some 0x6ad9c8b160cc266264e36f0e58287e58#128
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 13) == some 0x0006ad9c00060cc200064e3600058287#128
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 32) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.shift .sri .s4 .v0 .v1 1) == some 0x6ad9c8b1e0cc2662e4e36f0ed8287e58#128
#guard vrun 0 (.shift .sri .s4 .v0 .v1 13) == some 0x47bead9ce6860cc28cae4e36affd8287#128
#guard vrun 0 (.shift .sri .s4 .v0 .v1 32) == some 0x47be5543e684460b8caafc59aff91663#128
#guard vrun 0 (.perm .zip1 .s4 .v0 .v1 .v2) == some 0x36ca734ec9c6de1d082da43cb050fcb1#128
#guard vrun 0 (.perm .zip2 .s4 .v0 .v1 .v2) == some 0x183bb3b2d5b39162f27fe165c1984cc4#128
#guard vrun 0 (.perm .trn1 .s4 .v0 .v1 .v2) == some 0xf27fe165c1984cc4082da43cb050fcb1#128
#guard vrun 0 (.perm .trn2 .s4 .v0 .v1 .v2) == some 0x183bb3b2d5b3916236ca734ec9c6de1d#128
#guard vrun 0 (.perm .uzp1 .s4 .v0 .v1 .v2) == some 0xf27fe165082da43cc1984cc4b050fcb1#128
#guard vrun 0 (.perm .uzp2 .s4 .v0 .v1 .v2) == some 0x183bb3b236ca734ed5b39162c9c6de1d#128
#guard vrun 0 (.add .d2 .v0 .v1 .v2) == some 0xedef4515b4182e290091516bb87ea0ed#128
#guard vrun 0 (.sub .d2 .v0 .v1 .v2) == some 0xbd77ddafcf186b5f92fc6acfa8235875#128
#guard vrun 0 (.shift .shl .d2 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .shl .d2 .v0 .v1 7) == some 0xd9c8b160cc266200e36f0ed8287e5880#128
#guard vrun 0 (.shift .shl .d2 .v0 .v1 63) == some 0x00000000000000008000000000000000#128
#guard vrun 0 (.shift .sli .d2 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .sli .d2 .v0 .v1 7) == some 0xd9c8b160cc26620be36f0ed8287e58e3#128
#guard vrun 0 (.shift .sli .d2 .v0 .v1 63) == some 0x47be5543e684460b8caafc59aff91663#128
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 1) == some 0x6ad9c8b160cc266264e36f0ed8287e58#128
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 13) == some 0x0006ad9c8b160cc200064e36f0ed8287#128
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 64) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.shift .sri .d2 .v0 .v1 1) == some 0x6ad9c8b160cc2662e4e36f0ed8287e58#128
#guard vrun 0 (.shift .sri .d2 .v0 .v1 13) == some 0x47bead9c8b160cc28cae4e36f0ed8287#128
#guard vrun 0 (.shift .sri .d2 .v0 .v1 64) == some 0x47be5543e684460b8caafc59aff91663#128
#guard vrun 0 (.perm .zip1 .d2 .v0 .v1 .v2) == some 0x36ca734e082da43cc9c6de1db050fcb1#128
#guard vrun 0 (.perm .zip2 .d2 .v0 .v1 .v2) == some 0x183bb3b2f27fe165d5b39162c1984cc4#128
#guard vrun 0 (.perm .trn1 .d2 .v0 .v1 .v2) == some 0x36ca734e082da43cc9c6de1db050fcb1#128
#guard vrun 0 (.perm .trn2 .d2 .v0 .v1 .v2) == some 0x183bb3b2f27fe165d5b39162c1984cc4#128
#guard vrun 0 (.perm .uzp1 .d2 .v0 .v1 .v2) == some 0x36ca734e082da43cc9c6de1db050fcb1#128
#guard vrun 0 (.perm .uzp2 .d2 .v0 .v1 .v2) == some 0x183bb3b2f27fe165d5b39162c1984cc4#128
#guard vrun 0 (.ext .v0 .v1 .v2 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.ext .v0 .v1 .v2 1) == some 0x3cd5b39162c1984cc4c9c6de1db050fc#128
#guard vrun 0 (.ext .v0 .v1 .v2 8) == some 0x36ca734e082da43cd5b39162c1984cc4#128
#guard vrun 0 (.ext .v0 .v1 .v2 15) == some 0x3bb3b2f27fe16536ca734e082da43cd5#128
#guard vrun 0 (.rev .rev32b .v0 .v1) == some 0x6291b3d5c44c98c11ddec6c9b1fc50b0#128
#guard vrun 0 (.rev .rev32h .v0 .v1) == some 0x9162d5b34cc4c198de1dc9c6fcb1b050#128
#guard vrun 0 (.rev .rev64b .v0 .v1) == some 0xc44c98c16291b3d5b1fc50b01ddec6c9#128
#guard vrun 0 (.rev .rev64s .v0 .v1) == some 0xc1984cc4d5b39162b050fcb1c9c6de1d#128
#guard vrun 0 (.tbl .v0 .v1 .v3) == some 0x00d5fc0062b0c60000fc005000620000#128
#guard vrun 0 (.umull false .v0 .v1 .v2) == some 0x2b2f84a73140b3d605a1f73f27f99d7c#128
#guard vrun 0 (.umull true .v0 .v1 .v2) == some 0x143aac04d7189c24b762ad9299ca8d54#128
#guard vrun 0 (.umlal false .v0 .v1 .v2) == some 0x72edd9eb17c4f9e1924cf398d7f2b3df#128
#guard vrun 0 (.umlal true .v0 .v1 .v2) == some 0x5bf90148bd9ce22f440da9ec49c3a3b7#128
#guard vrun 0 (.pmull false .v0 .v1 .v2) == some 0x1741493c224e681a0d98ad159b352e7c#128
#guard vrun 0 (.pmull true .v0 .v1 .v2) == some 0x0be6e7a8b9d9791a2b96e51a9bd89254#128
#guard vrun 0 (.aese .v0 .v1) == some 0xcc5087fd6ed31c8ac0d7671b4f9c93b5#128
#guard vrun 0 (.aesd .v0 .v1) == some 0xcbb8a37b74b7945f3df3bb8668c4887f#128
#guard vrun 0 (.aesmc .v0 .v1) == some 0x35ea400a1afb2e1eb614224c1f261286#128
#guard vrun 0 (.aesimc .v0 .v1) == some 0xfa478fa7ca42fea7d06f44372b902630#128
#guard vrun 0 (.sha1 .c .v0 .v1 .v2) == some 0x5fcd6c9bb21adb1251afbde31d3b9ccc#128
#guard vrun 0 (.sha1 .p .v0 .v1 .v2) == some 0xf94c971cd3cb11a22c739fd66779019c#128
#guard vrun 0 (.sha1 .m .v0 .v1 .v2) == some 0x5f93f06bcc0a45104995757229d0755c#128
#guard vrun 0 (.sha1h .v0 .v1) == some 0x0000000000000000000000006c143f2c#128
#guard vrun 0 (.sha1su0 .v0 .v1 .v2) == some 0x964338eca4ab5bdffddeda544150f454#128
#guard vrun 0 (.sha1su1 .v0 .v1) == some 0x17838b7f666faed29a65613acc7f90fc#128
#guard vrun 0 (.sha256h .v0 .v1 .v2) == some 0x83962e62fc642832bcc84a4e5b935e68#128
#guard vrun 0 (.sha256h2 .v0 .v1 .v2) == some 0xb08d09d6b223c9462ac54347417efecc#128
#guard vrun 0 (.sha256su0 .v0 .v1) == some 0x920527be01acadf8a74a7645cd937fbc#128
#guard vrun 0 (.sha256su1 .v0 .v1 .v2) == some 0x24c0f3e8fb3ca2bbfdec8b138662cd08#128
#guard vrun 0 (.sha512h .v0 .v1 .v2) == some 0xb9f500a529009b652f1de5e624404ede#128
#guard vrun 0 (.sha512h2 .v0 .v1 .v2) == some 0xfd4ab9e6b07a67152fcdcc94e07ca0f9#128
#guard vrun 0 (.sha512su0 .v0 .v1) == some 0x9c7779b0e57cd56834c2e4b7e762c632#128
#guard vrun 0 (.sha512su1 .v0 .v1 .v2) == some 0x074ce8dcceec869615fd4254e7abcb15#128
#guard vrun 0 (.eor3 .v0 .v1 .v2 .v3) == some 0xd38723c13fe4abb8ef0db051ad714e91#128
#guard vrun 0 (.bcax .v0 .v1 .v2 .v3) == some 0xd58323c033e4ada0ef0cbc51b8715c91#128
#guard vrun 0 (.rax1 .v0 .v1 .v2) == some 0xe5c4f60725678e0ea4523881a00bb4c9#128
#guard vrun 0 (.xar .v0 .v1 .v2 0) == some 0xcd8822d033e7ada1ff0cad53b87d588d#128
#guard vrun 0 (.xar .v0 .v1 .v2 1) == some 0xe6c4116819f3d6d0ff8656a9dc3eac46#128
#guard vrun 0 (.xar .v0 .v1 .v2 63) == some 0x9b1045a067cf5b43fe195aa770fab11b#128
#guard vrun 0 (.add .s4 .v0 .v0 .v0) == some 0x8f7caa86cd088c161955f8b25ff22cc6#128
#guard vrun 0 (.ext .v0 .v0 .v1 4) == some 0xb050fcb147be5543e684460b8caafc59#128
#guard vrun 0 (.aese .v0 .v0) == some 0x63636363636363636363636363636363#128
#guard vrun 0 (.sha256h .v0 .v0 .v2) == some 0x463c83aefb3d02a472b6c7db002c5499#128
#guard vrun 0 (.sha256su1 .v0 .v0 .v0) == some 0x5717bdb8b6c4bc6253476721e8a1413f#128
#guard vrun 0 (.sha512h .v0 .v0 .v0) == some 0xf4c536bb530108a80bd37236a4cc101d#128
#guard vrun 0 (.tbl .v0 .v0 .v3) == some 0x0047160043afaa00001600f900430000#128
#guard vrun 0 (.umlal true .v0 .v0 .v0) == some 0x5bd97611bc5dd5945c3cee8dc27b1adc#128
#guard vrun 0 (.eor3 .v0 .v0 .v1 .v0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard xrun 0 (.umov .w .x0 .v1 0) == some 0x00000000b050fcb1#64
#guard xrun 0 (.umov .w .x0 .v1 1) == some 0x00000000c9c6de1d#64
#guard xrun 0 (.umov .w .x0 .v1 2) == some 0x00000000c1984cc4#64
#guard xrun 0 (.umov .w .x0 .v1 3) == some 0x00000000d5b39162#64
#guard xrun 0 (.umov .x .x0 .v1 0) == some 0xc9c6de1db050fcb1#64
#guard xrun 0 (.umov .x .x0 .v1 1) == some 0xd5b39162c1984cc4#64
#guard vrun 1 (.mov .v0 .v1) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.movi0 .v0) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.dup .s4 .v0 .x1) == some 0x042e967b042e967b042e967b042e967b#128
#guard vrun 1 (.dup .d2 .v0 .x1) == some 0xd55f2bbb042e967bd55f2bbb042e967b#128
#guard vrun 1 (.ins .s4 .v0 0 .x1) == some 0x55eadb18f6d1d81649d2bf3e042e967b#128
#guard vrun 1 (.ins .s4 .v0 1 .x1) == some 0x55eadb18f6d1d816042e967bf06dbe6f#128
#guard vrun 1 (.ins .s4 .v0 2 .x1) == some 0x55eadb18042e967b49d2bf3ef06dbe6f#128
#guard vrun 1 (.ins .s4 .v0 3 .x1) == some 0x042e967bf6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.ins .d2 .v0 0 .x1) == some 0x55eadb18f6d1d816d55f2bbb042e967b#128
#guard vrun 1 (.ins .d2 .v0 1 .x1) == some 0xd55f2bbb042e967b49d2bf3ef06dbe6f#128
#guard vrun 1 (.dupS .v0 .v1 0) == some 0x0000000000000000000000002c4563c4#128
#guard vrun 1 (.dupS .v0 .v1 1) == some 0x0000000000000000000000009f9eb90b#128
#guard vrun 1 (.dupS .v0 .v1 2) == some 0x0000000000000000000000003543c96b#128
#guard vrun 1 (.dupS .v0 .v1 3) == some 0x000000000000000000000000db26ce18#128
#guard vrun 1 (.logic .and .v0 .v1 .v2) == some 0x180240082540000a8e88200a240003c4#128
#guard vrun 1 (.logic .orr .v0 .v1 .v2) == some 0xfb6eef3f3df3dfefffffb9ebfce7efec#128
#guard vrun 1 (.logic .eor .v0 .v1 .v2) == some 0xe36caf3718b3dfe5717799e1d8e7ec28#128
#guard vrun 1 (.logic .bic .v0 .v1 .v2) == some 0xc3248e101003c9611116990108456000#128
#guard vrun 1 (.logic .orn .v0 .v1 .v2) == some 0xdfb7ded8f74fe97b9f9eff1f2f5d73d7#128
#guard vrun 1 (.not .v0 .v1) == some 0x24d931e7cabc3694606146f4d3ba9c3b#128
#guard vrun 1 (.add .s4 .v0 .v1 .v2) == some 0x13712f476333dff98e87d9f520e7f3b0#128
#guard vrun 1 (.sub .s4 .v0 .v1 .v2) == some 0xa2dc6ce90753b2ddb0b5982137a2d3d8#128
#guard vrun 1 (.shift .shl .s4 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .shl .s4 .v0 .v1 7) == some 0x93670c00a1e4b580cf5c858022b1e200#128
#guard vrun 1 (.shift .shl .s4 .v0 .v1 31) == some 0x00000000800000008000000000000000#128
#guard vrun 1 (.shift .sli .s4 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .sli .s4 .v0 .v1 7) == some 0x93670c18a1e4b596cf5c85be22b1e26f#128
#guard vrun 1 (.shift .sli .s4 .v0 .v1 31) == some 0x55eadb18f6d1d816c9d2bf3e706dbe6f#128
#guard vrun 1 (.shift .ushr .s4 .v0 .v1 1) == some 0x6d93670c1aa1e4b54fcf5c851622b1e2#128
#guard vrun 1 (.shift .ushr .s4 .v0 .v1 13) == some 0x0006d9360001aa1e0004fcf50001622b#128
#guard vrun 1 (.shift .ushr .s4 .v0 .v1 32) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.shift .sri .s4 .v0 .v1 1) == some 0x6d93670c9aa1e4b54fcf5c859622b1e2#128
#guard vrun 1 (.shift .sri .s4 .v0 .v1 13) == some 0x55eed936f6d1aa1e49d4fcf5f069622b#128
#guard vrun 1 (.shift .sri .s4 .v0 .v1 32) == some 0x55eadb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.perm .zip1 .s4 .v0 .v1 .v2) == some 0xeee920ea9f9eb90bf4a28fec2c4563c4#128
#guard vrun 1 (.perm .zip2 .s4 .v0 .v1 .v2) == some 0x384a612fdb26ce182df0168e3543c96b#128
#guard vrun 1 (.perm .trn1 .s4 .v0 .v1 .v2) == some 0x2df0168e3543c96bf4a28fec2c4563c4#128
#guard vrun 1 (.perm .trn2 .s4 .v0 .v1 .v2) == some 0x384a612fdb26ce18eee920ea9f9eb90b#128
#guard vrun 1 (.perm .uzp1 .s4 .v0 .v1 .v2) == some 0x2df0168ef4a28fec3543c96b2c4563c4#128
#guard vrun 1 (.perm .uzp2 .s4 .v0 .v1 .v2) == some 0x384a612feee920eadb26ce189f9eb90b#128
#guard vrun 1 (.add .d2 .v0 .v1 .v2) == some 0x13712f476333dff98e87d9f620e7f3b0#128
#guard vrun 1 (.sub .d2 .v0 .v1 .v2) == some 0xa2dc6ce90753b2ddb0b5982037a2d3d8#128
#guard vrun 1 (.shift .shl .d2 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .shl .d2 .v0 .v1 7) == some 0x93670c1aa1e4b580cf5c859622b1e200#128
#guard vrun 1 (.shift .shl .d2 .v0 .v1 63) == some 0x80000000000000000000000000000000#128
#guard vrun 1 (.shift .sli .d2 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .sli .d2 .v0 .v1 7) == some 0x93670c1aa1e4b596cf5c859622b1e26f#128
#guard vrun 1 (.shift .sli .d2 .v0 .v1 63) == some 0xd5eadb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.shift .ushr .d2 .v0 .v1 1) == some 0x6d93670c1aa1e4b54fcf5c859622b1e2#128
#guard vrun 1 (.shift .ushr .d2 .v0 .v1 13) == some 0x0006d93670c1aa1e0004fcf5c859622b#128
#guard vrun 1 (.shift .ushr .d2 .v0 .v1 64) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.shift .sri .d2 .v0 .v1 1) == some 0x6d93670c1aa1e4b54fcf5c859622b1e2#128
#guard vrun 1 (.shift .sri .d2 .v0 .v1 13) == some 0x55eed93670c1aa1e49d4fcf5c859622b#128
#guard vrun 1 (.shift .sri .d2 .v0 .v1 64) == some 0x55eadb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.perm .zip1 .d2 .v0 .v1 .v2) == some 0xeee920eaf4a28fec9f9eb90b2c4563c4#128
#guard vrun 1 (.perm .zip2 .d2 .v0 .v1 .v2) == some 0x384a612f2df0168edb26ce183543c96b#128
#guard vrun 1 (.perm .trn1 .d2 .v0 .v1 .v2) == some 0xeee920eaf4a28fec9f9eb90b2c4563c4#128
#guard vrun 1 (.perm .trn2 .d2 .v0 .v1 .v2) == some 0x384a612f2df0168edb26ce183543c96b#128
#guard vrun 1 (.perm .uzp1 .d2 .v0 .v1 .v2) == some 0xeee920eaf4a28fec9f9eb90b2c4563c4#128
#guard vrun 1 (.perm .uzp2 .d2 .v0 .v1 .v2) == some 0x384a612f2df0168edb26ce183543c96b#128
#guard vrun 1 (.ext .v0 .v1 .v2 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.ext .v0 .v1 .v2 1) == some 0xecdb26ce183543c96b9f9eb90b2c4563#128
#guard vrun 1 (.ext .v0 .v1 .v2 8) == some 0xeee920eaf4a28fecdb26ce183543c96b#128
#guard vrun 1 (.ext .v0 .v1 .v2 15) == some 0x4a612f2df0168eeee920eaf4a28fecdb#128
#guard vrun 1 (.rev .rev32b .v0 .v1) == some 0x18ce26db6bc943350bb99e9fc463452c#128
#guard vrun 1 (.rev .rev32h .v0 .v1) == some 0xce18db26c96b3543b90b9f9e63c42c45#128
#guard vrun 1 (.rev .rev64b .v0 .v1) == some 0x6bc9433518ce26dbc463452c0bb99e9f#128
#guard vrun 1 (.rev .rev64s .v0 .v1) == some 0x3543c96bdb26ce182c4563c49f9eb90b#128
#guard vrun 1 (.tbl .v0 .v1 .v3) == some 0x000000c4db262c00c4c400000043db9e#128
#guard vrun 1 (.umull false .v0 .v1 .v2) == some 0x94f6ec046339840e2a4e3fe384ba74b0#128
#guard vrun 1 (.umull true .v0 .v1 .v2) == some 0x3030297ec326ee68098edea60238eb5a#128
#guard vrun 1 (.umlal false .v0 .v1 .v2) == some 0xeae1c71d5a0b5c247420ff227528331f#128
#guard vrun 1 (.umlal true .v0 .v1 .v2) == some 0x861b0497b9f8c67e53619de4f2a6a9c9#128
#guard vrun 1 (.pmull false .v0 .v1 .v2) == some 0x7c193c7b7397c25d5a1bf2afa5a486b0#128
#guard vrun 1 (.pmull true .v0 .v1 .v2) == some 0x103e08f3c079d0fc76eefe90abc383a2#128
#guard vrun 1 (.aese .v0 .v1) == some 0x2e29c163f63459ff864b8296194f6f62#128
#guard vrun 1 (.aesd .v0 .v1) == some 0x935de352e6eea5133327c9d94a742f0e#128
#guard vrun 1 (.aesmc .v0 .v1) == some 0x6dec2e845d7b12e01f2f44c72959e15f#128
#guard vrun 1 (.aesimc .v0 .v1) == some 0x7a57393f7a2135ba68a2334a2441ec47#128
#guard vrun 1 (.sha1 .c .v0 .v1 .v2) == some 0x20e6267153b708bc90c27c5893d60b8b#128
#guard vrun 1 (.sha1 .p .v0 .v1 .v2) == some 0x86625f77c2b3205ef638db8f02903493#128
#guard vrun 1 (.sha1 .m .v0 .v1 .v2) == some 0x211ca733716754f86cdf1aab4bbfce1e#128
#guard vrun 1 (.sha1h .v0 .v1) == some 0x0000000000000000000000000b1158f1#128
#guard vrun 1 (.sha1su0 .v0 .v1 .v2) == some 0xf23e033cf764ad5cf2d144ccf21ee995#128
#guard vrun 1 (.sha1su1 .v0 .v1) == some 0x1419aba15bee2c1cf922ecaadfe60ec8#128
#guard vrun 1 (.sha256h .v0 .v1 .v2) == some 0xe1c497d97746073f1651782da1393a02#128
#guard vrun 1 (.sha256h2 .v0 .v1 .v2) == some 0xb165c410862835898af9be50fd0f88ed#128
#guard vrun 1 (.sha256su0 .v0 .v1) == some 0x2b0c08c683a273c58f04e444cad41f5c#128
#guard vrun 1 (.sha256su1 .v0 .v1 .v2) == some 0x71e9213329a7bb97fbd2f25d99aa26bd#128
#guard vrun 1 (.sha512h .v0 .v1 .v2) == some 0xf92721648f00fd877ab443d1beac0b3c#128
#guard vrun 1 (.sha512h2 .v0 .v1 .v2) == some 0x379e146e30a774b6e2dcb854bd79d4ed#128
#guard vrun 1 (.sha512su0 .v0 .v1) == some 0xe05ada678228565c85de122042e15cd2#128
#guard vrun 1 (.sha512su1 .v0 .v1 .v2) == some 0x31accce537ca31778baf01787ecbbc7e#128
#guard vrun 1 (.eor3 .v0 .v1 .v2 .v3) == some 0xf877b13717bddcf3717782f1ceede32e#128
#guard vrun 1 (.bcax .v0 .v1 .v2 .v3) == some 0xfb66af3715b3dde3717799e1cce5e32c#128
#guard vrun 1 (.rax1 .v0 .v1 .v2) == some 0xabb20c466ea3e477424cf8dec5007c1d#128
#guard vrun 1 (.xar .v0 .v1 .v2 0) == some 0xe36caf3718b3dfe5717799e1d8e7ec28#128
#guard vrun 1 (.xar .v0 .v1 .v2 1) == some 0xf1b6579b8c59eff238bbccf0ec73f614#128
#guard vrun 1 (.xar .v0 .v1 .v2 63) == some 0xc6d95e6e3167bfcbe2ef33c3b1cfd850#128
#guard vrun 1 (.add .s4 .v0 .v0 .v0) == some 0xabd5b630eda3b02c93a57e7ce0db7cde#128
#guard vrun 1 (.ext .v0 .v0 .v1 4) == some 0x2c4563c455eadb18f6d1d81649d2bf3e#128
#guard vrun 1 (.aese .v0 .v0) == some 0x63636363636363636363636363636363#128
#guard vrun 1 (.sha256h .v0 .v0 .v2) == some 0x80ae076d625d53ae215e5681f75091a3#128
#guard vrun 1 (.sha256su1 .v0 .v0 .v0) == some 0xedd72c07230faae5779ef25211748f71#128
#guard vrun 1 (.sha512h .v0 .v0 .v0) == some 0x31d5206fb8a283ba6b40f2af7ed8989f#128
#guard vrun 1 (.tbl .v0 .v0 .v3) == some 0x0000006f55eaf0006f6f000000d155d2#128
#guard vrun 1 (.umlal true .v0 .v0 .v0) == some 0x72c0a80c2a33ea5637cab68bc2bee053#128
#guard vrun 1 (.eor3 .v0 .v0 .v1 .v0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard xrun 1 (.umov .w .x0 .v1 0) == some 0x000000002c4563c4#64
#guard xrun 1 (.umov .w .x0 .v1 1) == some 0x000000009f9eb90b#64
#guard xrun 1 (.umov .w .x0 .v1 2) == some 0x000000003543c96b#64
#guard xrun 1 (.umov .w .x0 .v1 3) == some 0x00000000db26ce18#64
#guard xrun 1 (.umov .x .x0 .v1 0) == some 0x9f9eb90b2c4563c4#64
#guard xrun 1 (.umov .x .x0 .v1 1) == some 0xdb26ce183543c96b#64

/-! ## Only the destination changes -/

/-- The registers other than `v0` and `x0` after `i` in run 0 are those before. -/
def others (i : Instr) : Bool :=
  match exec i (s 0) with
  | some t => [VReg.v1, .v2, .v3, .v7, .v16, .v31].all (fun r => t.v r == (s 0).v r) &&
    [Reg.x1, .x2, .x3, .x30].all (fun r => t.gpr r == (s 0).gpr r) && t.sp == (s 0).sp
  | none => false

#guard others (.vop (.aese .v0 .v1))
#guard others (.vop (.sha256h .v0 .v1 .v2))
#guard others (.vop (.ins .s4 .v0 1 .x1))
#guard others (.vop (.umlal true .v0 .v1 .v2))
#guard others (.umov .x .x0 .v1 1)
#guard (exec (.vop (.aese .v0 .v1)) (s 0)).map (·.gpr .x0) == some 0xdeadbeefdeadbeef

/-! ## Immediates that are not encodable fault -/

#guard vrun 0 (.ext .v0 .v1 .v2 16) == none
#guard vrun 0 (.shift .shl .s4 .v0 .v1 32) == none
#guard vrun 0 (.shift .sli .d2 .v0 .v1 64) == none
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 0) == none
#guard vrun 0 (.shift .sri .s4 .v0 .v1 33) == none
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 65) == none
#guard vrun 0 (.ins .s4 .v0 4 .x1) == none
#guard vrun 0 (.ins .d2 .v0 2 .x1) == none
#guard vrun 0 (.dupS .v0 .v1 4) == none
#guard vrun 0 (.xar .v0 .v1 .v2 64) == none
#guard xrun 0 (.umov .w .x0 .v1 4) == none
#guard xrun 0 (.umov .x .x0 .v1 2) == none

/-! ## Loads and stores of a vector register

`ldr q`/`str q` move 16 bytes, little-endian, at an offset that is a multiple
of 16 below 65536, within the permitted regions. -/

/-- The 16 bytes at `0x100 + o` in `s k`, little-endian. -/
def bytesAt (o : Nat) : BitVec 128 :=
  BitVec.ofNat 128 ((List.range 16).foldl (fun acc i => acc + (17 * (o + i) + 3) % 256 * 256 ^ i) 0)

#guard bytesAt 0 == 0x02f1e0cfbead9c8b7a69584736251403#128
#guard ((exec (.ldrq .v0 .x2 0) (s 0)).map (·.v .v0)) == some (bytesAt 0)
#guard ((exec (.ldrq .v0 .x2 16) (s 0)).map (·.v .v0)) == some (bytesAt 16)
#guard ((exec (.ldrq .v0 .x2 8) (s 0)).map (·.v .v0)) == none
#guard ((exec (.ldrq .v0 .x2 32) (s 0)).map (·.v .v0)) == none
#guard ((exec (.ldrq .v0 .x2 65536) (s 0)).map (·.v .v0)) == none
#guard ((exec (.strq .v1 .x2 16) (s 0)).bind fun t => (exec (.ldrq .v0 .x2 16) t).map (·.v .v0)) ==
  some ((s 0).v .v1)
#guard ((exec (.strq .v1 .x2 16) (s 0)).map fun t => (t.mem 0x10f, t.mem 0x110)) ==
  some (0x02, vbyte ((s 0).v .v1) 0)
#guard ((exec (.strq .v1 .x2 32) (s 0)).map (·.v .v0)) == none

/-! ## Printing -/

#guard printer.instr (.vop (.mov .v0 .v1)) == ["mov v0.16b, v1.16b"]
#guard printer.instr (.vop (.movi0 .v0)) == ["movi v0.2d, #0"]
#guard printer.instr (.vop (.dup .s4 .v0 .x1)) == ["dup v0.4s, w1"]
#guard printer.instr (.vop (.dup .d2 .v0 .x1)) == ["dup v0.2d, x1"]
#guard printer.instr (.vop (.ins .s4 .v0 0 .x1)) == ["mov v0.s[0], w1"]
#guard printer.instr (.vop (.ins .s4 .v0 1 .x1)) == ["mov v0.s[1], w1"]
#guard printer.instr (.vop (.ins .s4 .v0 2 .x1)) == ["mov v0.s[2], w1"]
#guard printer.instr (.vop (.ins .s4 .v0 3 .x1)) == ["mov v0.s[3], w1"]
#guard printer.instr (.vop (.ins .d2 .v0 0 .x1)) == ["mov v0.d[0], x1"]
#guard printer.instr (.vop (.ins .d2 .v0 1 .x1)) == ["mov v0.d[1], x1"]
#guard printer.instr (.vop (.dupS .v0 .v1 0)) == ["dup s0, v1.s[0]"]
#guard printer.instr (.vop (.dupS .v0 .v1 1)) == ["dup s0, v1.s[1]"]
#guard printer.instr (.vop (.dupS .v0 .v1 2)) == ["dup s0, v1.s[2]"]
#guard printer.instr (.vop (.dupS .v0 .v1 3)) == ["dup s0, v1.s[3]"]
#guard printer.instr (.vop (.logic .and .v0 .v1 .v2)) == ["and v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.logic .orr .v0 .v1 .v2)) == ["orr v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.logic .eor .v0 .v1 .v2)) == ["eor v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.logic .bic .v0 .v1 .v2)) == ["bic v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.logic .orn .v0 .v1 .v2)) == ["orn v0.16b, v1.16b, v2.16b"]
#guard printer.instr (.vop (.not .v0 .v1)) == ["not v0.16b, v1.16b"]
#guard printer.instr (.vop (.add .s4 .v0 .v1 .v2)) == ["add v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.sub .s4 .v0 .v1 .v2)) == ["sub v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.shift .shl .s4 .v0 .v1 0)) == ["shl v0.4s, v1.4s, #0"]
#guard printer.instr (.vop (.shift .shl .s4 .v0 .v1 7)) == ["shl v0.4s, v1.4s, #7"]
#guard printer.instr (.vop (.shift .shl .s4 .v0 .v1 31)) == ["shl v0.4s, v1.4s, #31"]
#guard printer.instr (.vop (.shift .sli .s4 .v0 .v1 0)) == ["sli v0.4s, v1.4s, #0"]
#guard printer.instr (.vop (.shift .sli .s4 .v0 .v1 7)) == ["sli v0.4s, v1.4s, #7"]
#guard printer.instr (.vop (.shift .sli .s4 .v0 .v1 31)) == ["sli v0.4s, v1.4s, #31"]
#guard printer.instr (.vop (.shift .ushr .s4 .v0 .v1 1)) == ["ushr v0.4s, v1.4s, #1"]
#guard printer.instr (.vop (.shift .ushr .s4 .v0 .v1 13)) == ["ushr v0.4s, v1.4s, #13"]
#guard printer.instr (.vop (.shift .ushr .s4 .v0 .v1 32)) == ["ushr v0.4s, v1.4s, #32"]
#guard printer.instr (.vop (.shift .sri .s4 .v0 .v1 1)) == ["sri v0.4s, v1.4s, #1"]
#guard printer.instr (.vop (.shift .sri .s4 .v0 .v1 13)) == ["sri v0.4s, v1.4s, #13"]
#guard printer.instr (.vop (.shift .sri .s4 .v0 .v1 32)) == ["sri v0.4s, v1.4s, #32"]
#guard printer.instr (.vop (.perm .zip1 .s4 .v0 .v1 .v2)) == ["zip1 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.perm .zip2 .s4 .v0 .v1 .v2)) == ["zip2 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.perm .trn1 .s4 .v0 .v1 .v2)) == ["trn1 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.perm .trn2 .s4 .v0 .v1 .v2)) == ["trn2 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.perm .uzp1 .s4 .v0 .v1 .v2)) == ["uzp1 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.perm .uzp2 .s4 .v0 .v1 .v2)) == ["uzp2 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.add .d2 .v0 .v1 .v2)) == ["add v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.sub .d2 .v0 .v1 .v2)) == ["sub v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.shift .shl .d2 .v0 .v1 0)) == ["shl v0.2d, v1.2d, #0"]
#guard printer.instr (.vop (.shift .shl .d2 .v0 .v1 7)) == ["shl v0.2d, v1.2d, #7"]
#guard printer.instr (.vop (.shift .shl .d2 .v0 .v1 63)) == ["shl v0.2d, v1.2d, #63"]
#guard printer.instr (.vop (.shift .sli .d2 .v0 .v1 0)) == ["sli v0.2d, v1.2d, #0"]
#guard printer.instr (.vop (.shift .sli .d2 .v0 .v1 7)) == ["sli v0.2d, v1.2d, #7"]
#guard printer.instr (.vop (.shift .sli .d2 .v0 .v1 63)) == ["sli v0.2d, v1.2d, #63"]
#guard printer.instr (.vop (.shift .ushr .d2 .v0 .v1 1)) == ["ushr v0.2d, v1.2d, #1"]
#guard printer.instr (.vop (.shift .ushr .d2 .v0 .v1 13)) == ["ushr v0.2d, v1.2d, #13"]
#guard printer.instr (.vop (.shift .ushr .d2 .v0 .v1 64)) == ["ushr v0.2d, v1.2d, #64"]
#guard printer.instr (.vop (.shift .sri .d2 .v0 .v1 1)) == ["sri v0.2d, v1.2d, #1"]
#guard printer.instr (.vop (.shift .sri .d2 .v0 .v1 13)) == ["sri v0.2d, v1.2d, #13"]
#guard printer.instr (.vop (.shift .sri .d2 .v0 .v1 64)) == ["sri v0.2d, v1.2d, #64"]
#guard printer.instr (.vop (.perm .zip1 .d2 .v0 .v1 .v2)) == ["zip1 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.perm .zip2 .d2 .v0 .v1 .v2)) == ["zip2 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.perm .trn1 .d2 .v0 .v1 .v2)) == ["trn1 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.perm .trn2 .d2 .v0 .v1 .v2)) == ["trn2 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.perm .uzp1 .d2 .v0 .v1 .v2)) == ["uzp1 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.perm .uzp2 .d2 .v0 .v1 .v2)) == ["uzp2 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.ext .v0 .v1 .v2 0)) == ["ext v0.16b, v1.16b, v2.16b, #0"]
#guard printer.instr (.vop (.ext .v0 .v1 .v2 1)) == ["ext v0.16b, v1.16b, v2.16b, #1"]
#guard printer.instr (.vop (.ext .v0 .v1 .v2 8)) == ["ext v0.16b, v1.16b, v2.16b, #8"]
#guard printer.instr (.vop (.ext .v0 .v1 .v2 15)) == ["ext v0.16b, v1.16b, v2.16b, #15"]
#guard printer.instr (.vop (.rev .rev32b .v0 .v1)) == ["rev32 v0.16b, v1.16b"]
#guard printer.instr (.vop (.rev .rev32h .v0 .v1)) == ["rev32 v0.8h, v1.8h"]
#guard printer.instr (.vop (.rev .rev64b .v0 .v1)) == ["rev64 v0.16b, v1.16b"]
#guard printer.instr (.vop (.rev .rev64s .v0 .v1)) == ["rev64 v0.4s, v1.4s"]
#guard printer.instr (.vop (.tbl .v0 .v1 .v3)) == ["tbl v0.16b, {v1.16b}, v3.16b"]
#guard printer.instr (.vop (.umull false .v0 .v1 .v2)) == ["umull v0.2d, v1.2s, v2.2s"]
#guard printer.instr (.vop (.umull true .v0 .v1 .v2)) == ["umull2 v0.2d, v1.4s, v2.4s"]
#guard printer.instr (.vop (.umlal false .v0 .v1 .v2)) == ["umlal v0.2d, v1.2s, v2.2s"]
#guard printer.instr (.vop (.umlal true .v0 .v1 .v2)) == ["umlal2 v0.2d, v1.4s, v2.4s"]
#guard printer.instr (.vop (.pmull false .v0 .v1 .v2)) == ["pmull v0.1q, v1.1d, v2.1d"]
#guard printer.instr (.vop (.pmull true .v0 .v1 .v2)) == ["pmull2 v0.1q, v1.2d, v2.2d"]
#guard printer.instr (.vop (.aese .v0 .v1)) == ["aese v0.16b, v1.16b"]
#guard printer.instr (.vop (.aesd .v0 .v1)) == ["aesd v0.16b, v1.16b"]
#guard printer.instr (.vop (.aesmc .v0 .v1)) == ["aesmc v0.16b, v1.16b"]
#guard printer.instr (.vop (.aesimc .v0 .v1)) == ["aesimc v0.16b, v1.16b"]
#guard printer.instr (.vop (.sha1 .c .v0 .v1 .v2)) == ["sha1c q0, s1, v2.4s"]
#guard printer.instr (.vop (.sha1 .p .v0 .v1 .v2)) == ["sha1p q0, s1, v2.4s"]
#guard printer.instr (.vop (.sha1 .m .v0 .v1 .v2)) == ["sha1m q0, s1, v2.4s"]
#guard printer.instr (.vop (.sha1h .v0 .v1)) == ["sha1h s0, s1"]
#guard printer.instr (.vop (.sha1su0 .v0 .v1 .v2)) == ["sha1su0 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.sha1su1 .v0 .v1)) == ["sha1su1 v0.4s, v1.4s"]
#guard printer.instr (.vop (.sha256h .v0 .v1 .v2)) == ["sha256h q0, q1, v2.4s"]
#guard printer.instr (.vop (.sha256h2 .v0 .v1 .v2)) == ["sha256h2 q0, q1, v2.4s"]
#guard printer.instr (.vop (.sha256su0 .v0 .v1)) == ["sha256su0 v0.4s, v1.4s"]
#guard printer.instr (.vop (.sha256su1 .v0 .v1 .v2)) == ["sha256su1 v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.sha512h .v0 .v1 .v2)) == ["sha512h q0, q1, v2.2d"]
#guard printer.instr (.vop (.sha512h2 .v0 .v1 .v2)) == ["sha512h2 q0, q1, v2.2d"]
#guard printer.instr (.vop (.sha512su0 .v0 .v1)) == ["sha512su0 v0.2d, v1.2d"]
#guard printer.instr (.vop (.sha512su1 .v0 .v1 .v2)) == ["sha512su1 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.eor3 .v0 .v1 .v2 .v3)) == ["eor3 v0.16b, v1.16b, v2.16b, v3.16b"]
#guard printer.instr (.vop (.bcax .v0 .v1 .v2 .v3)) == ["bcax v0.16b, v1.16b, v2.16b, v3.16b"]
#guard printer.instr (.vop (.rax1 .v0 .v1 .v2)) == ["rax1 v0.2d, v1.2d, v2.2d"]
#guard printer.instr (.vop (.xar .v0 .v1 .v2 0)) == ["xar v0.2d, v1.2d, v2.2d, #0"]
#guard printer.instr (.vop (.xar .v0 .v1 .v2 1)) == ["xar v0.2d, v1.2d, v2.2d, #1"]
#guard printer.instr (.vop (.xar .v0 .v1 .v2 63)) == ["xar v0.2d, v1.2d, v2.2d, #63"]
#guard printer.instr (.vop (.add .s4 .v0 .v0 .v0)) == ["add v0.4s, v0.4s, v0.4s"]
#guard printer.instr (.vop (.ext .v0 .v0 .v1 4)) == ["ext v0.16b, v0.16b, v1.16b, #4"]
#guard printer.instr (.vop (.aese .v0 .v0)) == ["aese v0.16b, v0.16b"]
#guard printer.instr (.vop (.sha256h .v0 .v0 .v2)) == ["sha256h q0, q0, v2.4s"]
#guard printer.instr (.vop (.sha256su1 .v0 .v0 .v0)) == ["sha256su1 v0.4s, v0.4s, v0.4s"]
#guard printer.instr (.vop (.sha512h .v0 .v0 .v0)) == ["sha512h q0, q0, v0.2d"]
#guard printer.instr (.vop (.tbl .v0 .v0 .v3)) == ["tbl v0.16b, {v0.16b}, v3.16b"]
#guard printer.instr (.vop (.umlal true .v0 .v0 .v0)) == ["umlal2 v0.2d, v0.4s, v0.4s"]
#guard printer.instr (.vop (.eor3 .v0 .v0 .v1 .v0)) == ["eor3 v0.16b, v0.16b, v1.16b, v0.16b"]
#guard printer.instr (.umov .w .x0 .v1 0) == ["umov w0, v1.s[0]"]
#guard printer.instr (.umov .w .x0 .v1 1) == ["umov w0, v1.s[1]"]
#guard printer.instr (.umov .w .x0 .v1 2) == ["umov w0, v1.s[2]"]
#guard printer.instr (.umov .w .x0 .v1 3) == ["umov w0, v1.s[3]"]
#guard printer.instr (.umov .x .x0 .v1 0) == ["umov x0, v1.d[0]"]
#guard printer.instr (.umov .x .x0 .v1 1) == ["umov x0, v1.d[1]"]
#guard printer.instr (.ldrq .v31 .x2 16) == ["ldr q31, [x2, #16]"]
#guard printer.instr (.strq .v16 .x30 65520) == ["str q16, [x30, #65520]"]
#guard printer.enableFeature "aes" == [".arch_extension aes"]
#guard printer.disableFeature "sha3" == [".arch_extension nosha3"]

/-! ## CPU features -/

#guard isa.requires (.vop (.aese .v0 .v1)) == ["aes"]
#guard isa.requires (.vop (.aesimc .v0 .v1)) == ["aes"]
#guard isa.requires (.vop (.pmull true .v0 .v1 .v2)) == ["aes"]
#guard isa.requires (.vop (.sha1 .m .v0 .v1 .v2)) == ["sha2"]
#guard isa.requires (.vop (.sha1h .v0 .v1)) == ["sha2"]
#guard isa.requires (.vop (.sha256su1 .v0 .v1 .v2)) == ["sha2"]
#guard isa.requires (.vop (.sha512h2 .v0 .v1 .v2)) == ["sha3"]
#guard isa.requires (.vop (.eor3 .v0 .v1 .v2 .v3)) == ["sha3"]
#guard isa.requires (.vop (.xar .v0 .v1 .v2 3)) == ["sha3"]
#guard isa.requires (.vop (.tbl .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.umull false .v0 .v1 .v2)) == []
#guard isa.requires (.ldrq .v0 .x1 0) == []
#guard isa.requires (.umov .x .x0 .v1 0) == []
#guard !isa.writesSp (.vop (.add .s4 .v0 .v1 .v2))

/-! ## MUL, MLA, MLS, SQDMULH and UMIN

These expected values were computed on Arm hardware (an Apple M1 Max), by
the same instructions as the printer prints them (checked below), in inline
assembly that loaded `v0`–`v3` from the inputs above and stored `v0`
afterwards, as for the others. -/

#guard vrun 0 (.mul .v0 .v1 .v2) == some 0xd7189c2499ca8d543140b3d627f99d7c#128
#guard vrun 0 (.mul .v0 .v0 .v1) == some 0xa20096a6a398e46c4409c415ec31ee73#128
#guard vrun 0 (.mla .v0 .v1 .v2) == some 0x1ed6f167804ed35fbdebb02fd7f2b3df#128
#guard vrun 0 (.mla .v0 .v0 .v1) == some 0xe9beebe98a1d2a77d0b4c06e9c2b04d6#128
#guard vrun 0 (.mls .v0 .v1 .v2) == some 0x70a5b91f4cb9b8b75b6a488387ff78e7#128
#guard vrun 0 (.mls .v0 .v0 .v1) == some 0xa5bdbe9d42eb619f48a13844c3c727f0#128
#guard vrun 0 (.sqdmulh .v0 .v1 .v2) == some 0xf7fdf0a50694fed3e8ca22b2fae8a606#128
#guard vrun 0 (.sqdmulh .v0 .v0 .v1) == some 0xe84ab5030c6c935130db57ee31d1afb3#128
#guard vrun 0 (.sqdmulh .v0 .v3 .v1) == some 0xf61120c3fa24cdcbf9386307f2e5c349#128
#guard vrun 0 (.umin .v0 .v1 .v2) == some 0x183bb3b2c1984cc436ca734e082da43c#128
#guard vrun 0 (.umin .v0 .v0 .v1) == some 0x47be5543c1984cc48caafc59aff91663#128
#guard vrun 1 (.mul .v0 .v1 .v2) == some 0xc326ee680238eb5a6339840e84ba74b0#128
#guard vrun 1 (.mul .v0 .v0 .v1) == some 0x17e1da4008209732028605aaec95b9fc#128
#guard vrun 1 (.mla .v0 .v1 .v2) == some 0x1911c980f90ac370ad0c434c7528331f#128
#guard vrun 1 (.mla .v0 .v0 .v1) == some 0x6dccb558fef26f484c58c4e8dd03786b#128
#guard vrun 1 (.mls .v0 .v1 .v2) == some 0x92c3ecb0f498ecbce6993b306bb349bf#128
#guard vrun 1 (.mls .v0 .v0 .v1) == some 0x3e0900d8eeb140e4474cb99403d80473#128
#guard vrun 1 (.sqdmulh .v0 .v1 .v2) == some 0xefcb909f131dbd4c0cde241efc11b83f#128
#guard vrun 1 (.sqdmulh .v0 .v0 .v1) == some 0xe74428bafc2e06dec869d5f0fa9d487b#128
#guard vrun 1 (.sqdmulh .v0 .v3 .v1) == some 0xf83261050643c64dffffeb9f079f67c3#128
#guard vrun 1 (.umin .v0 .v1 .v2) == some 0x384a612f2df0168e9f9eb90b2c4563c4#128
#guard vrun 1 (.umin .v0 .v0 .v1) == some 0x55eadb183543c96b49d2bf3e2c4563c4#128

/-- `v0` after `sqdmulh v0.4s, v1.4s, v2.4s` with `v1 = x` and `v2 = y`. -/
def sqd (x y : BitVec 128) : Option (BitVec 128) :=
  (exec (.vop (.sqdmulh .v0 .v1 .v2)) { s 0 with v := fun r => if r = .v1 then x else if r = .v2 then y
    else 0 }).map (·.v .v0)

-- `-2 ^ 31` times `-1`, `-2 ^ 31 + 1`, `1` and `2 ^ 31 - 1` (on the M1 Max, as above).
#guard sqd 0x80000000800000008000000080000000#128 0x7fffffff0000000180000001ffffffff#128 ==
  some 0x80000001ffffffff7fffffff00000001#128
-- `-2 ^ 31` times `-2 ^ 31` saturates, and the model faults.
#guard sqd 0x80000000800000008000000080000000#128 0x00000001000000018000000000000001#128 == none

#guard printer.instr (.vop (.mul .v0 .v1 .v2)) == ["mul v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.mla .v0 .v1 .v2)) == ["mla v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.mls .v0 .v1 .v2)) == ["mls v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.sqdmulh .v0 .v1 .v2)) == ["sqdmulh v0.4s, v1.4s, v2.4s"]
#guard printer.instr (.vop (.umin .v0 .v1 .v2)) == ["umin v0.4s, v1.4s, v2.4s"]
#guard isa.requires (.vop (.sqdmulh .v0 .v1 .v2)) == []

end VG.Test.AArch64Simd
