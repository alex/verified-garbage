import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Constant-time byte comparison on PPC64LE

`vg_ct_eq(a = r3, a_len = r4, b = r5, b_len = r6)`: the same algorithm as
the AArch64 implementation (`VG.Impl.Ct.AArch64`). The lengths are compared
first; if they are equal, the XORs of the bytes at each offset are ORed
together into `r7`, and the result is `(r7 - 1) >> 63`, which is 1 iff `r7`
is zero. The branches are on the lengths only.
-/

namespace VG.Impl.Ct.PPC64LE
open VG.PPC64LE

def step : List Instr := [
  .add .r10 .r3 .r8, .lbz .r11 .r10 0,
  .add .r10 .r5 .r8, .lbz .r12 .r10 0,
  .logic .xor .r11 .r11 .r12, .logic .or .r7 .r7 .r11,
  .addi .r8 .r8 1, .sub .r9 .r8 .r4]

def finish : Prog isa := .block [.subi .r7 .r7 1, .lsr .d .r3 .r7 63]

def equal : Prog isa :=
  .seq (.block [.li .r8 0])
    (.seq (.ite (.zero .d .r4) (.block []) (.loop (.block step) (.nonzero .d .r9))) finish)

def eq : Prog isa :=
  .seq (.block [.li .r7 0, .sub .r9 .r4 .r6])
    (.ite (.zero .d .r9) equal (.block [.li .r3 0]))

end VG.Impl.Ct.PPC64LE
