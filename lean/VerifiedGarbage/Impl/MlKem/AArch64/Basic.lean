import VerifiedGarbage.TCB.AArch64.Isa

/-!
# ML-KEM on AArch64: helpers

Coefficients are `u32`s less than `q = 3329`, loaded with `ldr w` (which
zero-extends them) and computed on in 64-bit registers, where no
intermediate value wraps. A value less than `2q` is reduced with one
conditional subtraction without a branch (`csub`): `d - q` is negative
exactly when `d < q`, which its sign bit (bit 63) says, and `madd` adds `q`
back times that bit. The model has no flags, conditional select or
register-offset addressing: pointers advance by an immediate, and loops
count down to zero (`cbnz`).

`vg_mlkem_add` and `vg_mlkem_sub` compute in vectors
(`Impl/MlKem/AArch64/Ntt.lean`).
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `mov d, n` (`add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- `d ← d mod q` for `d < 2q`, with `q` in `qr` and a temporary `t`:
`d - q`, plus `q` if that is negative. -/
def csub (d t qr : Reg) : List Instr := [.sub .x d d qr, .lsr .x t d 63, .madd .x d t qr d]

end VG.Impl.MlKem.AArch64
