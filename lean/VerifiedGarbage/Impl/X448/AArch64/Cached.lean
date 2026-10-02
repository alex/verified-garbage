import VerifiedGarbage.Impl.X448.AArch64.Wide

/-! Squaring with all eight wide operands retained in caller-saved registers. -/
namespace VG.Impl.X448.AArch64.Cached

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld)

def cacheReg : Nat → Reg
  | 0 => .x6 | 1 => .x7 | 2 => .x8 | 3 => .x9
  | 4 => .x13 | 5 => .x14 | 6 => .x15 | _ => .x16

def loadCached (a : Nat) : List Instr :=
  (List.range 8).flatMap fun i => [ld (cacheReg i) (a + 8 * i)]

end VG.Impl.X448.AArch64.Cached
