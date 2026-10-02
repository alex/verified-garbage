import VerifiedGarbage.Impl.X448.AArch64.Cached
/-! Symmetric squaring: each cross product is computed once. -/
namespace VG.Impl.X448.AArch64.Symmetric
open VG VG.AArch64
open VG.Impl.X448.AArch64 (st ACC)
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached

def body (k : Nat) : List Instr :=
  (List.range 8).flatMap (fun i => if i ≤ k ∧ k < i + 8 ∧ i ≤ k - i then
    if i = k - i then termFrom (cacheReg i) (cacheReg (k - i))
    else termFromDouble (cacheReg i) (cacheReg (k - i)) else [])

def column (k : Nat) : List Instr :=
  [.movz .x .x4 0 0, .movz .x .x5 0 0] ++ body k ++
  [st .x4 (ACC + 16 * k), st .x5 (ACC + 16 * k + 8)]
end VG.Impl.X448.AArch64.Symmetric
