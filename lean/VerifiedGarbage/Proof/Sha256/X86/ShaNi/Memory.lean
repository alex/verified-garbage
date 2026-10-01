import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Sha256

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86
open VG.Spec.Sha256 (stateAt)

theorem stateAt_lo (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW p 128) j = (stateAt m p)[j] := by
  rw [dword_readW _ _ hj]; simp only [stateAt, Vector.getElem_ofFn]

theorem stateAt_hi (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW (p + BitVec.ofNat 64 16) 128) j = (stateAt m p)[4 + j] := by
  rw [dword_readW _ _ hj]
  simp only [stateAt, Vector.getElem_ofFn]
  refine congrArg (fun a => m.readW a 32) ?_
  exact Offset.add_add_eq _ (by omega)

theorem stateAt_store (m : Mem) (p : Addr) (x y : BitVec 128) :
    stateAt ((m.writeW p x).writeW (p + BitVec.ofNat 64 16) y) p =
      #v[dword x 0, dword x 1, dword x 2, dword x 3, dword y 0, dword y 1, dword y 2, dword y 3] := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  by_cases hlo : j < 4
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      readW_writeW128 _ _ _ hlo]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [show p + BitVec.ofNat 64 (4 * j) = p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (4 * (j - 4)) from
        (Offset.add_add_eq _ (by omega)).symm, readW_writeW128 _ _ _ (by omega)]
    rcases (by omega : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Sha256.X86.ShaNi
