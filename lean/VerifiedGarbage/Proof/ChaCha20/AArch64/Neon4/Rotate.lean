import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64

theorem vword_rev32h_rol16 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VRevOp.rev32h.eval x) e = (vword x e).rotateLeft 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, VRevOp.eval,
    BitVec.getLsbD_rotateLeft]
  rw [show 32 * e + i = 8 * (4 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega)]
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and]
  simp only [Nat.reduceMod]
  split
  · simp only [show 32 - 16 + i < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp only [show i - 16 < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

theorem rol8_index (i : Fin 16) :
    (vbyte VG.Impl.ChaCha20.AArch64.Neon4.rol8Table i).toNat =
      4 * (i.val / 4) + (i.val + 3) % 4 :=
  (show ∀ i : Fin 16, (vbyte VG.Impl.ChaCha20.AArch64.Neon4.rol8Table i).toNat =
      4 * (i.val / 4) + (i.val + 3) % 4 by decide +kernel) i

theorem vword_tbl_rol8 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (ofVBytes fun j =>
      let idx := (vbyte VG.Impl.ChaCha20.AArch64.Neon4.rol8Table j).toNat
      if idx < 16 then vbyte x idx else 0) e = (vword x e).rotateLeft 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_rotateLeft]
  rw [show 32 * e + i = 8 * (4 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega)]
  rw [rol8_index ⟨4 * e + i / 8, by omega⟩]
  have hidx : 4 * ((4 * e + i / 8) / 4) + (4 * e + i / 8 + 3) % 4 < 16 := by omega
  simp only [hidx, ite_true, vbyte, BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, Nat.reduceMod]
  split
  · simp only [show 32 - 8 + i < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp only [show i - 8 < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

end VG.Proof.ChaCha20.AArch64.Neon4
