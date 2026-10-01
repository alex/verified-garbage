import VerifiedGarbage.Proof.Ed25519.X86.DecodeY
import VerifiedGarbage.Proof.Ed25519.X86.RecoverPoint

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def decodeNumber (n : Nat) : Option Spec.Ed25519.Point :=
  if h : n % 2 ^ 255 < Spec.X25519.P then
    (Spec.Ed25519.recoverX ⟨n % 2 ^ 255, h⟩ (n / 2 ^ 255 == 1)).map
      (fun x => recoveredPoint x ⟨n % 2 ^ 255, h⟩)
  else none

theorem pointDecode_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointDecode s fun t => MulKeep x s t ∧ DecodeResult x (decodeNumber (fe s.mem x 96)) t := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun b ⟨kb, eb, bb, zb⟩ => ?_
  have km := ka.trans (MulKeep.of_ikeep ca (IKeep.of_field kb))
  apply WP.ite (decide (fe s.mem x 96 % 2 ^ 255 < Spec.X25519.P)) (by rw [ya] at zb; exact zb)
  · intro hh
    have hh' := of_decide_eq_true hh
    have ey : env b.mem x 1 = (⟨fe s.mem x 96 % 2 ^ 255, hh'⟩ : Spec.X25519.Fe) := by
      rw [eb]
      change VG.Proof.X25519.toFe (fe a.mem x 96) = _
      rw [ya]
      apply Fin.ext
      exact Nat.mod_eq_of_lt hh'
    have ebits : wd b.mem x 32 = signWord (fe s.mem x 96 / 2 ^ 255 == 1) := by
      rw [bb, ba]
      have hn : fe s.mem x 96 / 2 ^ 255 ≤ 1 := by have := fe_lt s.mem x 96; omega_using [this]
      rcases (by omega_using [hn] : fe s.mem x 96 / 2 ^ 255 = 0 ∨ fe s.mem x 96 / 2 ^ 255 = 1) with h | h <;>
        rw [h] <;> rfl
    refine WP.mono (recoverPoint_ok (km.ctx hc) _ ebits) fun t ⟨kt, tr⟩ => ?_
    refine ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) kt), ?_⟩
    rw [ey] at tr
    simpa only [decodeNumber, dite_eq_left hh'] using tr
  · intro hh
    have hh' := of_decide_eq_false hh
    refine WP.mono (recoverInvalid_ok b x) fun t ⟨kt, tr⟩ => ?_
    exact ⟨km.trans (MulKeep.of_ikeep (km.ctx hc) (IKeep.of_field kt)), by
      simpa only [decodeNumber, dite_eq_right hh'] using tr⟩

end VG.Proof.Ed25519.X86
