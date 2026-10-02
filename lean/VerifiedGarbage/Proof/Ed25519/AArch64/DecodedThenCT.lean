import VerifiedGarbage.Proof.Ed25519.AArch64.PointDecodeCT
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext

/-! A decoder's public success flag selects the continuation. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem DecodeResult.of_keeps {base : Addr} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (kt : Keeps [] s t) : DecodeResult base p t := by
  cases p with
  | none => exact (kt.gpr _ (by simp)).trans h
  | some p => exact ⟨(kt.gpr _ (by simp)).trans h.1, by rw [kt.mem]; exact h.2⟩

theorem decodedThen_ct (base : Addr) (p : Option Spec.Ed25519.Point) (P : State → Prop) (next : Prog isa)
    (_hP : ∀ s t, Keeps [] s t → P s → P t)
    (hn : ∀ a, p = some a → CT
      (fun s t => (P s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    CT (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  rw [decodedThen]
  refine CT.ite ?_ ?_ ?_
  · intro s t h
    simp only [eval, read_x, decodeResult_flag h.1.2, decodeResult_flag h.2.2]
  · cases p with
    | none =>
      apply CT.of_false
      intro s t h
      have hz : s.gpr .x8 = 0 := h.1.1.2
      have he := h.2
      change some (s.gpr .x8 != 0) = some true at he
      rw [hz] at he
      contradiction
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.2⟩, ⟨h.1.2.1, h.1.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
