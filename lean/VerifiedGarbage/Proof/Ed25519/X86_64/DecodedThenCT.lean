import VerifiedGarbage.Proof.Ed25519.X86_64.PointDecodeCT
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyContext

/-! Untrusted: a decoder's public success flag selects the continuation. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem DecodeResult.of_keeps {base : Addr} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (kt : Keeps [] s t) : DecodeResult base p t := by
  cases p with
  | none => exact (kt.1 _ (by simp)).trans h
  | some p => exact ⟨(kt.1 _ (by simp)).trans h.1, by rw [kt.2.1]; exact h.2⟩

theorem decodedThen_ct (base : Addr) (p : Option Spec.Ed25519.Point) (P : State → Prop) (next : Prog isa)
    (hP : ∀ s t, Keeps [] s t → P s → P t)
    (hn : ∀ a, p = some a → RelCT isa
      (fun s t => (P s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    RelCT isa (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (P s ∧ DecodeResult base p s) ∧ (P t ∧ DecodeResult base p t))
      (.block [.alu .test .rax (.reg .rax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => Taint.agree_ofRegs (by simp)
  have hw (s : State) (h : P s ∧ DecodeResult base p s) :
      WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
        P t ∧ DecodeResult base p t ∧ t.zf = some (!p.isSome) := by
    refine WP.mono (testResult_ok p.isSome (decodeResult_flag h.2)) fun t ⟨tz, kt⟩ => ?_
    exact ⟨hP s t kt h.1, h.2.of_keeps kt, tz⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [decodedThen]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2.2, h.2.2.2.2]
  · cases p with
    | none =>
      apply VG.RelCT.of_false
      intro s t h
      have he := h.2
      simp only [eval, h.1.2.1.2.2, Option.isSome_none, Bool.not_false,
        Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at he
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.1.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
