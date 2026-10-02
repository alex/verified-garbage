import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks

/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ eval (.zero .x .x8) t = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.gpr _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  change some (t.gpr .x8 == 0) = _
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    CT (fun x y => Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y)
      (.seq (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine CT.seq (R := fun x y => x.gpr .x0 = base ∧ y.gpr .x0 = base)
    (CT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : CT (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
      exact fun _ _ _ => agree_ofRegs (by simp)
    have hw := CT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some true) =>
        And.intro (WP.block_nil h.1.1.x0) (WP.block_nil h.1.2.1.x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct base).mono
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        ⟨h.1.1.x0, h.1.2.1.x0⟩) (fun _ _ h => h)
    have hw := CT.wp ht
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        And.intro (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) fun _ k => (k.1.scr h.1.1).x0)
          (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) fun _ k => (k.1.scr h.1.2.1).x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.scr h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.AArch64
