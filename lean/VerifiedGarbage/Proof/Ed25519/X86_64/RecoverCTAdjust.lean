import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks

/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scratch s base)
    (b : Bool) (hb : s.gpr .rsi = signWord b) :
    WP isa (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ t.zf = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeWide_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.1 _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    RelCT isa (fun x y => Scratch x base ∧ Scratch y base ∧ x.zf = y.zf)
      (.seq (.ite .e (.block []) (.block (fieldCode fld [.const 5 0, .sub 0 5 0])))
        (.block (recoverSuccess fld))) (fun _ _ => True) := by
  refine VG.RelCT.seq (M := isa) (R := fun x y => x.gpr .rdi = base ∧ y.gpr .rdi = base)
    (VG.RelCT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : RelCT isa (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply taintFld (Taint.ofRegs []) _ (by fld_taint_decide)
      exact fun _ _ _ => Taint.agree_ofRegs (by simp)
    have hw := VG.RelCT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some true) =>
        And.intro (WP.block_nil h.1.1.rdi) (WP.block_nil h.1.2.1.rdi))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct (fld := fld) base).mono
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some false) =>
        ⟨h.1.1.rdi, h.1.2.1.rdi⟩) (fun _ _ h => h)
    have hw := VG.RelCT.wp ht
      (fun x y (h : (Scratch x base ∧ Scratch y base ∧ x.zf = y.zf) ∧ isa.eval .e x = some false) =>
        And.intro (WP.mono (fieldCodeWide_ok h.1.1 [.const 5 0, .sub 0 5 0]) fun _ k => (h.1.1.of_keep k.1).rdi)
          (WP.mono (fieldCodeWide_ok h.1.2.1 [.const 5 0, .sub 0 5 0]) fun _ k => (h.1.2.1.of_keep k.1).rdi))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (recoverAdjustSign fld) (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (Impl.X25519.X86_64.freeze (offset 0) ++ recoverParity)) s fun t =>
        Scratch t base ∧ t.zf = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨h.1.of_keep kt, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.rdi, h.2.1.rdi⟩)
    (fun _ _ h => h)
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.X86_64
