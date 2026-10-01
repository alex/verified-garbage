import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ s.gpr .esi = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) s fun t =>
      FieldKeep base s t ∧ t.zf = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ka, _, va⟩ => ?_
  refine WP.mono (recoverParity_ok (ka.ctx hs) b (ka.keep.esi.trans hb)) fun t ⟨kt, _, tz⟩ => ?_
  refine ⟨ka.trans kt, ?_⟩
  change fe a.mem base 64 = _ at va
  rw [tz, va]

theorem adjustTail_ct (base : BitVec 32) :
    RelCT isa (fun s t => Ctx base s ∧ Ctx base t ∧ s.zf = t.zf)
      (.seq (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine VG.RelCT.seq (M := isa) (R := fun s t => s.gpr .edi = base ∧ t.gpr .edi = base)
    (VG.RelCT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · intro s t ts tt s' t' h es et
    rw [Exec.block_iff] at es et
    change some (s, []) = some (s', ts) at es
    change some (t, []) = some (t', tt) at et
    cases es; cases et
    exact ⟨rfl, h.1.1.edi, h.1.2.1.edi⟩
  · have ct := (negateBlock_ct base).mono
      (P' := fun (s t : State) => (Ctx base s ∧ Ctx base t ∧ s.zf = t.zf) ∧ isa.eval .e s = some false)
      (fun _ _ h => ⟨h.1.1.edi, h.1.2.1.edi⟩) (fun _ _ h => h)
    have hwp := ct.wp (fun _ _ h =>
      ⟨WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) (fun _ k => (k.1.ctx h.1.1).edi),
       WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) (fun _ k => (k.1.ctx h.1.2.1).edi)⟩)
    exact hwp.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    RelCT isa (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (Impl.X25519.X86.freeze 64 ++ recoverParity)) s fun t =>
        Ctx base t ∧ t.zf = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.ctx h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.edi, h.2.1.edi⟩)
    (fun _ _ h => h)
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.X86
