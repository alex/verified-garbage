import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTFinish

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem baseWr_agree {s t : State} (hs : scalarBaseLocal.pre s) (ht : scalarBaseLocal.pre t)
    (hp : scalarBaseLocal.pub s t) : s.wr = t.wr := by
  rw [hs.2.1, ht.2.1, hp.2.1, hp.2.2.2]

def BaseCTReady (s₀ s : State) : Prop :=
  Saved s₀ (arg s₀ 2) s ∧ MulCTInput (arg s₀ 2) (baseScalar s₀) 16 s

theorem scalarBaseTail_ct (s₀ t₀ : State) (hs : scalarBaseLocal.pre s₀) (ht : scalarBaseLocal.pre t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
      (.seq (pointMultiply 16) (.seq pointEncode (.block (finishWords 96)))) (fun _ _ => True) := by
  have hwr := baseWr_agree hs ht hp
  have mulct := (pointMultiply_ct (arg s₀ 2) (baseScalar s₀) (baseScalar t₀) 16 (Or.inl rfl)).mono
    (P' := fun (s t : State) => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
    (fun _ _ h => ⟨h.1.2, hp.2.2.2.symm ▸ h.2.2,
      h.1.1.wr.trans (hwr.trans h.2.1.wr.symm)⟩) (fun _ _ h => h)
  have mw (u s : State) (h : BaseCTReady u s) : WP isa (pointMultiply 16) s (Saved u (arg u 2)) := by
    refine WP.mono (pointMultiply_ok h.2.ctx.ctx (baseScalar u) 16 (by decide) (by decide)
      h.2.bound h.2.bits h.2.d) fun t ⟨kt, _, _⟩ => ?_
    exact h.1.mulkeep h.2.ctx.ctx.fit kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s h.1, mw t₀ t h.2⟩)
  have encct := pointEncode_ct.mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => h.1.edi.trans (hp.2.2.2.trans h.2.edi.symm)) (fun _ _ h => h)
  have ew (u s : State) (hu : scalarBaseLocal.pre u) (h : Saved u (arg u 2) s) :
      WP isa pointEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (pointEncode_ok (h.ctx pu.fit pu.wr)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (scalarBaseFinish_ct s₀ t₀ hs ht hp))

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns scalarBaseStart_ct
    (fun _ _ h => ⟨scalarBaseStart_ok h.1, scalarBaseStart_ok h.2.1⟩)
  rw [scalarBase]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact scalarBaseTail_ct u v hp.1 hp.2.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

end VG.Proof.Ed25519.X86
