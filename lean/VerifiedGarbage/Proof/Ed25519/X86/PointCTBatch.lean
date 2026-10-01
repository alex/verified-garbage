import VerifiedGarbage.Proof.Ed25519.X86.PointCTPowers
import VerifiedGarbage.Proof.Ed25519.X86.PointMulCounter

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem prepareBatch_ct (x : BitVec 32) (j : Nat) (hj : j < 32) :
    RelCT isa (fun s t => PowersCTStart x s t ∧ s.gpr .esi = BitVec.ofNat 32 j ∧ t.gpr .esi = BitVec.ofNat 32 j)
      prepareBatch (fun _ _ => True) := by
  have hl : RelCT isa (fun s t => PowersCTStart x s t ∧ s.gpr .esi = BitVec.ofNat 32 j ∧ t.gpr .esi = BitVec.ofNat 32 j)
      (.block loadCheckpoint) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.ctx.edi.trans h.1.2.1.ctx.edi.symm
    · exact h.2.1.trans h.2.2.symm
  have hw (s : State) (h : PointCTCtx x s) (hb : s.gpr .esi = BitVec.ofNat 32 j)
      (hd : env s.mem x 16 = Spec.Ed25519.d) :
      WP isa (.block loadCheckpoint) s fun t => PointCTCtx x t ∧ t.wr = s.wr ∧ env t.mem x 16 = Spec.Ed25519.d := by
    refine WP.mono (loadCheckpoint_ok h.ctx j hj hb) fun t ⟨kt, _, _, dt⟩ => ?_
    exact ⟨h.keep kt.keep.edi kt.keep.wr, kt.keep.wr, dt.trans hd⟩
  have hh := ctWithRuns hl (fun s t h => ⟨hw s h.1.1 h.2.1 h.1.2.2.2.1,
    hw t h.1.2.1 h.2.2 h.1.2.2.2.2⟩)
  have hp := pointPowers_ct x 5120 16 false (by decide) (by decide) (by decide) (by decide) (powersBodyLocal_ct x)
  have hp' := ctWithRuns hp (fun s t h => ⟨pointPowers_ok false h.1.ctx 5120 16 (by decide) (by decide)
    (by decide) (by decide) h.2.2.2.1, pointPowers_ok false h.2.1.ctx 5120 16 (by decide) (by decide)
    (by decide) (by decide) h.2.2.2.2⟩)
  have hr : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) (.block restorePoint) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)
  rw [prepareBatch]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) (VG.RelCT.seq (hp'.mono (fun _ _ h => h) ?_) hr)
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact ⟨hs.1, ht.1, hs.2.1.trans (hp.1.2.2.1.trans ht.2.1.symm), hs.2.2, ht.2.2⟩
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact (hs.1.ctx hp.1.ctx).edi.trans (ht.1.ctx hp.2.1.ctx).edi.symm

structure BatchCTState (x : BitVec 32) (j : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  counter : wd s.mem x 28 = BitVec.ofNat 32 j
  d : env s.mem x 16 = Spec.Ed25519.d

theorem pointMulBatch_ct (x : BitVec 32) (j : Nat) (hj : j < 32) :
    RelCT isa (fun s t => BatchCTState x (j + 1) s ∧ BatchCTState x (j + 1) t ∧ s.wr = t.wr)
      pointMulBatch (fun _ _ => True) := by
  have hb : RelCT isa (fun s t => BatchCTState x (j + 1) s ∧ BatchCTState x (j + 1) t ∧ s.wr = t.wr)
      (.block batchBegin) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ (h.1.ctx.ctx.edi.trans h.2.1.ctx.ctx.edi.symm))
  have hw (s : State) (h : BatchCTState x (j + 1) s) : WP isa (.block batchBegin) s fun t =>
      BatchCTState x j t ∧ t.gpr .esi = BitVec.ofNat 32 j ∧ t.wr = s.wr := by
    refine WP.mono (batchBegin_ok h.ctx.ctx j h.counter) fun t ⟨kt, bt, it, ft⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, it, by rw [counter28_env h.ctx.ctx.fit ft]; exact h.d⟩, bt, kt.wr⟩
  have hh := ctWithRuns hb (fun s t h => ⟨hw s h.1, hw t h.2.1⟩)
  have prep := (prepareBatch_ct x j hj).mono
    (P' := fun (s t : State) => BatchCTState x j s ∧ BatchCTState x j t ∧ s.wr = t.wr ∧
      s.gpr .esi = BitVec.ofNat 32 j ∧ t.gpr .esi = BitVec.ofNat 32 j)
    (fun _ _ h => ⟨⟨h.1.ctx, h.2.1.ctx, h.2.2.1, h.1.d, h.2.1.d⟩, h.2.2.2⟩) (fun _ _ h => h)
  have pw (s : State) (h : BatchCTState x j s) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
      WP isa prepareBatch s fun t => BatchCTState x j t ∧ t.wr = s.wr := by
    refine WP.mono (prepareBatch_ok h.ctx.ctx j hj hb h.d) fun t ⟨kt, _, _, dt⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, (kt.batch_index h.ctx.ctx).trans h.counter, dt⟩, kt.wr⟩
  have prep' := ctWithRuns prep (fun s t h => ⟨pw s h.1 h.2.2.2.1, pw t h.2.1 h.2.2.2.2⟩)
  have test : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) (.block batchTest) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)
  rw [pointMulBatch]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_)
    (VG.RelCT.seq (prep'.mono (fun _ _ h => h) ?_) (VG.RelCT.seq (accumulate16_ct_regs x) test))
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact ⟨hs.1, ht.1, hs.2.2.trans (hp.2.2.trans ht.2.2.symm), hs.2.1, ht.2.1⟩
  · intro s t ⟨_, a, b, hp, hs, ht⟩
    exact ⟨hs.1.ctx, ht.1.ctx, hs.2.trans (hp.2.2.1.trans ht.2.symm), hs.1.counter.trans ht.1.counter.symm⟩

end VG.Proof.Ed25519.X86
