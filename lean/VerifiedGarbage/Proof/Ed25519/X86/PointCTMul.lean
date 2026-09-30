import VerifiedGarbage.Proof.Ed25519.X86.PointCTMulLoop

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

private theorem pointMultiplyInit_ct (x : BitVec 32) (count : Nat) (hn : count = 16 ∨ count = 32) :
    RelCT isa (PowersCTStart x) (pointMultiplyInit count) (fun _ _ => True) := by
  have hn0 : 0 < count := by omega
  have hn32 : count ≤ 32 := by omega
  have bodyct : RelCT isa (PowersCTPre x) (powersBody 1024 count true) (fun _ _ => True) := by
    rcases hn with rfl | rfl
    · exact powersBody16_ct x
    · exact powersBody32_ct x
  have hp := pointPowers_ct x 1024 count true (by decide) (by omega) hn0 hn32 bodyct
  have hh := ctWithRuns hp (fun _ _ h => ⟨pointPowers_ok true h.1.ctx 1024 count (by decide) (by omega)
    hn0 hn32 h.2.2.2.1, pointPowers_ok true h.2.1.ctx 1024 count (by decide) (by omega)
    hn0 hn32 h.2.2.2.2⟩)
  have ht : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
      (.seq (.block (constPoint Spec.Ed25519.identity)) (.block (mulCounterInit count))) (fun _ _ => True) := by
    rcases hn with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
      intro s t h
      exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)
  rw [pointMultiplyInit]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) ht
  intro s t ⟨_, a, b, h, hs, ht⟩
  exact (hs.1.ctx h.1.ctx).edi.trans (ht.1.ctx h.2.1.ctx).edi.symm

structure MulCTInput (x : BitVec 32) (scalar count : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  bound : scalar < 2 ^ (16 * count)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

theorem pointMultiply_ct (x : BitVec 32) (a b count : Nat) (hn : count = 16 ∨ count = 32) :
    RelCT isa (fun s t => MulCTInput x a count s ∧ MulCTInput x b count t ∧ s.wr = t.wr)
      (pointMultiply count) (fun _ _ => True) := by
  have hn0 : 0 < count := by omega
  have hn32 : count ≤ 32 := by omega
  have init := (pointMultiplyInit_ct x count hn).mono
    (P' := fun (s t : State) => MulCTInput x a count s ∧ MulCTInput x b count t ∧ s.wr = t.wr)
    (fun _ _ h => ⟨h.1.ctx, h.2.1.ctx, h.2.2, h.1.d, h.2.1.d⟩) (fun _ _ h => h)
  have hw (s : State) (scalar : Nat) (h : MulCTInput x scalar count s) :
      WP isa (pointMultiplyInit count) s fun t =>
        MulCTState x scalar count (point (env s.mem x) 0 1 2 3) count t ∧ t.wr = s.wr := by
    refine WP.mono (pointMultiplyInit_ok h.ctx.ctx count hn0 hn32 h.d) fun t ⟨kt, it, pt, tt, dt⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, it,
      pt.trans (after_top scalar (16 * count) _ h.bound).symm, tt,
      fun i hi => (kt.bit h.ctx.ctx i (by omega)).trans (h.bits i hi), dt⟩, kt.wr⟩
  have hh := ctWithRuns init (fun s t h => ⟨hw s a h.1, hw t b h.2.1⟩)
  rw [pointMultiply]
  refine VG.RelCT.seq hh ?_
  intro s t ts tt s' t' ⟨_, u, v, h, hs, ht⟩ es et
  exact pointMulLoop_ct x a b count _ _ hn32 count _ _ _ _ _ _
    ⟨hn0, Nat.le_refl _, hs.1, ht.1, hs.2.trans (h.2.2.trans ht.2.symm)⟩ es et

end VG.Proof.Ed25519.X86
