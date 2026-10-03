import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86.PointMul

/-! Merged from `Proof.Ed25519.X86.PointCTBatch`. -/
section
/-! Merged from `Proof.Ed25519.X86.PointCTPowers`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure PowersCTState (x : BitVec 32) (j : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  counter : wd s.mem x 24 = BitVec.ofNat 32 j
  d : env s.mem x 16 = Spec.Ed25519.d

def PowersCTInv (x : BitVec 32) (count n : Nat) (s t : State) : Prop :=
  0 < n ∧ n ≤ count ∧ PowersCTState x (count - n) s ∧ PowersCTState x (count - n) t ∧ s.wr = t.wr

theorem powersLoop_ct (x : BitVec 32) (o count : Nat) (batch : Bool)
    (hlo : 928 ≤ o) (hfit : o + 128 * count ≤ 8192) (hn : count ≤ 32)
    (hc : RelCT isa (PowersCTPre x) (powersBody o count batch) (fun _ _ => True)) (n : Nat) :
    RelCT isa (PowersCTInv x count n) (.loop (powersBody o count batch) .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (PowersCTInv x count) (n := n)
  intro n
  have hb : RelCT isa (PowersCTInv x count n) (powersBody o count batch) (fun _ _ => True) :=
    hc.mono (fun _ _ h => ⟨h.2.2.1.ctx, h.2.2.2.1.ctx, h.2.2.2.2,
      h.2.2.1.counter.trans h.2.2.2.1.counter.symm⟩) (fun _ _ h => h)
  have hw (s : State) (h : PowersCTState x (count - n) s) (h0 : 0 < n) (hle : n ≤ count) :
      WP isa (powersBody o count batch) s fun t =>
        PowersCTState x (count - n + 1) t ∧ t.wr = s.wr ∧
          isa.eval .ne t = some (!decide (count - n + 1 = count)) := by
    refine WP.mono (powersBody_ok h.ctx.ctx o count (count - n) batch (by omega) hn hlo hfit
      h.counter h.d) fun t ⟨kt, it, zt, _, _, dt⟩ => ?_
    exact ⟨⟨h.ctx.keep kt.edi kt.wr, it, (dt 16 (by decide)).trans h.d⟩, kt.wr, zt⟩
  have hh := ctWithRuns hb (fun s t h => ⟨hw s h.2.2.1 h.1 h.2.1, hw t h.2.2.2.1 h.1 h.2.1⟩)
  apply hh.mono (fun _ _ h => h)
  intro s t ⟨_, a, b, hp, hs, ht⟩
  refine ⟨hs.2.2.trans ht.2.2.symm, fun _ => trivial, ?_⟩
  intro hz
  have hpos := hp.1
  have hle := hp.2.1
  rw [hs.2.2] at hz
  have hn1 : 1 < n := by
    by_contra hn1
    have he : count - n + 1 = count := by omega
    simp only [he, decide_true, Bool.not_true, Option.some.injEq] at hz
    cases hz
  have he : count - (n - 1) = count - n + 1 := by omega
  exact ⟨n - 1, by omega, by omega, by omega, he ▸ hs.1, he ▸ ht.1,
    hs.2.1.trans (hp.2.2.2.2.trans ht.2.1.symm)⟩

def PowersCTStart (x : BitVec 32) (s t : State) : Prop :=
  PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧
    env s.mem x 16 = Spec.Ed25519.d ∧ env t.mem x 16 = Spec.Ed25519.d

theorem pointPowers_ct (x : BitVec 32) (o count : Nat) (batch : Bool)
    (hlo : 928 ≤ o) (hfit : o + 128 * count ≤ 8192) (hn0 : 0 < count) (hn : count ≤ 32)
    (hc : RelCT isa (PowersCTPre x) (powersBody o count batch) (fun _ _ => True)) :
    RelCT isa (PowersCTStart x) (pointPowers o count batch) (fun _ _ => True) := by
  have hi : RelCT isa (PowersCTStart x)
      (.block [.mov .eax (.imm 0), .store (Impl.X25519.X86.sc 24) .eax]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ (h.1.ctx.edi.trans h.2.1.ctx.edi.symm))
  have hw (s : State) (h : PointCTCtx x s) (hd : env s.mem x 16 = Spec.Ed25519.d) :
      WP isa (.block [.mov .eax (.imm 0), .store (Impl.X25519.X86.sc 24) .eax]) s fun t =>
        PowersCTState x 0 t ∧ t.wr = s.wr := by
    refine WP.mono (powersInit_ok h.ctx o (128 * count)) fun t ⟨kt, it, ft⟩ => ?_
    exact ⟨⟨h.keep kt.edi kt.wr, it, by rw [counter_env h.ctx.fit ft]; exact hd⟩, kt.wr⟩
  have hh := ctWithRuns hi (fun s t h => ⟨hw s h.1 h.2.2.2.1, hw t h.2.1 h.2.2.2.2⟩)
  rw [pointPowers]
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) (powersLoop_ct x o count batch hlo hfit hn hc count)
  intro s t ⟨_, a, b, hp, hs, ht⟩
  exact ⟨hn0, Nat.le_refl _, (Nat.sub_self count).symm ▸ hs.1,
    (Nat.sub_self count).symm ▸ ht.1, hs.2.trans (hp.2.2.1.trans ht.2.symm)⟩

end VG.Proof.Ed25519.X86
end

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
end

/-! Merged from `Proof.Ed25519.X86.PointCTMulLoop`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulCTState (x : BitVec 32) (scalar count : Nat) (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  counter : wd s.mem x 28 = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = after scalar p (16 * n)
  table : ∀ j < count, tablePoint s.mem x (1024 + 128 * j) = powerPoint p (16 * j)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

theorem mulCTState_step {x : BitVec 32} {s : State} {scalar count j : Nat} {p : Spec.Ed25519.Point}
    (h : MulCTState x scalar count p (j + 1) s) (hj : j < count) (hn : count ≤ 32) :
    WP isa pointMulBatch s fun t => MulCTState x scalar count p j t ∧ t.wr = s.wr ∧
      isa.eval .ne t = some (!decide (j = 0)) := by
  refine WP.mono (pointMulBatch_ok h.ctx.ctx scalar j p (by omega) h.counter
    (fun i hi => h.bits _ (by omega)) (h.table j hj) h.value h.d) fun t ⟨kt, it, zt, pt, dt⟩ => ?_
  refine ⟨⟨h.ctx.keep kt.edi kt.wr, it, pt, ?_, ?_, dt⟩, kt.wr, zt⟩
  · intro k hk
    exact (kt.checkpoint h.ctx.ctx k (by omega)).trans (h.table k hk)
  · intro i hi
    exact (kt.bit h.ctx.ctx i (by omega)).trans (h.bits i hi)

def MulCTInv (x : BitVec 32) (a b count : Nat) (p q : Spec.Ed25519.Point) (n : Nat) (s t : State) : Prop :=
  0 < n ∧ n ≤ count ∧ MulCTState x a count p n s ∧ MulCTState x b count q n t ∧ s.wr = t.wr

theorem pointMulLoop_ct (x : BitVec 32) (a b count : Nat) (p q : Spec.Ed25519.Point)
    (hn : count ≤ 32) (n : Nat) :
    RelCT isa (MulCTInv x a b count p q n) (.loop pointMulBatch .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (MulCTInv x a b count p q) (n := n)
  intro n
  by_cases hn0 : n = 0
  · subst n
    exact VG.RelCT.of_false (fun _ _ h => Nat.not_lt_zero _ h.1)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  by_cases hj : j < count
  · have hb := (pointMulBatch_ct x j (by omega)).mono
      (P' := MulCTInv x a b count p q (j + 1))
      (fun _ _ h => ⟨⟨h.2.2.1.ctx, h.2.2.1.counter, h.2.2.1.d⟩,
        ⟨h.2.2.2.1.ctx, h.2.2.2.1.counter, h.2.2.2.1.d⟩, h.2.2.2.2⟩) (fun _ _ h => h)
    have hh := ctWithRuns hb (fun _ _ h => ⟨mulCTState_step h.2.2.1 hj hn, mulCTState_step h.2.2.2.1 hj hn⟩)
    apply hh.mono (fun _ _ h => h)
    intro s t ⟨_, u, v, hp, hs, ht⟩
    refine ⟨hs.2.2.trans ht.2.2.symm, fun _ => trivial, ?_⟩
    intro hz
    have hj0 : 0 < j := by
      by_contra hzero
      have he : j = 0 := by omega
      rw [hs.2.2, he] at hz
      contradiction
    exact ⟨j, by omega, hj0, by omega, hs.1, ht.1,
      hs.2.1.trans (hp.2.2.2.2.trans ht.2.1.symm)⟩
  · exact VG.RelCT.of_false (fun _ _ h => hj (by have := h.2.1; omega))

end VG.Proof.Ed25519.X86
end

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
