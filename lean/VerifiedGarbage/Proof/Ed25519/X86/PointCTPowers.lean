import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.PointPowersLoop

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
