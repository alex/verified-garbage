import VerifiedGarbage.Proof.Ed25519.X86.PointCTBatch
import VerifiedGarbage.Proof.Ed25519.X86.PointMul

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
