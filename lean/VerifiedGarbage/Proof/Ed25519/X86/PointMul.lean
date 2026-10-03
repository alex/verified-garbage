import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame

/-! Merged from `Proof.Ed25519.X86.PointMulInit`. -/
section
/-! Checkpoints, identity accumulator and the public batch count. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem constPoint_d (p : Spec.Ed25519.Point) (e : Env) : evalOps (constPointOps p) e 16 = e 16 := rfl

theorem pointMultiplyInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointMultiplyInit count) s fun t => MulKeep x s t ∧
      wd t.mem x 28 = BitVec.ofNat 32 count ∧ point (env t.mem x) 0 1 2 3 = Spec.Ed25519.identity ∧
      (∀ j < count, tablePoint t.mem x (1024 + 128 * j) =
        powerPoint (point (env s.mem x) 0 1 2 3) (16 * j)) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (pointPowers_ok true hc 1024 count (by decide) (by omega) hn0 hn hd)
    fun a ⟨ka, ta, _, ha⟩ => ?_)
  have ca := ka.ctx hc
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) ca) fun b ⟨kb, eb⟩ => ?_)
  have cb := kb.ctx ca
  refine WP.mono (mulCounterInit_ok cb count) fun t ⟨kt, ft, it⟩ => ?_
  have et := counter28_env hc.fit ft
  have bt : BatchKeep x b t := BatchKeep.of_counter cb kt.edi kt.esp kt.rd kt.wr ft
  refine ⟨((MulKeep.of_powers hc ka (by decide) (by omega)).trans
    (MulKeep.of_ikeep ca (IKeep.of_field kb))).trans (MulKeep.of_batch cb bt), it, ?_, ?_, ?_⟩
  · rw [et, eb, constPoint_eval]
  · intro j hj
    rw [bt.checkpoint cb j (by omega), workspace_table (IKeep.of_field kb) ca _ (by omega) (by omega), ta j hj]
    rfl
  · rw [et, eb, constPoint_d, ha 16 (by decide), hd]

end VG.Proof.Ed25519.X86
end

/-! The whole scalar multiplication follows the specification's exact coordinates. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulInv (x : BitVec 32) (s₀ : State) (scalar count : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  keep : MulKeep x s₀ s
  counter : wd s.mem x 28 = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = after scalar p (16 * n)
  table : ∀ j < count, tablePoint s.mem x (1024 + 128 * j) = powerPoint p (16 * j)
  d : env s.mem x 16 = Spec.Ed25519.d

theorem multiplyLoop_ok {x : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (scalar count : Nat) (p : Spec.Ed25519.Point) (hc0 : 0 < count) (hc32 : count ≤ 32)
    (hcounter : wd s₀.mem x 28 = BitVec.ofNat 32 count)
    (hbits : ∀ i < 16 * count, s₀.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat)
    (htable : ∀ j < count, tablePoint s₀.mem x (1024 + 128 * j) = powerPoint p (16 * j))
    (hp : point (env s₀.mem x) 0 1 2 3 = after scalar p (16 * count))
    (hd : env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop pointMulBatch .ne) s₀ fun t => MulKeep x s₀ t ∧
      point (env t.mem x) 0 1 2 3 = Spec.Ed25519.pointMul scalar p ∧ env t.mem x 16 = Spec.Ed25519.d := by
  apply WP.loop (fun n => MulInv x s₀ scalar count p n) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    have cs := h.keep.ctx hc
    refine WP.mono (pointMulBatch_ok cs scalar j p (by omega) h.counter
      (fun i hi => (h.keep.bit hc _ (by omega)).trans (hbits _ (by omega)))
      (h.table j hj) h.value h.d) fun t ⟨kt, it, zt, pt, dt⟩ => ?_
    have kk := h.keep.trans (MulKeep.of_batch cs kt)
    have tt : ∀ k < count, tablePoint t.mem x (1024 + 128 * k) = powerPoint p (16 * k) :=
      fun k hk => (kt.checkpoint cs k (by omega)).trans (h.table k hk)
    by_cases hz : j = 0
    · subst j
      exact .inl ⟨by rw [zt]; rfl, kk, pt.trans (after_zero scalar p), dt⟩
    · exact .inr ⟨by rw [zt]; simp only [decide_eq_false hz]; rfl,
        j, by omega, ⟨by omega, by omega, kk, it, pt, tt, dt⟩⟩
  · exact ⟨hc0, Nat.le_refl _, MulKeep.refl _ _, hcounter, hp, htable, hd⟩

theorem pointMultiply_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (scalar count : Nat) (hc0 : 0 < count) (hc32 : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hbits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointMultiply count) s fun t => MulKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = Spec.Ed25519.pointMul scalar (point (env s.mem x) 0 1 2 3) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (pointMultiplyInit_ok hc count hc0 hc32 hd) fun u ⟨ku, iu, pu, tu, du⟩ => ?_)
  refine WP.mono (multiplyLoop_ok (ku.ctx hc) scalar count (point (env s.mem x) 0 1 2 3) hc0 hc32 iu
    (fun i hi => (ku.bit hc i (by omega)).trans (hbits i hi)) tu
    (pu.trans (after_top scalar (16 * count) _ hscalar).symm) du) fun t ⟨kt, pt, dt⟩ => ?_
  exact ⟨ku.trans kt, pt, dt⟩

end VG.Proof.Ed25519.X86
