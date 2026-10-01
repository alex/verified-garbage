import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts

namespace VG.Proof.Sha3.AArch64.Scalar.Control
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Control
open VG.Proof.Sha3.AArch64

structure ConstantKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x26 → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem constant_ok (v : BitVec 64) (s : State) :
    WP isa (.block (constant v)) s fun s' =>
      ConstantKeep s s' ∧ s'.gpr .x26 = Sha3.Vector.constantLow v := by
  by_cases h1 : v.extractLsb' 16 16 = 0 <;>
    by_cases h2 : v.extractLsb' 32 16 = 0 <;>
    by_cases h3 : v.extractLsb' 48 16 = 0
  all_goals
    simp only [constant, h1, h2, h3, ite_true, ite_false,
      List.cons_append, List.nil_append]
    repeat' apply WP.cons rfl
    apply wp_nil
    refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · intro r hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [Sha3.Vector.constantLow, h1, h2, h3, ite_true, ite_false,
        Sha3.Vector.movkValue, RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

/-- A finite counted-loop rule. The caller supplies the proved body, including
its iota operation; no unrolling of the 24-round machine program is required. -/
theorem loop_ok (core : List Instr) (Inv : Nat → State → Prop)
    (hb : ∀ k s, k < 24 → Inv k s →
      WP isa (body core) s (Inv (k + 1)))
    (ht : ∀ k s, 0 < k → k ≤ 24 → Inv k s →
      isa.eval (.nonzero .x .x27) s = some (decide (k < 24)))
    (s : State) (hs : Inv 0 s) : WP isa (loop core) s (Inv 24) := by
  unfold loop
  refine WP.loop (M := isa) (body := body core) (c := .nonzero .x .x27)
    (Q := Inv 24) (fun n (q : State) => ∃ k, k < 24 ∧ n = 24 - k ∧ Inv k q) ?_ 24 s
    ⟨0, by decide, rfl, hs⟩
  · intro n q ⟨k, hk, hn, hq⟩
    refine WP.mono (hb k q hk hq) ?_
    intro q' hq'
    have hp : 0 < k + 1 := by omega
    have hl : k + 1 ≤ 24 := by omega
    have hc := ht (k + 1) q' hp hl hq'
    by_cases he : k + 1 = 24
    · left
      exact ⟨by simpa only [he, Nat.lt_irrefl, decide_false] using hc,
        by simpa only [he] using hq'⟩
    · right
      have hk' : k + 1 < 24 := by omega
      refine ⟨by simpa only [hk', decide_true] using hc, 24 - (k + 1), by omega, ?_⟩
      exact ⟨k + 1, hk', rfl, hq'⟩


open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector

def constAddr (orig : State) (i : Nat) : Addr := orig.gpr .x1 + BitVec.ofNat 64 (128 + 8*i)

def Constants (orig : State) (k : Nat) (m : Mem) : Prop :=
  ∀ i < k, m.readW (constAddr orig i) 64 = Spec.Sha3.RC i

structure SetupInv (orig : State) (A : Spec.Sha3.State) (k : Nat) (s : State) : Prop where
  core : CoreState orig A s
  base : s.gpr .x28 = orig.gpr .x1
  vals : Constants orig k s.mem

theorem constant_contains (orig : State) {i : Nat} (hi : i < 24) :
    (⟨orig.gpr .x1,512⟩ : Region).Contains (constAddr orig i) 8 :=
  Offset.contains_base _ (by omega) (by omega)

theorem setup_constants_ok (orig : State) (A : Spec.Sha3.State) (s : State)
    (hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : SetupInv orig A 0 s) :
    WP isa (.block ((List.range 24).flatMap constantStore)) s (SetupInv orig A 24) := by
  refine wp_range_flatMap (M := isa) (SetupInv orig A) (fun i s hi hs => ?_)
    24 (Nat.le_refl _) s hs
  unfold constantStore
  rw [WP.block_append_iff]
  refine (constant_ok (Spec.Sha3.RC i) s).mono fun q ⟨hkeep,hval⟩ => ?_
  rw [constantLow_RC i hi] at hval
  have hbase : q.gpr .x28 = orig.gpr .x1 :=
    (hkeep.gpr .x28 (by decide)).trans hs.base
  refine WP.cons (exec_str_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
  · rw [hkeep.wr, hs.core.keep.wr, hbase]
    exact hp.in_wr (.inr rfl) (constant_contains orig hi)
  · refine ⟨⟨?_,?_,?_,?_,?_⟩,hbase,?_⟩
    · exact ⟨hkeep.rd.trans hs.core.keep.rd,hkeep.wr.trans hs.core.keep.wr,
        hkeep.sp.trans hs.core.keep.sp⟩
    · simpa only [Boundary.Ptrs, hkeep.vec] using hs.core.ptrs
    · intro j hj
      change (q.mem.writeW _ _).readW _ 64 = _
      rw [hbase, hval, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      rw [hkeep.mem]
      exact hs.core.saved j hj
    · intro r hr
      rw [hkeep.vec]
      exact hs.core.vec r hr
    · intro j hj
      change q.gpr (VG.Impl.Sha3.AArch64.Scalar.laneReg j) = _
      rw [hkeep.gpr _ ((scratch_not_lane .x26 (by simp) j hj))]
      exact hs.core.lanes j hj
    · intro j hj
      change (q.mem.writeW _ _).readW _ 64 = _
      simp only [constAddr]
      rw [hbase,hval]
      by_cases he : j = i
      · subst j
        exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),hkeep.mem]
        exact hs.vals j (by omega)

structure Ready (orig : State) (A : Spec.Sha3.State) (k : Nat) (s : State) : Prop where
  core : CoreState orig A s
  constants : Constants orig 24 s.mem
  next : vdword (s.v .v26) 0 = constAddr orig k
  limit : vdword (s.v .v27) 0 = constAddr orig 24

theorem setup_ok (orig : State) (A : Spec.Sha3.State) (s : State)
    (hp : VG.Proof.Sha3.AArch64.Pre orig) (hs : CoreState orig A s) :
    WP isa (.block setup) s (Ready orig A 0) := by
  unfold setup
  simp only [List.cons_append,List.nil_append]
  refine WP.cons (exec_umov_low s .x28 .v31) ?_
  rw [WP.block_append_iff]
  have hu : SetupInv orig A 0 (s.write .x .x28 (vdword (s.v .v31) 0)) := by
    refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,fun i hi => by omega⟩
    · exact ⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩
    · exact hs.ptrs
    · exact hs.saved
    · exact hs.vec
    · intro i hi
      simp only [RegUpd.gpr_write, scratch_not_lane .x28 (by simp) i hi, ite_false]
      exact hs.lanes i hi
    · simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq] using hs.ptrs.2
  refine (setup_constants_ok orig A _ hp hu).mono fun q hq => ?_
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (wp_nil ?_))))
  refine ⟨⟨?_,?_,?_,?_,?_⟩,hq.vals,?_,?_⟩
  · exact ⟨hq.core.keep.rd,hq.core.keep.wr,hq.core.keep.sp⟩
  · simp only [Boundary.Ptrs,RegUpd.v_setV,reduceCtorEq,ite_false]
    exact hq.core.ptrs
  · exact hq.core.saved
  · intro r hr
    have hn : ∀ r ∈ preservedV, r ≠ .v26 ∧ r ≠ .v27 := by decide
    simp only [RegUpd.v_write,RegUpd.v_setV,(hn r hr).1,(hn r hr).2,ite_false]
    exact hq.core.vec r hr
  · intro i hi
    simp only [RegUpd.gpr_setV,RegUpd.gpr_write,
      scratch_not_lane .x26 (by simp) i hi,ite_false]
    exact hq.core.lanes i hi
  · simp only [RegUpd.v_write,RegUpd.v_setV,reduceCtorEq,ite_false,ite_true,vdword_ofVDwords_0,
      RegUpd.gpr_setV,RegUpd.gpr_write,ite_false,ite_true,State.read,Size.bits,
      BitVec.setWidth_eq,hq.base,constAddr,Nat.mul_zero,Nat.add_zero]
  · simp only [RegUpd.v_write,RegUpd.v_setV,reduceCtorEq,ite_true,vdword_ofVDwords_0,
      RegUpd.gpr_setV,RegUpd.gpr_write,ite_false,ite_true,State.read,Size.bits,
      BitVec.setWidth_eq,hq.base,constAddr]

end VG.Proof.Sha3.AArch64.Scalar.Control
