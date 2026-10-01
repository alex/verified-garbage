import VerifiedGarbage.Impl.Zeroize.Arm
import VerifiedGarbage.Proof.Zeroize.Common32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Zeroize.Contract

namespace VG.Proof.Zeroize.Arm
open VG VG.Arm RegUpd VG.Impl.Zeroize.Arm

syntax "zrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| zrun) => `(tactic| zrun [])
  | `(tactic| zrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        Op2.eval, isa, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg,
        State.load32, State.store32, State.load8, State.store8,
        subFlags, addFlags, ite_true, ite_false, Option.map_some, Option.some.injEq,
        exists_eq_left', true_and, and_true, reduceCtorEq, $ls,*]))

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩] ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  post s t := Spec.Zeroize.bytesAt t.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
    Spec.Zeroize.zeros (s.gpr .r1).toNat
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .r2 = 0 ∧ s.gpr .r0 = s₀.gpr .r0 + BitVec.ofNat 32 i ∧
  Prefix s.mem (State.addr (s₀.gpr .r0)) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 4 else 1) ≤ (s₀.gpr .r1).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 4 else 1)) t ∧
      t.gpr .r3 = s.gpr .r3 - 1 ∧ t.gpr .r1 = s.gpr .r1 ∧
      t.z = (s.gpr .r3 - 1 == 0) := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .r1).isLt
  have hc : (⟨State.addr (s₀.gpr .r0), (s₀.gpr .r1).toNat⟩ : Region).Contains
      (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) (if word then 4 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i) (if word then 4 else 1) :=
    ⟨_, by rw [hw, hp.2.1]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨State.addr (s₀.gpr .r0), (s₀.gpr .r1).toNat⟩ : Region)
  rw [← hp.2.1] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .r0 + BitVec.ofNat 32 i + BitVec.ofNat 32 k =
      s₀.gpr .r0 + BitVec.ofNat 32 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  have haddr : State.addr (s₀.gpr .r0 + BitVec.ofNat 32 i) =
      State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i :=
    addr_add (by have := hp.2.2; cases word <;> simp_all only [↓reduceIte, Bool.false_eq_true] <;> omega)
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    zrun [hd, ha, hs, Inv, hw, haddr,
      (show (0 : BitVec 32).setWidth 8 = 0 from rfl),
      (show ∀ a : BitVec 32, a + BitVec.ofNat 32 0 = a from BitVec.add_zero)]
  · exact ⟨hadd _, prefix_writeW hz (by omega), hf.writeW hmem _ hc⟩
  · exact ⟨hadd _, prefix_writeW hz (by omega), hf.writeW hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 4 else 1) * n ≤ (s₀.gpr .r1).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .r3 = BitVec.ofNat 32 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 4 else 1) * n) t ∧ t.gpr .r1 = s.gpr .r1 := by
  have hlt : n < 2 ^ 32 := by
    have := (s₀.gpr .r1).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  have start : WP isa (.block [.cmp .r3 (.imm 0)]) s fun t =>
      Inv s₀ i t ∧ t.gpr .r3 = BitVec.ofNat 32 n ∧ t.gpr .r1 = s.gpr .r1 ∧
      t.z = (BitVec.ofNat 32 n == 0) := by
    zrun [Inv, hc, (show ∀ a : BitVec 32, a - 0 = a from BitVec.sub_zero)]
    exact h
  unfold loop
  refine WP.seq (WP.mono start fun t ⟨ht, hct, hst, hz⟩ => ?_)
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, hz]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hst
  · have hne : BitVec.ofNat 32 n ≠ (0 : BitVec 32) := by bv_omega
    refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + (if word then 4 else 1) * j) t ∧ t.gpr .r3 = BitVec.ofNat 32 (n-j) ∧
      t.gpr .r1 = s.gpr .r1) ?_ n t ?_
    · intro rem u ⟨j, hj, hr, hu, hcu, hsu⟩
      refine WP.mono (step_ok word s₀ u hp _ ?_ hu) fun v ⟨hv, hcv, hsv, hzv⟩ => ?_
      · cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn ⊢ <;> omega
      have hpred : BitVec.ofNat 32 (n-j) - 1 = BitVec.ofNat 32 (n-(j+1)) := by bv_omega
      rw [hcu, hpred] at hcv hzv
      have hoff : i + (if word then 4 else 1) * j + (if word then 4 else 1) =
          i + (if word then 4 else 1) * (j+1) := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hv
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [eval, hzv, hend], ?_⟩
        rw [hend] at hv
        exact ⟨hv, hsv.trans hsu⟩
      · right
        have hnz : BitVec.ofNat 32 (n-(j+1)) ≠ (0 : BitVec 32) := by bv_omega
        refine ⟨by simp only [eval, hzv, beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega,
          j+1, by omega, rfl, hv, hcv, hsv.trans hsu⟩
    · exact ⟨0, by omega, by omega, by simpa using ht, by simpa using hct, hst⟩

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .r1).toNat
  have start : WP isa (.block [.mov .r2 (.imm 0), .mov .r3 (.shifted .r1 .lsr 2),
      .dp .and .r1 .r1 (.imm 3)]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .r3 = BitVec.ofNat 32 (n / 4) ∧
      t.gpr .r1 = BitVec.ofNat 32 (n % 4) := by
    zrun [Inv, Prefix, count32, tail32,
      (show ∀ p : BitVec 32, p + BitVec.ofNat 32 0 = p from BitVec.add_zero)]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl, rfl⟩
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ t hp 0 (n / 4) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.mov .r3 (.reg .r1)]) u fun v =>
      Inv s₀ (4 * (n / 4)) v ∧ v.gpr .r3 = BitVec.ofNat 32 (n % 4) := by
    zrun [Inv, hsu, hs]
    change Inv s₀ (4 * (n / 4)) u
    simpa only [Nat.zero_add, ↓reduceIte] using hu
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv⟩ => ?_)
  refine WP.mono (loop_ok false s₀ v hp (4 * (n / 4)) (n % 4) (by dsimp [n]; omega) hv hcv)
    fun w ⟨hw, _⟩ => ?_
  have hn : 4 * (n / 4) + (if false then 4 else 1) * (n % 4) = n := by simp; omega
  rw [hn] at hw
  exact ⟨prefix_spec hw.2.2.2.1, hw.2.2.2.2⟩

def sat : State where
  gpr _ := 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he⟩, ho⟩
    intro r hr
    have hc : zeroize.allInstrs (fun i => preserved.all (fun r => dstOf i != some r)) = true := by decide +kernel
    rw [Code.allInstrs_eq] at hc
    apply Exec.gpr (fun i hi => ?_) he
    simpa only [bne, Bool.not_eq_true', beq_eq_false_iff_ne] using
      List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
    intro s t _ _ h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs,
      reduceClassify, Loc.val, State.addr] [sat] using sat

end VG.Proof.Zeroize.Arm
