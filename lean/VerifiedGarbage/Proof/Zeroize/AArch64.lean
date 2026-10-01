import VerifiedGarbage.Impl.Zeroize.AArch64
import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.Ct.AArch64
import VerifiedGarbage.Spec.Zeroize.Contract

namespace VG.Proof.Zeroize.AArch64
open VG VG.AArch64 VG.Impl.Zeroize.AArch64 RegUpd

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  post s t := Spec.Zeroize.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    Spec.Zeroize.zeros (s.gpr .x1).toNat
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .x2 = 0 ∧ s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 i ∧
  Prefix s.mem (s₀.gpr .x0) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 8 else 1) ≤ (s₀.gpr .x1).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 8 else 1)) t ∧
      t.gpr .x3 = s.gpr .x3 - 1 ∧ t.gpr .x1 = s.gpr .x1 := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .x1).isLt
  have hc : (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr (s₀.gpr .x0 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    ⟨_, by rw [hw, hp.2]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region)
  rw [← hp.2] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .x0 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .x0 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    crun [hd, ha, hs, Inv, hw, State.store,
      (show (0 : BitVec 64).setWidth 32 = 0 from rfl),
      (show (0 : BitVec 32).setWidth 8 = 0 from rfl)]
  · exact ⟨hadd _, prefix_write hz (by dsimp [Size.bytes]; omega), hf.write hmem _ hc⟩
  · exact ⟨hadd _, prefix_write hz (by dsimp [Size.bytes]; omega), hf.write hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 8 else 1) * n ≤ (s₀.gpr .x1).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .x3 = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 8 else 1) * n) t ∧ t.gpr .x1 = s.gpr .x1 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .x1).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  unfold loop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, State.read, hc]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .x1 = s.gpr .x1)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, hc, beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + (if word then 8 else 1) * j) t ∧ t.gpr .x3 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .x1 = s.gpr .x1) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      refine WP.mono (step_ok word s₀ t hp _ ?_ ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      · cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn ⊢ <;> omega
      have hpred : BitVec.ofNat 64 (n-j) - 1 = BitVec.ofNat 64 (n-(j+1)) := by bv_omega
      rw [hct, hpred] at hcu
      have hoff : i + (if word then 8 else 1) * j + (if word then 8 else 1) =
          i + (if word then 8 else 1) * (j+1) := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [eval, State.read, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [eval, State.read, BitVec.setWidth_eq, hcu, bne, beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega,
          j+1, by omega, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega, by omega, by simpa using h, by simpa using hc, rfl⟩

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .x1).toNat
  have start : WP isa (.block [.movz .x .x2 0 0, .lsr .x .x3 .x1 3, .movz .x .x4 7 0,
      .logic .and .x .x1 .x1 .x4]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .x3 = BitVec.ofNat 64 (n / 8) ∧
      t.gpr .x1 = BitVec.ofNat 64 (n % 8) := by
    crun [Inv, Prefix, count, (show BitVec.setWidth 64 (7#16) = (7 : BitVec 64) from rfl), tail]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl, tail _⟩
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ t hp 0 (n / 8) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.addImm .x .x3 .x1 0]) u fun v =>
      Inv s₀ (8 * (n / 8)) v ∧ v.gpr .x3 = BitVec.ofNat 64 (n % 8) := by
    crun [Inv, hsu, hs]
    change Inv s₀ (8 * (n / 8)) u
    simpa only [Nat.zero_add, ↓reduceIte] using hu
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv⟩ => ?_)
  refine WP.mono (loop_ok false s₀ v hp (8 * (n / 8)) (n % 8) (by dsimp [n]; omega) hv hcv)
    fun w ⟨hw, _⟩ => ?_
  have hn : 8 * (n / 8) + (if false then 8 else 1) * (n % 8) = n := by simp; omega
  rw [hn] at hw
  exact ⟨prefix_spec hw.2.2.2.1, hw.2.2.2.2⟩

def sat : State where
  gpr _ := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he⟩, ho⟩
    intro r hr
    have hc := instrs_keeps (c := zeroize) (rs := preserved) (by decide +kernel)
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs] [sat] using sat
end VG.Proof.Zeroize.AArch64
