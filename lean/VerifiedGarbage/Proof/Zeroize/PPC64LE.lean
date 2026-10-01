import VerifiedGarbage.Impl.Zeroize.PPC64LE
import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Zeroization on PPC64LE

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Zeroize.AArch64`).
-/

namespace VG.Proof.Zeroize.PPC64LE
open VG VG.PPC64LE VG.Impl.Zeroize.PPC64LE

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  post s t := Spec.Zeroize.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
    Spec.Zeroize.zeros (s.gpr .r4).toNat
  pub s t := s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .r5 = 0 ∧ s.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 64 i ∧
  Prefix s.mem (s₀.gpr .r3) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 8 else 1) ≤ (s₀.gpr .r4).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 8 else 1)) t ∧
      t.gpr .r6 = s.gpr .r6 - 1 ∧ t.gpr .r4 = s.gpr .r4 := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .r4).isLt
  have hc : (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region).Contains
      (s₀.gpr .r3 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr (s₀.gpr .r3 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    ⟨_, by rw [hw, hp.2]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region)
  rw [← hp.2] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .r3 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .r3 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    crun [hd, ha, hs, hw, Inv, (show (0 : BitVec 64).setWidth 8 = 0 from rfl)]
  · exact ⟨hadd _, prefix_write hz (by omega), hf.write hmem _ hc⟩
  · exact ⟨hadd _, prefix_write hz (by omega), hf.write hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 8 else 1) * n ≤ (s₀.gpr .r4).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 8 else 1) * n) t ∧ t.gpr .r4 = s.gpr .r4 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .r4).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  unfold loop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [VG.PPC64LE.eval, State.read, hc]) (fun _ => WP.block_nil ?_)
      (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .r4 = s.gpr .r4)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, hc,
      beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + (if word then 8 else 1) * j) t ∧ t.gpr .r6 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .r4 = s.gpr .r4) ?_ n s ?_
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
        refine ⟨by simp [VG.PPC64LE.eval, State.read, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, hcu, bne,
          beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega,
          j+1, by omega, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega, by omega, by simpa using h, by simpa using hc, rfl⟩

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .r4).toNat
  have start : WP isa (.block [.li .r5 0, .lsr .d .r6 .r4 3, .li .r7 7,
      .logic .and .r4 .r4 .r7]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .r6 = BitVec.ofNat 64 (n / 8) ∧
      t.gpr .r4 = BitVec.ofNat 64 (n % 8) := by
    crun [Inv, Prefix, count, tail]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl, tail _⟩
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ t hp 0 (n / 8) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.addi .r6 .r4 0]) u fun v =>
      Inv s₀ (8 * (n / 8)) v ∧ v.gpr .r6 = BitVec.ofNat 64 (n % 8) := by
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
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, ho⟩
    intro r hr
    have hc : ((instrs zeroize).all fun i => preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs]
      [sat] using sat

end VG.Proof.Zeroize.PPC64LE
