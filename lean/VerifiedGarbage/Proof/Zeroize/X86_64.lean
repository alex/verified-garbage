import VerifiedGarbage.Impl.Zeroize.X86_64
import VerifiedGarbage.Proof.Zeroize.Common
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.TCB.X86_64.Target

namespace VG.Proof.Zeroize.X86_64
open VG VG.X86_64 VG.Impl.Zeroize.X86_64 VG.Proof.MlKem.X86_64

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  post s t := Spec.Zeroize.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    Spec.Zeroize.zeros (s.gpr .rsi).toNat
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .rax = 0 ∧ s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 i ∧
  Prefix s.mem (s₀.gpr .rdi) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 8 else 1) ≤ (s₀.gpr .rsi).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 8 else 1)) t ∧
      t.gpr .rdx = s.gpr .rdx - 1 ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.zf = some (s.gpr .rdx - 1 == 0) := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .rsi).isLt
  have hc : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region).Contains
      (s₀.gpr .rdi + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    ⟨_, by rw [hw, hp.2.1]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region)
  rw [← hp.2.1] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .rdi + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .rdi + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    xrun [hd, ha, hs, Inv, hw, VG.Impl.MlKem.X86_64.at_, State.ea,
      (show BitVec.ofInt 64 0 = 0 from rfl),
      (show ∀ a : Addr, a + 0 = a from BitVec.add_zero),
      (show (0 : BitVec 64).setWidth 8 = 0 from rfl)]
  · exact ⟨hadd _, prefix_writeW hz (by omega), hf.writeW hmem _ hc⟩
  · exact ⟨hadd _, prefix_writeW hz (by omega), hf.writeW hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 8 else 1) * n ≤ (s₀.gpr .rsi).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 8 else 1) * n) t ∧ t.gpr .rsi = s.gpr .rsi := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .rsi).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  have start : WP isa (.block [.alu .cmp .rdx (.imm 0)]) s fun t =>
      Inv s₀ i t ∧ t.gpr .rdx = BitVec.ofNat 64 n ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.zf = some (BitVec.ofNat 64 n == 0) := by
    xrun [Inv, hc, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl),
      (show ∀ a : Addr, a - 0 = a from BitVec.sub_zero)]
    exact h
  unfold loop
  refine WP.seq (WP.mono start fun t ⟨ht, hct, hsi, hz⟩ => ?_)
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, hz]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hsi
  · refine WP.ite false (by simp only [eval, hz, ofNat64_beq_zero hlt, decide_eq_false he]) (by simp) (fun _ => ?_)
    apply wp_countdown hlt (by omega)
      (fun j u => Inv s₀ (i + (if word then 8 else 1) * j) u ∧ u.gpr .rsi = s.gpr .rsi)
      (cnt := .rdx)
    · intro j hj u ⟨hu, hsu⟩ _
      refine WP.mono (step_ok word s₀ u hp _ ?_ hu) fun v ⟨hv, hcv, hsv, hzv⟩ => ?_
      · cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn ⊢ <;> omega
      · rw [Nat.mul_succ, ← Nat.add_assoc]
        exact ⟨⟨hv, hsv.trans hsu⟩, hcv, hzv⟩
    · exact fun _ h => h
    · simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hsi
    · exact hct

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .rsi).toNat
  have start : WP isa (.block [.mov .rax (.imm 0), .mov .rdx (.reg .rsi),
      .shift .shr .rdx 3, .alu .and .rsi (.imm 7)]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .rdx = BitVec.ofNat 64 (n / 8) ∧
      t.gpr .rsi = BitVec.ofNat 64 (n % 8) := by
    xrun [Inv, Prefix, count, tail, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl),
      (show BitVec.signExtend 64 (7 : BitVec 32) = 7 from rfl),
      (show ∀ p : Addr, p + BitVec.ofNat 64 0 = p from BitVec.add_zero)]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl, rfl⟩
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ t hp 0 (n / 8) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.mov .rdx (.reg .rsi)]) u fun v =>
      Inv s₀ (8 * (n / 8)) v ∧ v.gpr .rdx = BitVec.ofNat 64 (n % 8) := by
    xrun [Inv, hsu, hs]
    simpa only [Nat.zero_add, ↓reduceIte, Inv] using hu
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv⟩ => ?_)
  refine WP.mono (loop_ok false s₀ v hp (8 * (n / 8)) (n % 8) (by dsimp [n]; omega) hv hcv)
    fun w ⟨hw, _⟩ => ?_
  have hn : 8 * (n / 8) + (if false then 8 else 1) * (n % 8) = n := by simp; omega
  rw [hn] at hw
  exact ⟨prefix_spec hw.2.2.2.1, hw.2.2.2.2⟩

def sat : State where
  gpr r := match r with | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ⟨ho, hf⟩, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rdx] (correct s hp) (by rfl)
    refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ?_, ho⟩
    apply gprPreserved_of hk (by decide +kernel) hf
    intro r hr
    rw [hp.2.1] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.2.2
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
    intro s t _ _ h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs] [sat] using sat

end VG.Proof.Zeroize.X86_64
