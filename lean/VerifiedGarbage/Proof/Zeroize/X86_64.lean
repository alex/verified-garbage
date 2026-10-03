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

/-- `body` `n` times, each zeroing `w` more bytes. -/
theorem loopOf_ok (body : List Instr) (w : Nat) (hw : 0 < w) (s₀ s : State) (i n : Nat)
    (hn : i + w * n ≤ (s₀.gpr .rsi).toNat)
    (hstep : ∀ j u, j < n → Inv s₀ (i + w * j) u → WP isa (.block body) u fun v =>
      Inv s₀ (i + w * (j + 1)) v ∧ v.gpr .rdx = u.gpr .rdx - 1 ∧ v.gpr .rsi = u.gpr .rsi ∧
      v.zf = some (u.gpr .rdx - 1 == 0))
    (h : Inv s₀ i s) (hc : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (loopOf body) s fun t => Inv s₀ (i + w * n) t ∧ t.gpr .rsi = s.gpr .rsi := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .rsi).isLt
    have : n ≤ w * n := Nat.le_mul_of_pos_left n hw
    omega
  have start : WP isa (.block [.alu .cmp .rdx (.imm 0)]) s fun t =>
      Inv s₀ i t ∧ t.gpr .rdx = BitVec.ofNat 64 n ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.zf = some (BitVec.ofNat 64 n == 0) := by
    xrun [Inv, hc, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl),
      (show ∀ a : Addr, a - 0 = a from BitVec.sub_zero)]
    exact h
  unfold loopOf
  refine WP.seq (WP.mono start fun t ⟨ht, hct, hsi, hz⟩ => ?_)
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, hz]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hsi
  · refine WP.ite false (by simp only [eval, hz, ofNat64_beq_zero hlt, decide_eq_false he]) (by simp) (fun _ => ?_)
    apply wp_countdown hlt (by omega)
      (fun j u => Inv s₀ (i + w * j) u ∧ u.gpr .rsi = s.gpr .rsi)
      (cnt := .rdx)
    · intro j hj u ⟨hu, hsu⟩ _
      refine WP.mono (hstep j u hj hu) fun v ⟨hv, hcv, hsv, hzv⟩ => ?_
      exact ⟨⟨hv, hsv.trans hsu⟩, hcv, hzv⟩
    · exact fun _ h => h
    · simpa only [Nat.mul_zero, Nat.add_zero] using And.intro ht hsi
    · exact hct

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 8 else 1) * n ≤ (s₀.gpr .rsi).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 8 else 1) * n) t ∧ t.gpr .rsi = s.gpr .rsi :=
  loopOf_ok (step word) _ (by cases word <;> decide) s₀ s i n hn
    (fun j u hj hu => by
      have hs := step_ok word s₀ u hp _ (by
        have : (if word then 8 else 1) * (j + 1) ≤ (if word then 8 else 1) * n :=
          Nat.mul_le_mul_left _ hj
        rw [Nat.mul_succ] at this; omega) hu
      rwa [Nat.mul_succ, ← Nat.add_assoc])
    h hc

theorem wideStep_ok (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + 32 ≤ (s₀.gpr .rsi).toNat) (h : Inv s₀ i s) :
    WP isa (.block wideStep) s fun t =>
      Inv s₀ (i + 32) t ∧ t.gpr .rdx = s.gpr .rdx - 1 ∧ t.gpr .rsi = s.gpr .rsi ∧
      t.zf = some (s.gpr .rdx - 1 == 0) := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .rsi).isLt
  have hc : ∀ k, k ≤ 24 → (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region).Contains
      (s₀.gpr .rdi + BitVec.ofNat 64 (i + k)) 8 :=
    fun k hk => Offset.contains_base _ (by omega) (by omega)
  have hmem := List.mem_singleton_self (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region)
  rw [← hp.2.1] at hmem
  have hs : ∀ k, k ≤ 24 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 (i + k)) 8 :=
    fun k hk => ⟨_, hmem, hc k hk⟩
  have hadd (k : Nat) : s₀.gpr .rdi + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .rdi + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  have s0 := hs 0 (by decide); have s8 := hs 8 (by decide); have s16 := hs 16 (by decide)
  have s24 := hs 24 (by decide)
  rw [Nat.add_zero] at s0
  unfold wideStep
  xrun [hd, ha, s0, s8, s16, s24, Inv, hw, State.ea, hadd,
    (show BitVec.ofInt 64 0 = 0 from rfl), (show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl),
    (show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl),
    (show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl),
    (show BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 from rfl),
    (show ∀ a : Addr, a + 0 = a from BitVec.add_zero)]
  have c : ∀ k, k ≤ 24 → (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region).Contains
      (s₀.gpr .rdi + BitVec.ofNat 64 (i + k)) (64 / 8) := hc
  have c0 : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region).Contains (s₀.gpr .rdi + BitVec.ofNat 64 i) (64 / 8) := by
    have := c 0 (by decide); rwa [Nat.add_zero] at this
  exact ⟨prefix_writeW4 (w := 64) hz (by omega),
    (((hf.writeW (w := 64) hmem _ c0).writeW hmem _ (c 8 (by decide))).writeW hmem _ (c 16 (by decide))).writeW
      hmem _ (c 24 (by decide))⟩

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .rsi).toNat
  have hn := (s₀.gpr .rsi).isLt
  have start : WP isa (.block [.mov .rax (.imm 0), .mov .rdx (.reg .rsi), .shift .shr .rdx 5]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .rdx = BitVec.ofNat 64 (n / 32) ∧ t.gpr .rsi = s₀.gpr .rsi := by
    xrun [Inv, Prefix, shr64, (show BitVec.signExtend 64 (0 : BitVec 32) = 0 from rfl),
      (show ∀ p : Addr, p + BitVec.ofNat 64 0 = p from BitVec.add_zero)]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl⟩
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loopOf_ok wideStep 32 (by decide) s₀ t 0 (n / 32) (by dsimp [n]; omega)
    (fun j u hj hu => by
      have := wideStep_ok s₀ u hp _ (by dsimp [n] at hj ⊢; omega) hu
      rwa [Nat.mul_succ, ← Nat.add_assoc]) ht hc) fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.mov .rdx (.reg .rsi), .shift .shr .rdx 3, .alu .and .rdx (.imm 3)]) u fun v =>
      Inv s₀ (32 * (n / 32)) v ∧ v.gpr .rdx = BitVec.ofNat 64 (n / 8 % 4) ∧ v.gpr .rsi = s₀.gpr .rsi := by
    xrun [Inv, hsu, hs, shr64, (show BitVec.signExtend 64 (3 : BitVec 32) = 3 from rfl),
      and3_64]
    exact ⟨by simpa only [Nat.zero_add, Inv] using hu, rfl⟩
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv, hsv⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ v hp (32 * (n / 32)) (n / 8 % 4) (by dsimp [n]; omega) hv hcv)
    fun w ⟨hw, hsw⟩ => ?_)
  have tl : WP isa (.block [.mov .rdx (.reg .rsi), .alu .and .rdx (.imm 7)]) w fun x =>
      Inv s₀ (32 * (n / 32) + 8 * (n / 8 % 4)) x ∧ x.gpr .rdx = BitVec.ofNat 64 (n % 8) := by
    xrun [Inv, hsw, hsv, tail, (show BitVec.signExtend 64 (7 : BitVec 32) = 7 from rfl)]
    exact ⟨by simpa only [↓reduceIte, Inv] using hw, rfl⟩
  refine WP.seq (WP.mono tl fun x ⟨hx, hcx⟩ => ?_)
  refine WP.mono (loop_ok false s₀ x hp _ (n % 8) (by dsimp [n]; simp; omega) hx hcx) fun y ⟨hy, _⟩ => ?_
  have he : 32 * (n / 32) + 8 * (n / 8 % 4) + (if false then 8 else 1) * (n % 8) = n := by simp; omega
  rw [he] at hy
  exact ⟨prefix_spec hy.2.2.2.1, hy.2.2.2.2⟩

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
