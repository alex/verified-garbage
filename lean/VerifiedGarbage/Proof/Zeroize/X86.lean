import VerifiedGarbage.Impl.Zeroize.X86
import VerifiedGarbage.Proof.Zeroize.Common32
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Zeroize.Contract

namespace VG.Proof.Zeroize.X86
open VG VG.X86 VG.Impl.Zeroize.X86 VG.Proof.MlDsa.X86.Pack

def contract : Contract isa where
  pre s := s.rd = [⟨argAddr s 0, 8⟩] ∧ s.wr = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩] ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ∧
    Region.Disjoint ⟨argAddr s 0, 8⟩ ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  post s t := Spec.Zeroize.bytesAt t.mem ((arg s 0).setWidth 64) (arg s 1).toNat =
    Spec.Zeroize.zeros (arg s 1).toNat
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.rd = s₀.rd ∧ s.gpr .esp = s₀.gpr .esp ∧ s.wr = s₀.wr ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = arg s₀ 0 + BitVec.ofNat 32 i ∧
  Prefix s.mem ((arg s₀ 0).setWidth 64) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 4 else 1) ≤ (arg s₀ 1).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 4 else 1)) t ∧
      t.gpr .edx = s.gpr .edx - 1 ∧ t.gpr .esp = s.gpr .esp ∧
      t.zf = some (s.gpr .edx - 1 == 0) := by
  obtain ⟨hrd, hsp, hw, ha, hd, hz, hf⟩ := h
  have hn := (arg s₀ 1).isLt
  have hc : (⟨(arg s₀ 0).setWidth 64, (arg s₀ 1).toNat⟩ : Region).Contains
      ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 i) (if word then 4 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr ((arg s₀ 0).setWidth 64 + BitVec.ofNat 64 i) (if word then 4 else 1) :=
    ⟨_, by rw [hw, hp.2.1]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨(arg s₀ 0).setWidth 64, (arg s₀ 1).toNat⟩ : Region)
  rw [← hp.2.1] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : arg s₀ 0 + BitVec.ofNat 32 i + BitVec.ofNat 32 k =
      arg s₀ 0 + BitVec.ofNat 32 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  have haddr : ((arg s₀ 0 + BitVec.ofNat 32 i).setWidth 64) =
      (arg s₀ 0).setWidth 64 + BitVec.ofNat 64 i := by
    simpa only [addr, BitVec.add_zero, Nat.add_zero] using
      (VG.Proof.MlKem.X86.addr_add (x := arg s₀ 0) (k := i) (d := 0)
        (by have := hp.2.2.1; cases word <;> simp_all only [↓reduceIte, Bool.false_eq_true] <;> omega))
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    xrun [hd, ha, hs, Inv, hrd, hsp, hw, haddr, State.ea,
      (show BitVec.ofNat 32 0 = 0 from rfl),
      (show (0 : BitVec 32).setWidth 8 = 0 from rfl),
      (show ∀ a : BitVec 32, a + BitVec.ofNat 32 0 = a from BitVec.add_zero),
      (show ∀ a : BitVec 32, a + 0 = a from BitVec.add_zero)]
  · exact ⟨hadd _, prefix_writeW hz (by omega), hf.writeW hmem _ hc⟩
  · exact ⟨hadd _, prefix_writeW hz (by omega), hf.writeW hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 4 else 1) * n ≤ (arg s₀ 1).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .edx = BitVec.ofNat 32 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 4 else 1) * n) t ∧ t.gpr .esp = s.gpr .esp := by
  have hlt : n < 2 ^ 32 := by
    have := (arg s₀ 1).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  have start : WP isa (.block [.alu .cmp .edx (.imm 0)]) s fun t =>
      Inv s₀ i t ∧ t.gpr .edx = BitVec.ofNat 32 n ∧ t.gpr .esp = s.gpr .esp ∧
      t.zf = some (BitVec.ofNat 32 n == 0) := by
    xrun [Inv, hc, (show ∀ a : BitVec 32, a - 0 = a from BitVec.sub_zero)]
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
      Inv s₀ (i + (if word then 4 else 1) * j) t ∧ t.gpr .edx = BitVec.ofNat 32 (n-j) ∧
      t.gpr .esp = s.gpr .esp) ?_ n t ?_
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

theorem arg_addr (s : State) (hn : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32)
    (k : Nat) (hk : k < 2) :
    argAddr s k = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4*k) :=
  VG.Proof.MlKem.X86.ea_off (by omega)

theorem arg_contains (s : State) (hp : contract.pre s) (k : Nat) (hk : k < 2) :
    (⟨argAddr s 0, 8⟩ : Region).Contains (argAddr s k) 4 := by
  rw [arg_addr s hp.2.2.2.1 0 (by decide), arg_addr s hp.2.2.2.1 k hk]
  exact Offset.contains _ (by omega) (by omega) (by decide)

theorem args_out (s : State) (hp : contract.pre s) : ArgsOut 2 s := by
  refine ⟨hp.2.2.2.1, ?_⟩
  intro r hr
  rw [hp.2.1] at hr
  obtain rfl := List.mem_singleton.mp hr
  intro a ha hb
  let j := (a - (s.gpr .esp).setWidth 64).toNat
  have hj : j < 12 := by change j + 1 ≤ 12 at ha; omega
  have he : (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j = a := by
    change (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (a - (s.gpr .esp).setWidth 64).toNat = a
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  by_cases h : j < 4
  · exact hp.2.2.2.2.1 a (by rw [← he]; exact Offset.contains_base _ (by omega) (by omega)) hb
  · apply hp.2.2.2.2.2 a ?_ hb
    rw [arg_addr s hp.2.2.2.1 0 (by decide), ← he]
    exact Offset.contains _ (by omega) (by omega) (by decide)

theorem read_arg (s₀ s : State) (hp : contract.pre s₀) (i : Nat) (h : Inv s₀ i s)
    (k : Nat) (hk : k < 2) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ k) 4 ∧ s.mem.readW (argAddr s₀ k) 32 = arg s₀ k := by
  have hc := arg_contains s₀ hp k hk
  refine ⟨⟨_, by rw [h.1, hp.1]; simp, hc⟩, ?_⟩
  apply h.2.2.2.2.2.2.readW hc ?_ (by decide)
  intro r hr
  rw [hp.2.1] at hr
  obtain rfl := List.mem_singleton.mp hr
  exact hp.2.2.2.2.2

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (arg s₀ 1).toNat
  have reads (k : Nat) (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ k) 4 :=
    ⟨_, by rw [hp.1]; simp, arg_contains s₀ hp k hk⟩
  have start : WP isa (.block [.mov .eax (.imm 0), .mov .ecx (.mem {base := .esp, disp := 4}),
      .mov .edx (.mem {base := .esp, disp := 8}), .shift .shr .edx 2]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .edx = BitVec.ofNat 32 (n / 4) := by
    xrun [Inv, Prefix, State.ea,
      (show ∀ p : BitVec 32, p + BitVec.ofNat 32 0 = p from BitVec.add_zero),
      (show (s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64 = argAddr s₀ 0 from rfl),
      (show (s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64 = argAddr s₀ 1 from rfl), reads 0 (by decide), reads 1 (by decide),
      (show s₀.mem.readW (argAddr s₀ 0) 32 = arg s₀ 0 from rfl),
      (show s₀.mem.readW (argAddr s₀ 1) 32 = arg s₀ 1 from rfl), count32]
    exact ⟨⟨by omega, Frame.refl _ _⟩, rfl⟩
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ t hp 0 (n / 4) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, _⟩ => ?_)
  obtain ⟨hread, hval⟩ := read_arg s₀ u hp _ hu 1 (by decide)
  have mid : WP isa (.block [.mov .edx (.mem {base := .esp, disp := 8}), .alu .and .edx (.imm 3)]) u
      fun v => Inv s₀ (4*(n/4)) v ∧ v.gpr .edx = BitVec.ofNat 32 (n%4) := by
    xrun [Inv, State.ea, hu.2.1,
      (show (s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64 = argAddr s₀ 1 from rfl), hread, hval, tail32]
    refine ⟨?_, rfl⟩
    have hu' : Inv s₀ (4*(n/4)) u := by simpa only [Nat.zero_add, ↓reduceIte] using hu
    exact ⟨hu'.1, hu'.2.2⟩
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv⟩ => ?_)
  refine WP.mono (loop_ok false s₀ v hp (4*(n/4)) (n%4) (by dsimp [n]; omega) hv hcv)
    fun w ⟨hw, _⟩ => ?_
  have hn : 4*(n/4) + (if false then 4 else 1)*(n%4) = n := by simp; omega
  rw [hn] at hw
  exact ⟨prefix_spec hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

def sat : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ⟨ho, hf⟩, hk⟩ := WP.keep [.eax,.ecx,.edx] (correct s hp) (by rfl)
    refine ⟨tr, t, he, ⟨?_, ?_⟩, ho⟩
    · intro r hr
      exact hk.gpr (by cases r <;> simp_all [calleeSaved])
    · apply hf.readW (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      rw [hp.2.1] at hr
      obtain rfl := List.mem_singleton.mp hr
      exact hp.2.2.2.2.1
  · refine VG.Taint.constantTime (A := taint) (argTaint [] 12) ?_ (by taint_decide)
    intro s t hs ht hp
    refine agree_argTaint (k := 2) (fun _ h => nomatch h) hp.1 (args_out s hs) (args_out t ht) ?_
    intro i hi
    rcases (show i=0 ∨ i=1 by omega) with rfl | rfl
    · exact hp.2.1
    · exact hp.2.2
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argSlots,
      argVal, argBytes] [sat, arg, argAddr, Mem.readW, Mem.read] using sat
end VG.Proof.Zeroize.X86
