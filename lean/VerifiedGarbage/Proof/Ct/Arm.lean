import VerifiedGarbage.Impl.Ct.Arm
import VerifiedGarbage.Proof.Ct.Common32
import VerifiedGarbage.Proof.Zeroize.Arm
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Spec.Ct.Contract

namespace VG.Proof.Ct.Arm
open VG VG.Arm VG.Impl.Ct.Arm RegUpd

def Pre (s : State) : Prop :=
  s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] ∧
  (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
  (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32

def Post (s t : State) : Prop := t.gpr .r0 = if Spec.Ct.eq
  (Spec.Ct.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  (Spec.Ct.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) then 1 else 0

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.rd = s₀.rd ∧ s.mem = s₀.mem ∧
  s.gpr .r0 = s₀.gpr .r0 + BitVec.ofNat 32 i ∧
  s.gpr .r2 = s₀.gpr .r2 + BitVec.ofNat 32 i ∧
  s.gpr .r1 = BitVec.ofNat 32 ((s₀.gpr .r1).toNat - i) ∧
  s.gpr .r3 = (diff s₀.mem (State.addr (s₀.gpr .r0)) (State.addr (s₀.gpr .r2)) i).setWidth 32

theorem step_ok (s₀ s : State) (hp : Pre s₀) (hlen : s₀.gpr .r3 = s₀.gpr .r1)
    (i : Nat) (hi : i < (s₀.gpr .r1).toNat) (h : Inv s₀ i s) :
    WP isa (.block step) s fun t => Inv s₀ (i+1) t ∧ t.z = decide (i+1 = (s₀.gpr .r1).toNat) := by
  obtain ⟨hrd, hm, h0, h2, h1, h3⟩ := h
  have hn := (s₀.gpr .r1).isLt
  have ha : State.addr (s₀.gpr .r0 + BitVec.ofNat 32 i) =
      State.addr (s₀.gpr .r0) + BitVec.ofNat 64 i := addr_add (by have := hp.2.1; omega)
  have hb : State.addr (s₀.gpr .r2 + BitVec.ofNat 32 i) =
      State.addr (s₀.gpr .r2) + BitVec.ofNat 64 i := addr_add (by have := hp.2.2; rw [hlen] at this; omega)
  have reads (r : Reg) (hr : r = .r0 ∨ r = .r2) :
      InRegions (s.rd ++ s.wr) (State.addr (s₀.gpr r) + BitVec.ofNat 64 i) 1 := by
    refine ⟨⟨State.addr (s₀.gpr r), (s₀.gpr .r1).toNat⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩
    rw [hrd, hp.1, hlen]
    rcases hr with rfl | rfl <;> simp
  have hadd (p : BitVec 32) : p + BitVec.ofNat 32 i + 1 = p + BitVec.ofNat 32 (i+1) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  have hpred : BitVec.ofNat 32 ((s₀.gpr .r1).toNat-i) - 1 =
      BitVec.ofNat 32 ((s₀.gpr .r1).toNat-(i+1)) := by bv_omega
  have hz : (BitVec.ofNat 32 ((s₀.gpr .r1).toNat-i) - 1 == 0) =
      decide (i+1 = (s₀.gpr .r1).toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega
  have hreadA := reads .r0 (.inl rfl)
  have hreadB := reads .r2 (.inr rfl)
  rw [hrd] at hreadA hreadB
  unfold step
  zrun [Inv, hrd, hm, h0, h2, h1, h3, ha, hb, hreadA, hreadB,
    (show ∀ p : BitVec 32, p + BitVec.ofNat 32 0 = p from BitVec.add_zero), hadd, hz,
    ← BitVec.setWidth_xor, ← BitVec.setWidth_or]
  exact ⟨hpred, rfl⟩

theorem loop_ok (s₀ s : State) (hp : Pre s₀) (hlen : s₀.gpr .r3 = s₀.gpr .r1)
    (i : Nat) (hi : i < (s₀.gpr .r1).toNat) (h : Inv s₀ i s) :
    WP isa (.loop (.block step) .ne) s (Inv s₀ (s₀.gpr .r1).toNat) := by
  let n := (s₀.gpr .r1).toNat
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n-j ∧ Inv s₀ j t)
    ?_ (n-i) s ⟨i, hi, rfl, h⟩
  intro rem t ⟨j, hj, hr, ht⟩
  refine WP.mono (step_ok s₀ t hp hlen j hj ht) fun u ⟨hu, hz⟩ => ?_
  change u.z = decide (j+1=n) at hz
  by_cases he : j+1 = n
  · exact .inl ⟨by simp [eval, hz, he], by simpa only [he] using hu⟩
  · exact .inr ⟨by simp [eval, hz, he], n-(j+1), by omega, j+1, by omega, rfl, hu⟩

theorem finish_ok (s : State) (d : Byte) (ha : s.gpr .r3 = d.setWidth 32) :
    WP isa finish s fun t => t.mem = s.mem ∧ t.gpr .r0 = if d=0 then 1 else 0 := by
  unfold finish
  zrun [ha]
  exact result32 d

theorem equal_ok (s₀ s : State) (hp : Pre s₀) (hlen : s₀.gpr .r3 = s₀.gpr .r1)
    (hregs : s.gpr = s₀.gpr) (hrd : s.rd = s₀.rd) (hm : s.mem = s₀.mem) :
    WP isa equal s fun t => t.mem = s₀.mem ∧ Post s₀ t := by
  have start : WP isa (.block [.mov .r3 (.imm 0), .cmp .r1 (.imm 0)]) s fun t =>
      Inv s₀ 0 t ∧ t.z = (s₀.gpr .r1 == 0) := by
    zrun [Inv, hregs, hrd, hm, diff, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      (show ∀ p : BitVec 32, p + BitVec.ofNat 32 0 = p from BitVec.add_zero),
      (show ∀ p : BitVec 32, p - 0 = p from BitVec.sub_zero)]
  unfold equal
  refine WP.seq (WP.mono start fun t ⟨ht, hz⟩ => WP.seq ?_)
  have middle : WP isa (.ite .eq (.block []) (.loop (.block step) .ne)) t
      (Inv s₀ (s₀.gpr .r1).toNat) := by
    by_cases he : s₀.gpr .r1 = 0
    · refine WP.ite true (by simp [eval, hz, he]) (fun _ => WP.block_nil ?_) (by simp)
      simpa only [he, show (0 : BitVec 32).toNat = 0 from rfl] using ht
    · exact WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr he]) (by simp)
        (fun _ => loop_ok s₀ t hp hlen 0 (by bv_omega) ht)
  refine WP.mono middle fun u hu => WP.mono (finish_ok u _ hu.2.2.2.2.2) fun v ⟨hmv, hv⟩ => ?_
  refine ⟨hmv.trans hu.2.1, ?_⟩
  unfold Post
  rw [hlen, diff_spec]
  simpa only [decide_eq_true_eq] using hv

theorem body_ok (s₀ : State) (hp : Pre s₀) :
    WP isa body s₀ fun t => t.mem = s₀.mem ∧ Post s₀ t := by
  have start : WP isa (.block [.cmp .r1 (.reg .r3)]) s₀ fun t =>
      t.gpr = s₀.gpr ∧ t.rd = s₀.rd ∧ t.mem = s₀.mem ∧ t.z = (s₀.gpr .r1 - s₀.gpr .r3 == 0) := by
    zrun []
  unfold body
  refine WP.seq (WP.mono start fun t ⟨hg, hr, hm, hz⟩ => ?_)
  have hsub (a b : BitVec 32) : (a-b==0) = (a==b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  rw [hsub] at hz
  by_cases he : s₀.gpr .r1 = s₀.gpr .r3
  · exact WP.ite true (by simp [eval, hz, he]) (fun _ => equal_ok s₀ t hp he.symm hg hr hm) (by simp)
  · refine WP.ite false (by simp [eval, hz, he]) (by simp) (fun _ => ?_)
    have hn : (s₀.gpr .r1).toNat ≠ (s₀.gpr .r3).toNat := fun h => he (BitVec.eq_of_toNat_eq h)
    zrun [hm, Post, lengths_ne _ _ _ hn]

def frameR (s : State) : Region := ⟨State.addr s.sp - 4#64, 4⟩

def contract : Contract isa where
  pre s := Pre s ∧ s.wr = [] ∧ 4 ≤ s.sp.toNat ∧
    Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (frameR s) ∧
    Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (frameR s)
  post := Post
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ s.sp = t.sp

theorem frame_addr (s : State) (h : 4 ≤ s.sp.toNat) :
    State.addr (s.sp - 4) = State.addr s.sp - 4 := by
  apply BitVec.eq_of_toNat_eq
  simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have := s.sp.isLt
  have h4 : (4 : BitVec 32).toNat = 4 := rfl
  have h4' : (4 : BitVec 64).toNat = 4 := rfl
  rw [h4, h4']
  omega

theorem push_frame (s : State) (h : 4 ≤ s.sp.toNat) :
    Frame [frameR s] s.mem (pushed [.r4] s).mem := by
  change Frame [frameR s] s.mem (s.mem.writeW (State.addr (s.sp - 4)) (s.gpr .r4))
  rw [frame_addr s h]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem push_bytes (s : State) (hp : contract.pre s) (p : Addr) (n : Nat)
    (hd : Region.Disjoint ⟨p,n⟩ (frameR s)) (hn : n ≤ 2^64) :
    Spec.Ct.bytesAt (pushed [.r4] s).mem p n = Spec.Ct.bytesAt s.mem p n := by
  unfold Spec.Ct.bytesAt
  apply List.map_congr_left
  intro i hi
  exact (push_frame s hp.2.2.1).bytes (R := ⟨p,n⟩) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hd)
    hn (List.mem_range.mp hi)

theorem correct (s : State) (hp : contract.pre s) :
    WP isa eq s fun t => abiPreserved s t ∧ Post s t := by
  unfold eq
  apply WP.frame (rs := [.r4]) (by decide) hp.2.2.1 (by decide)
  obtain ⟨tr, t, he, hm, ho⟩ := body_ok (pushed [.r4] s) hp.1
  refine ⟨tr, t, he, ⟨?_, ?_⟩, ?_⟩
  · intro r hr
    by_cases h4 : r = .r4
    · subst r
      change t.mem.readW (State.addr t.sp) 32 = s.gpr .r4
      rw [hm, Exec.sp he]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [popped_gpr h4]
      have hc : ∀ r ∈ preserved, r ≠ .r4 →
          body.allInstrs (fun i => dstOf i != some r) = true := by decide +kernel
      have hkeep := hc r hr h4
      rw [Code.allInstrs_eq] at hkeep
      apply Exec.gpr (fun i hi => ?_) he
      simpa only [bne, Bool.not_eq_true', beq_eq_false_iff_ne] using List.all_eq_true.mp hkeep i hi
  · rw [popped_sp, Exec.sp he, pushed_sp]
    exact BitVec.sub_add_cancel _ _
  · unfold Post at ho ⊢
    rw [popped_gpr (by decide)]
    change t.gpr .r0 = if Spec.Ct.eq
      (Spec.Ct.bytesAt (pushed [.r4] s).mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Ct.bytesAt (pushed [.r4] s).mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) then 1 else 0 at ho
    rw [push_bytes s hp _ _ hp.2.2.2.1 (by have := (s.gpr .r1).isLt; omega),
      push_bytes s hp _ _ hp.2.2.2.2 (by have := (s.gpr .r3).isLt; omega)] at ho
    exact ho

theorem body_ct : ConstantTime isa (fun _ => True)
    (fun s t => ∀ r ∈ [.r0,.r1,.r2,.r3], s.gpr r = t.gpr r) body :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0,.r1,.r2,.r3])
    (fun _ _ _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem constantTime : ConstantTime isa contract.pre contract.pub eq := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ hp₁ hp₂ hpub he₁ he₂
  have hrel := RelCT.frame (rs := [.r4]) (r := .r4) (n := 4) (body := body)
    (P := fun s t => contract.pre s ∧ contract.pre t ∧ contract.pub s t)
    (fun _ _ h => h.2.2.2.2.2.2) (by
      intro a b ta tb a' b' h ea eb
      obtain ⟨s, t, ⟨hs, ht, hp⟩, hpushs, hpusht⟩ := h
      rw [push_pushed (rs := [.r4]) (by decide) hs.2.2.1] at hpushs
      rw [push_pushed (rs := [.r4]) (by decide) ht.2.2.1] at hpusht
      obtain rfl := Option.some.inj hpushs
      obtain rfl := Option.some.inj hpusht
      refine ⟨body_ct _ _ _ _ _ _ trivial trivial ?_ ea eb, trivial⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.1
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.1)
  exact (hrel _ _ _ _ _ _ ⟨hp₁, hp₂, hpub⟩ he₁ he₂).1

def sat : State where
  gpr _ := 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0,0⟩, ⟨0,0⟩]
  wr := []

theorem verified : Verified target eq (Spec.Ct.eqContract abi 4) := by
  apply Verified.of_correct (k := contract)
  · exact correct
  · exact constantTime
  · refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
    · intro s h
      sig_pre [Spec.Ct.eqContract, Spec.Ct.eqSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
      sig_split h
      sig_reduce [contract, Pre, frameR, State.addr]
      sig_simp [] []
      sig_and_intros
      sig_close
      all_goals exact Region.Disjoint.symm ‹_›
    · intro s t _ h
      sig_post [Spec.Ct.eqContract, Spec.Ct.eqSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
      rw [BitVec.setWidth_append_eq_right]
      exact h
    · sig_implies_pub [Spec.Ct.eqContract, Spec.Ct.eqSig, contract, abi, argRegs, reduceClassify, Loc.val]
    · sig_implies_sat [Spec.Ct.eqContract, Spec.Ct.eqSig, abi, argRegs, reduceClassify, Loc.val] [sat] using sat
end VG.Proof.Ct.Arm
