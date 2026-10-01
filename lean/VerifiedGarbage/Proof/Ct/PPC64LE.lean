import VerifiedGarbage.Impl.Ct.PPC64LE
import VerifiedGarbage.Proof.Ct.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Constant-time byte comparison on PPC64LE

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Ct.AArch64`).
-/

namespace VG.Proof.Ct.PPC64LE
open VG VG.PPC64LE VG.Impl.Ct.PPC64LE

/-- The registers the code writes. -/
def scratch : List Reg := [.r3, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The comparison changes only `scratch` (all but `r3` before `finish`) and
not its permissions. -/
def Keep (s t : State) : Prop :=
  (∀ r, r ∉ scratch → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem keep {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q)
    (hc : c.allInstrs (fun i => match dstOf i with
      | none => true | some r => scratch.contains r) = true)
    (hn : c.noCalls = true := by decide +kernel) :
    WP isa c s fun t => Q t ∧ Keep s t := by
  obtain ⟨tr, t, he, hq⟩ := h
  refine ⟨tr, t, he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn),
    (Exec.rdwr he).1, (Exec.rdwr he).2.1⟩
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

theorem Keep.trans {a b c : State} (h : Keep a b) (k : Keep b c) : Keep a c :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

def contract : Contract isa where
  pre s := s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩, ⟨s.gpr .r5, (s.gpr .r6).toNat⟩] ∧ s.wr = []
  post s t := (t.gpr .r3).setWidth 32 = if Spec.Ct.eq
    (Spec.Ct.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (Spec.Ct.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) then 1 else 0
  pub s t := s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧
    s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  Keep s₀ s ∧ s.gpr .r3 = s₀.gpr .r3 ∧ s.mem = s₀.mem ∧ s.gpr .r8 = BitVec.ofNat 64 i ∧
  s.gpr .r7 = (diff s₀.mem (s₀.gpr .r3) (s₀.gpr .r5) i).setWidth 64

theorem step_ok (s₀ s : State) (hp : contract.pre s₀)
    (hlen : s₀.gpr .r6 = s₀.gpr .r4) (i : Nat) (hi : i < (s₀.gpr .r4).toNat)
    (h : Inv s₀ i s) :
    WP isa (.block step) s fun t => Inv s₀ (i + 1) t ∧
      t.gpr .r9 = BitVec.ofNat 64 (i + 1) - s₀.gpr .r4 := by
  obtain ⟨hk, h3, hm, hx, ha⟩ := h
  have h4 := hk.1 .r4 (by decide)
  have h5 := hk.1 .r5 (by decide)
  have hn := (s₀.gpr .r4).isLt
  have hA : InRegions (s.rd ++ s.wr) (s₀.gpr .r3 + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2, hp.1, hp.2, List.append_nil]
    exact ⟨⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hB : InRegions (s.rd ++ s.wr) (s₀.gpr .r5 + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2, hp.1, hp.2, hlen, List.append_nil]
    exact ⟨⟨s₀.gpr .r5, (s₀.gpr .r4).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hadd : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by rw [BitVec.ofNat_add]
  unfold step
  refine WP.mono (keep (Q := fun t => t.gpr .r3 = s₀.gpr .r3 ∧ t.mem = s₀.mem ∧
    t.gpr .r8 = BitVec.ofNat 64 (i + 1) ∧
    t.gpr .r7 = (diff s₀.mem (s₀.gpr .r3) (s₀.gpr .r5) (i + 1)).setWidth 64 ∧
    t.gpr .r9 = BitVec.ofNat 64 (i + 1) - s₀.gpr .r4) ?_ (by rfl)) ?_
  · crun [h3, h4, h5, hx, ha, hm, hA, hB, hadd, ← BitVec.setWidth_or, ← BitVec.setWidth_xor]
    rfl
  · intro t ⟨⟨h3', hm', hx', ha', hz⟩, hk'⟩
    exact ⟨⟨hk.trans hk', h3', hm', hx', ha'⟩, hz⟩

theorem sub_zero (a b : BitVec 64) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem loop_ok (s₀ : State) (hp : contract.pre s₀) (hlen : s₀.gpr .r6 = s₀.gpr .r4)
    (s : State) (i : Nat) (hi : i < (s₀.gpr .r4).toNat) (h : Inv s₀ i s) :
    WP isa (.loop (.block step) (.nonzero .d .r9)) s (Inv s₀ (s₀.gpr .r4).toNat) := by
  let n := (s₀.gpr .r4).toNat
  apply WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧ Inv s₀ j t) ?_ (n - i) s
    ⟨i, hi, rfl, h⟩
  intro rem t ⟨j, hj, hr, hinv⟩
  refine WP.mono (step_ok s₀ t hp hlen j hj hinv) fun t' ⟨hout, hz⟩ => ?_
  by_cases he : j + 1 = n
  · left
    refine ⟨?_, (by simpa only [he] using hout)⟩
    simp [VG.PPC64LE.eval, State.read, hz, he, n]
  · right
    have hne : BitVec.ofNat 64 (j + 1) ≠ s₀.gpr .r4 := by
      intro hh
      have := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s₀.gpr .r4).isLt; dsimp [n] at *; omega)] at this
      exact he this
    refine ⟨?_, n - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
    simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, hz, bne, sub_zero,
      beq_eq_false_iff_ne.mpr hne]
    rfl

theorem finish_ok (s : State) (d : Byte) (ha : s.gpr .r7 = d.setWidth 64) :
    WP isa finish s fun t => t.mem = s.mem ∧
      (t.gpr .r3).setWidth 32 = if d = 0 then 1 else 0 := by
  unfold finish
  crun [ha]
  exact result64 d

theorem equal_ok (s₀ s : State) (hp : contract.pre s₀)
    (hlen : s₀.gpr .r6 = s₀.gpr .r4)
    (hk : Keep s₀ s) (h3 : s.gpr .r3 = s₀.gpr .r3) (hm : s.mem = s₀.mem) (ha : s.gpr .r7 = 0) :
    WP isa equal s fun t => t.mem = s₀.mem ∧ contract.post s₀ t := by
  have start : WP isa (.block [.li .r8 0]) s (Inv s₀ 0) := by
    refine WP.mono (keep (Q := fun t => t.gpr .r3 = s₀.gpr .r3 ∧ t.mem = s₀.mem ∧
      t.gpr .r8 = 0 ∧ t.gpr .r7 = 0) ?_ (by rfl)) ?_
    · crun [h3, hm, ha]
    · intro t ⟨⟨h3', hm', hx', ha'⟩, hk'⟩
      exact ⟨hk.trans hk', h3', hm', hx', ha'⟩
  unfold equal
  refine WP.seq (WP.mono start fun t hinv => WP.seq ?_)
  have h4 := hinv.1.1 .r4 (by decide)
  have after : WP isa (.ite (.zero .d .r4) (.block []) (.loop (.block step) (.nonzero .d .r9))) t
      (Inv s₀ (s₀.gpr .r4).toNat) := by
    by_cases he : s₀.gpr .r4 = 0
    · refine WP.ite true (by simp [VG.PPC64LE.eval, State.read, h4, he]) (fun _ => ?_) (by simp)
      apply WP.block_nil
      simpa only [he, (show (0 : BitVec 64).toNat = 0 from rfl)] using hinv
    · refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h4,
          beq_eq_false_iff_ne.mpr he]) (by simp) (fun _ => ?_)
      exact loop_ok s₀ hp hlen t 0 (by bv_omega) hinv
  refine WP.mono after fun u hu => ?_
  refine WP.mono (finish_ok u _ hu.2.2.2.2) fun v ⟨hmv, hv⟩ => ?_
  refine ⟨hmv.trans hu.2.2.1, ?_⟩
  change (v.gpr .r3).setWidth 32 = _
  rw [hlen, diff_spec]
  simpa only [decide_eq_true_eq] using hv

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa eq s₀ fun t => t.mem = s₀.mem ∧ contract.post s₀ t := by
  have start : WP isa (.block [.li .r7 0, .sub .r9 .r4 .r6]) s₀
      (fun t => Keep s₀ t ∧ t.gpr .r3 = s₀.gpr .r3 ∧ t.mem = s₀.mem ∧ t.gpr .r7 = 0 ∧
        t.gpr .r9 = s₀.gpr .r4 - s₀.gpr .r6) := by
    refine WP.mono (keep (Q := fun t => t.gpr .r3 = s₀.gpr .r3 ∧ t.mem = s₀.mem ∧
        t.gpr .r7 = 0 ∧ t.gpr .r9 = s₀.gpr .r4 - s₀.gpr .r6) ?_ (by rfl)) ?_
    · crun
    · intro t ⟨h, hk⟩; exact ⟨hk, h⟩
  unfold eq
  refine WP.seq (WP.mono start fun t ⟨hk, h3, hm, ha, hz⟩ => ?_)
  by_cases he : s₀.gpr .r4 = s₀.gpr .r6
  · exact WP.ite true (by simp [VG.PPC64LE.eval, State.read, hz, he])
      (fun _ => equal_ok s₀ t hp he.symm hk h3 hm ha) (by simp)
  · refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, hz,
      sub_zero, beq_eq_false_iff_ne.mpr he]) (by simp) (fun _ => ?_)
    have hn : (s₀.gpr .r4).toNat ≠ (s₀.gpr .r6).toNat := fun h => he (BitVec.eq_of_toNat_eq h)
    crun [hm, contract, lengths_ne _ _ _ hn]

def sat : State where
  gpr _ := 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0, 0⟩]
  wr := []

theorem verified : Verified target eq (Spec.Ct.eqContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, hm, ho⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, ho⟩
    intro r hr
    have hc : ((instrs eq).all fun i => preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_
      (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
  · sig_implies [Spec.Ct.eqContract, Spec.Ct.eqSig, contract, abi, argRegs] [sat] using sat

end VG.Proof.Ct.PPC64LE
