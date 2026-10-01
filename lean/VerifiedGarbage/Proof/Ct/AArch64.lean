import VerifiedGarbage.Impl.Ct.AArch64
import VerifiedGarbage.Proof.Ct.Common
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.TCB.AArch64.Target

namespace VG.Proof.Ct.AArch64
open VG VG.AArch64 VG.Impl.Ct.AArch64 RegUpd

def Keep (s t : State) : Prop :=
  (∀ r, r ∉ [.x4, .x5, .x6, .x7, .x8, .x9] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem keep {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q)
    (hc : c.allInstrs (fun i => match dstOf i with
      | none => true | some r => [.x4, .x5, .x6, .x7, .x8, .x9].contains r) = true)
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

syntax "crun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| crun) => `(tactic| crun [])
  | `(tactic| crun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec, State.read, addr, State.load, gpr_write, mem_write, rd_write, wr_write,
        BitVec.setWidth_eq, (show ∀ b : Byte, (b.setWidth 32).setWidth 64 = b.setWidth 64 from fun _ => BitVec.setWidth_setWidth (by decide)),
        BitVec.shiftLeft_zero, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Mem.read, BitVec.zero_width_append, BitVec.cast_eq, Option.bind_some, Option.map_some,
        Option.some.injEq, exists_eq_left', ite_true, ite_false, reduceCtorEq,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, true_and, and_true, $ls,*]))

def contract : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧ s.wr = []
  post s t := (t.gpr .x0).setWidth 32 = if Spec.Ct.eq
    (Spec.Ct.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Ct.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) then 1 else 0
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  Keep s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .x8 = BitVec.ofNat 64 i ∧
  s.gpr .x4 = (diff s₀.mem (s₀.gpr .x0) (s₀.gpr .x2) i).setWidth 64

theorem step_ok (s₀ s : State) (hp : contract.pre s₀)
    (hlen : s₀.gpr .x3 = s₀.gpr .x1) (i : Nat) (hi : i < (s₀.gpr .x1).toNat)
    (h : Inv s₀ i s) :
    WP isa (.block step) s fun t => Inv s₀ (i + 1) t ∧
      t.gpr .x9 = BitVec.ofNat 64 (i + 1) - s₀.gpr .x1 := by
  obtain ⟨hk, hm, hx, ha⟩ := h
  have h0 := hk.1 .x0 (by decide)
  have h1 := hk.1 .x1 (by decide)
  have h2 := hk.1 .x2 (by decide)
  have hn := (s₀.gpr .x1).isLt
  have hA : InRegions (s.rd ++ s.wr) (s₀.gpr .x0 + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2, hp.1, hp.2, List.append_nil]
    exact ⟨⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hB : InRegions (s.rd ++ s.wr) (s₀.gpr .x2 + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2, hp.1, hp.2, hlen, List.append_nil]
    exact ⟨⟨s₀.gpr .x2, (s₀.gpr .x1).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hadd : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by rw [BitVec.ofNat_add]
  unfold step
  refine WP.mono (keep (Q := fun t => t.mem = s₀.mem ∧ t.gpr .x8 = BitVec.ofNat 64 (i + 1) ∧
    t.gpr .x4 = (diff s₀.mem (s₀.gpr .x0) (s₀.gpr .x2) (i + 1)).setWidth 64 ∧
    t.gpr .x9 = BitVec.ofNat 64 (i + 1) - s₀.gpr .x1) ?_ (by rfl)) ?_
  · crun [h0, h1, h2, hx, ha, hm, hA, hB, hadd, ← BitVec.setWidth_or, ← BitVec.setWidth_xor]
    rfl
  · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
    exact ⟨⟨hk.trans hk', hm', hx', ha'⟩, hz⟩


theorem sub_zero (a b : BitVec 64) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem loop_ok (s₀ : State) (hp : contract.pre s₀) (hlen : s₀.gpr .x3 = s₀.gpr .x1)
    (s : State) (i : Nat) (hi : i < (s₀.gpr .x1).toNat) (h : Inv s₀ i s) :
    WP isa (.loop (.block step) (.nonzero .x .x9)) s (Inv s₀ (s₀.gpr .x1).toNat) := by
  let n := (s₀.gpr .x1).toNat
  apply WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧ Inv s₀ j t) ?_ (n - i) s
    ⟨i, hi, rfl, h⟩
  intro rem t ⟨j, hj, hr, hinv⟩
  refine WP.mono (step_ok s₀ t hp hlen j hj hinv) fun t' ⟨hout, hz⟩ => ?_
  by_cases he : j + 1 = n
  · left
    refine ⟨?_, (by simpa only [he] using hout)⟩
    simp [eval, State.read, hz, he, n]
  · right
    have hne : BitVec.ofNat 64 (j + 1) ≠ s₀.gpr .x1 := by
      intro hh
      have := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s₀.gpr .x1).isLt; dsimp [n] at *; omega)] at this
      exact he this
    refine ⟨?_, n - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne, sub_zero, beq_eq_false_iff_ne.mpr hne]
    rfl

theorem finish_ok (s : State) (d : Byte) (ha : s.gpr .x4 = d.setWidth 64) :
    WP isa finish s fun t => t.mem = s.mem ∧
      (t.gpr .x0).setWidth 32 = if d = 0 then 1 else 0 := by
  unfold finish
  crun [ha]
  exact result64 d

theorem equal_ok (s₀ s : State) (hp : contract.pre s₀)
    (hlen : s₀.gpr .x3 = s₀.gpr .x1)
    (hk : Keep s₀ s) (hm : s.mem = s₀.mem) (ha : s.gpr .x4 = 0) :
    WP isa equal s fun t => t.mem = s₀.mem ∧ contract.post s₀ t := by
  have start : WP isa (.block [.movz .x .x8 0 0]) s (Inv s₀ 0) := by
    refine WP.mono (keep (Q := fun t => t.mem = s₀.mem ∧ t.gpr .x8 = 0 ∧ t.gpr .x4 = 0)
      ?_ (by rfl)) ?_
    · crun [hm, ha]
    · intro t ⟨⟨hm', hx', ha'⟩, hk'⟩
      exact ⟨hk.trans hk', hm', hx', ha'⟩
  unfold equal
  refine WP.seq (WP.mono start fun t hinv => WP.seq ?_)
  have h1 := hinv.1.1 .x1 (by decide)
  have after : WP isa (.ite (.zero .x .x1) (.block []) (.loop (.block step) (.nonzero .x .x9))) t
      (Inv s₀ (s₀.gpr .x1).toNat) := by
    by_cases he : s₀.gpr .x1 = 0
    · refine WP.ite true (by simp [eval, State.read, h1, he]) (fun _ => ?_) (by simp)
      apply WP.block_nil
      simpa only [he, (show (0 : BitVec 64).toNat = 0 from rfl)] using hinv
    · refine WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, h1,
          beq_eq_false_iff_ne.mpr he]) (by simp) (fun _ => ?_)
      exact loop_ok s₀ hp hlen t 0 (by bv_omega) hinv
  refine WP.mono after fun u hu => ?_
  refine WP.mono (finish_ok u _ hu.2.2.2) fun v ⟨hmv, hv⟩ => ?_
  refine ⟨hmv.trans hu.2.1, ?_⟩
  change (v.gpr .x0).setWidth 32 = _
  rw [hlen, diff_spec]
  simpa only [decide_eq_true_eq] using hv

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa eq s₀ fun t => t.mem = s₀.mem ∧ contract.post s₀ t := by
  have start : WP isa (.block [.movz .x .x4 0 0, .sub .x .x9 .x1 .x3]) s₀
      (fun t => Keep s₀ t ∧ t.mem = s₀.mem ∧ t.gpr .x4 = 0 ∧
        t.gpr .x9 = s₀.gpr .x1 - s₀.gpr .x3) := by
    refine WP.mono (keep (Q := fun t => t.mem = s₀.mem ∧ t.gpr .x4 = 0 ∧
        t.gpr .x9 = s₀.gpr .x1 - s₀.gpr .x3) ?_ (by rfl)) ?_
    · crun
    · intro t ⟨h, hk⟩; exact ⟨hk, h⟩
  unfold eq
  refine WP.seq (WP.mono start fun t ⟨hk, hm, ha, hz⟩ => ?_)
  by_cases he : s₀.gpr .x1 = s₀.gpr .x3
  · exact WP.ite true (by simp [eval, State.read, hz, he])
      (fun _ => equal_ok s₀ t hp he.symm hk hm ha) (by simp)
  · refine WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, hz, sub_zero,
      beq_eq_false_iff_ne.mpr he]) (by simp) (fun _ => ?_)
    have hn : (s₀.gpr .x1).toNat ≠ (s₀.gpr .x3).toNat := fun h => he (BitVec.eq_of_toNat_eq h)
    crun [hm, contract, lengths_ne _ _ _ hn]

def sat : State where
  gpr _ := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0, 0⟩]
  wr := []

theorem verified : Verified target eq (Spec.Ct.eqContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, hm, ho⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he⟩, ho⟩
    intro r hr
    have hc := instrs_keeps (c := eq) (rs := preserved) (by decide +kernel)
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
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
end VG.Proof.Ct.AArch64
