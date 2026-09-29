import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.Arm
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SHA-256 compression function on ARMv7: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.Arm

open VG VG.Arm VG.Impl.Sha256.Arm
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7]

/-- The pointers and the count: never written by the rounds. -/
def pubRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The address of `W[j mod 16]`, and of the intermediate sum. -/
abbrev slotAddr (scr : BitVec 32) (j : Nat) : Addr := State.addr (scr + BitVec.ofNat 32 (slot j))
abbrev tmpAddr (scr : BitVec 32) : Addr := State.addr (scr + BitVec.ofNat 32 tmp)

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers a round reads are not those it writes after them (`T1`,
`T2`, `d`, `h`). In parts: `decide` cannot synthesize the instance of one
long conjunction. -/
theorem round_ne₁ (t : Nat) :
    (¬var t 0 = .r12 ∧ ¬var t 0 = .lr ∧ ¬var t 1 = .r12 ∧ ¬var t 1 = .lr ∧
      ¬var t 2 = .r12 ∧ ¬var t 2 = .lr ∧ ¬var t 3 = .r12 ∧ ¬var t 3 = .lr) ∧
    (¬var t 4 = .r12 ∧ ¬var t 4 = .lr ∧ ¬var t 5 = .r12 ∧ ¬var t 5 = .lr ∧
      ¬var t 6 = .r12 ∧ ¬var t 6 = .lr ∧ ¬var t 7 = .r12 ∧ ¬var t 7 = .lr) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem round_ne₂ (t : Nat) :
    (¬var t 0 = var t 3 ∧ ¬var t 1 = var t 3 ∧ ¬var t 2 = var t 3 ∧ ¬var t 4 = var t 3 ∧
      ¬var t 5 = var t 3 ∧ ¬var t 6 = var t 3 ∧ ¬var t 7 = var t 3) ∧
    (¬var t 0 = var t 7 ∧ ¬var t 1 = var t 7 ∧ ¬var t 2 = var t 7 ∧ ¬var t 3 = var t 7 ∧
      ¬var t 4 = var t 7 ∧ ¬var t 5 = var t 7 ∧ ¬var t 6 = var t 7) ∧
    (¬Reg.r3 = var t 3 ∧ ¬Reg.r3 = var t 7 ∧ ¬Reg.r12 = var t 3 ∧ ¬Reg.r12 = var t 7 ∧
      ¬Reg.lr = var t 3 ∧ ¬Reg.lr = var t 7) := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The registers the rounds keep are none of those a round writes. -/
theorem pub_ne (t : Nat) :
    ∀ r ∈ pubRegs, ¬r = .r12 ∧ ¬r = .lr ∧ ¬r = var t 3 ∧ ¬r = var t 7 := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_ne₁`, `round_ne₂` and `pub_ne` say are different where it
matters), with the register writes kept folded (`VG.Arm.RegUpd`). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word) (scr : BitVec 32)
    (hv : Vars t s v) (hr3 : s.gpr .r3 = scr) (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hs : slot t < 4096 := by simp only [slot]; omega
  obtain ⟨n₁, n₂⟩ := round_ne₁ t
  obtain ⟨n₃, n₄, n₅⟩ := round_ne₂ t
  have hp := pub_ne t
  simp only [slotAddr] at hin hw
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.Arm.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T1, T2]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, isa, State.load32,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, ite_true, Nat.reduceLeDiff, and_self, not_false_eq_true, reduceCtorEq,
    n₁, n₂, n₃, n₄, n₅, h0, h1, h2, h3, h4, h5, h6, h7, hr3, hin, hw, hs,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · obtain ⟨p₁, p₂, p₃, p₄⟩ := hp r hr
    simp only [RegUpd.gpr_setReg_of_ne, p₁, p₂, p₃, p₄, not_false_eq_true]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1, ch_eq, bsig0, maj_eq, movw_movt, BitVec.add_assoc]

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32)
    (hr1 : s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (htin : InRegions (s.rd ++ s.wr) (tmpAddr scr) 4) (htout : InRegions s.wr (tmpAddr scr) 4)
    (htsep : ∀ j (m : Mem) (x : Word), (m.writeW (tmpAddr scr) x).readW (slotAddr scr j) 32 =
      m.readW (slotAddr scr j) 32)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : t < 16 → rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (∃ x : Word, s'.mem = (s.mem.writeW (tmpAddr scr) x).writeW (slotAddr scr t) (W M t) ∨
        s'.mem = s.mem.writeW (slotAddr scr t) (W M t)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  simp only [slotAddr, tmpAddr] at hin hout hwin htin htout htsep ⊢
  have hs : ∀ j, slot j < 4096 := fun j => by simp only [slot]; omega
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    have ho : 4 * t < 4096 := by omega
    simp only [Impl.Sha256.Arm.schedule, ht, ite_true, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
      RegUpd.rd_setReg,
      RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq, State.load32,
      State.store32, hr1, hr3, hi, hout, ho, hs, ite_true, hb, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨0, .inr trivial⟩, trivial, trivial, fun r h1 _ => ?_⟩
    simp only [RegUpd.gpr_setReg_of_ne, h1, not_false_eq_true]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    have htmp : tmp < 4096 := by decide
    simp only [Impl.Sha256.Arm.schedule, ht, ite_false, T1, T2]
    simp only [runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
      RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, Nat.reduceLeDiff, and_self, not_false_eq_true,
      reduceCtorEq, State.load32, State.store32, hr3, hin, hout, htin, htout, hs, htmp, ite_true,
      htsep, Mem.readW_writeW_self32, e2, e7, e15, e16, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    refine ⟨⟨ssig1 (W M (t - 2)) + W M (t - 7), .inl ?_⟩, trivial, trivial, fun r h1 h2 => ?_⟩
    · rw [hW]; rfl
    · simp only [RegUpd.gpr_setReg_of_ne, h1, h2, not_false_eq_true]

/-! ## The 64 rounds -/

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T1 ∧ r ≠ T2 := by decide

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T1 ∧ r ≠ T2 := by decide

/-- The scratch area the rounds write: the window and the intermediate sum. -/
abbrev workRegion (scr : BitVec 32) : Region := ⟨State.addr scr, 68⟩

theorem slotAddr_eq {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    slotAddr scr j = State.addr scr + BitVec.ofNat 64 (slot j) :=
  addr_add (by simp only [slot]; omega)

theorem tmpAddr_eq {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) :
    tmpAddr scr = State.addr scr + BitVec.ofNat 64 tmp :=
  addr_add (by simp only [tmp]; omega)

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem win_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    (workRegion scr).Contains (slotAddr scr j) 4 := by
  rw [slotAddr_eq h]; exact contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem tmp_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) :
    (workRegion scr).Contains (tmpAddr scr) 4 := by
  rw [tmpAddr_eq h]; exact contains_offset (by simp only [tmp]; omega) (by simp only [tmp]; omega)

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {i j : Nat}
    (hij : i % 16 ≠ j % 16) : Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  rw [slotAddr_eq h, slotAddr_eq h]
  simp only [slot]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem tmp_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    Mem.Sep (slotAddr scr j) 4 (tmpAddr scr) 4 := by
  rw [slotAddr_eq h, tmpAddr_eq h]
  simp only [slot, tmp]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [workRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hscr : scr.toNat + 112 ≤ 2 ^ 32)
    (hr1 : sB.gpr .r1 = bp) (hr3 : sB.gpr .r3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (htin : InRegions (sB.rd ++ sB.wr) (tmpAddr scr) 4) (htout : InRegions sB.wr (tmpAddr scr) 4)
    (hbin : ∀ t : Nat, t < 16 →
      InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : ∀ m, Frame [workRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev (m.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  have htsep : ∀ j (m : Mem) (x : Word), (m.writeW (tmpAddr scr) x).readW (slotAddr scr j) 32 =
      m.readW (slotAddr scr j) 32 := fun j m x => Mem.readW_writeW_sep (tmp_sep hscr j) (by decide)
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_r1 : s.gpr .r1 = bp := (hs.pub .r1 (by decide)).trans hr1
    have hs_r3 : s.gpr .r3 = scr := (hs.pub .r3 (by decide)).trans hr3
    refine WP.mono (schedule_ok t s M bp scr hs_r1 hs_r3
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (by rw [hs.rd, hs.wr]; exact htin) (by rw [hs.wr]; exact htout) htsep
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨⟨x, hm₁⟩, hrd₁, hwr₁, hr₁⟩ => ?_
    -- the new memory
    have hmem : s₁.mem = (s.mem.writeW (tmpAddr scr) x).writeW (slotAddr scr t) (W M t) ∨
        s₁.mem = s.mem.writeW (slotAddr scr t) (W M t) := hm₁
    have hframe₁ : Frame [workRegion scr] sB.mem s₁.mem := by
      rcases hmem with h | h <;> rw [h]
      · exact (hs.frame.writeW (List.mem_singleton_self _) _ (tmp_contains hscr)).writeW
          (List.mem_singleton_self _) _ (win_contains hscr t)
      · exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains hscr t)
    have hread : ∀ j, j % 16 ≠ t % 16 →
        s₁.mem.readW (slotAddr scr j) 32 = s.mem.readW (slotAddr scr j) 32 := by
      intro j hj
      rcases hmem with h | h <;> rw [h, Mem.readW_writeW_sep (slot_sep hscr hj) (by decide)]
      exact htsep j _ _
    have hself : s₁.mem.readW (slotAddr scr t) 32 = W M t := by
      rcases hmem with h | h <;> rw [h] <;> exact Mem.readW_writeW_self32 _ _ _
    have hv₁ : Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne' _ (var_mem t k); hr₁ _ this.1 this.2
      simp only [Vars, e] at hv ⊢
      exact hv
    have hr3₁ : s₁.gpr .r3 = scr := by
      rw [hr₁ .r3 (by decide) (by decide), hs_r3]
    refine WP.mono (round_ok t s₁ _ _ scr hv₁ hr3₁
      (by rw [hrd₁, hwr₁, hs.rd, hs.wr]; exact hin t) hself) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne' r hr
      rw [hr₂ r hr, hr₁ r this.1 this.2, hs.pub r hr]
    · rw [hm₂]; exact hframe₁
    · intro j hj hj'
      rw [hm₂]
      by_cases hjt : j = t
      · subst hjt; exact hself
      · rw [hread j (by omega)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha256.Arm
