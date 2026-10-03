import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.Arm
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.Arm.Contract
import VerifiedGarbage.Proof.Sha256.Arm.Lit

/-!
# SHA-256 compression function on ARMv7: the message schedule and the rounds
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

/-!
# SHA-256 compression function on ARMv7: the whole function
-/

namespace VG.Proof.Sha256.Arm

open VG VG.Arm VG.Impl.Sha256.Arm
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev stR : Region := ⟨State.addr (st s₀), 32⟩
abbrev blR : Region := ⟨State.addr (bp s₀), 64 * nb s₀⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (st s₀))

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (State.addr (bp s₀) + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := State.addr (st s₀ + BitVec.ofNat 32 (4 * k))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 8) :
    stAddr s₀ k = State.addr (st s₀) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.st_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t)) =
      State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega),
    addr_add (by omega)]

theorem in_state {k : Nat} (hk : k < 8) : InRegions (s₀.rd ++ s₀.wr) (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem out_state {k : Nat} (hk : k < 8) : InRegions s₀.wr (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega) (by simp only [slot]; omega)
    (slotAddr_eq h.scr_fits j)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega) (by simp only [slot]; omega)
    (slotAddr_eq h.scr_fits j)⟩

theorem in_tmp : InRegions (s₀.rd ++ s₀.wr) (tmpAddr (scr s₀)) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [tmp]; omega) (by simp only [tmp]; omega)
    (tmpAddr_eq h.scr_fits)⟩

theorem out_tmp : InRegions s₀.wr (tmpAddr (scr s₀)) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [tmp]; omega) (by simp only [tmp]; omega)
    (tmpAddr_eq h.scr_fits)⟩

theorem in_save {d : Nat} (hd : d + 4 ≤ 112) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 112) : InRegions s₀.wr (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    State.addr (bp s₀) + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := by
  exact Offset.sep p (by omega) (by omega) (by omega)

/-- Reading word `j` of the hash value after writing word `k`. -/
theorem readW_writeW_word {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {j k : Nat} (hj : j < 8)
    (hk : k < 8) (h : j ≠ k) :
    (m.writeW (stAddr s₀ k) v).readW (stAddr s₀ j) 32 = m.readW (stAddr s₀ j) 32 := by
  rw [hp.stAddr_eq hj, hp.stAddr_eq hk]
  exact Mem.readW_writeW_sep (word_sep _ hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m (State.addr (st s₀)) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (State.addr (st s₀)))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (State.addr (scr s₀)) s₀.gpr saved

theorem saved_slots : Spill.Slots 68 104 saved := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (State.addr (st s₀)) =
    compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r1 : s.gpr .r1 = blkAddr s₀ i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .ldr .r4 .r0 (4 * 0), .ldr .r5 .r0 (4 * 1), .ldr .r6 .r0 (4 * 2), .ldr .r7 .r0 (4 * 3),
    .ldr .r8 .r0 (4 * 4), .ldr .r9 .r0 (4 * 5), .ldr .r10 .r0 (4 * 6), .ldr .r11 .r0 (4 * 7)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .r12 .r0 (4 * 0), .dp .add .r4 .r4 (.reg .r12), .str .r4 .r0 (4 * 0),
    .ldr .r12 .r0 (4 * 1), .dp .add .r5 .r5 (.reg .r12), .str .r5 .r0 (4 * 1),
    .ldr .r12 .r0 (4 * 2), .dp .add .r6 .r6 (.reg .r12), .str .r6 .r0 (4 * 2),
    .ldr .r12 .r0 (4 * 3), .dp .add .r7 .r7 (.reg .r12), .str .r7 .r0 (4 * 3),
    .ldr .r12 .r0 (4 * 4), .dp .add .r8 .r8 (.reg .r12), .str .r8 .r0 (4 * 4),
    .ldr .r12 .r0 (4 * 5), .dp .add .r9 .r9 (.reg .r12), .str .r9 .r0 (4 * 5),
    .ldr .r12 .r0 (4 * 6), .dp .add .r10 .r10 (.reg .r12), .str .r10 .r0 (4 * 6),
    .ldr .r12 .r0 (4 * 7), .dp .add .r11 .r11 (.reg .r12), .str .r11 .r0 (4 * 7),
    .dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] ∧
    s.gpr .r8 = v[4] ∧ s.gpr .r9 = v[5] ∧ s.gpr .r10 = v[6] ∧ s.gpr .r11 = v[7] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .r0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (State.addr (st s₀))) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg,
    RegUpd.wr_setReg, State.load32,
    hr0, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 8 by decide), stateAt_get hp _ (show 1 < 8 by decide),
    stateAt_get hp _ (show 2 < 8 by decide), stateAt_get hp _ (show 3 < 8 by decide),
    stateAt_get hp _ (show 4 < 8 by decide), stateAt_get hp _ (show 5 < 8 by decide),
    stateAt_get hp _ (show 6 < 8 by decide), stateAt_get hp _ (show 7 < 8 by decide)]
  refine ⟨⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩, fun r hr => ?_, trivial⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [RegUpd.gpr_setReg_of_ne]

/-- Eight words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  ((((((((m.writeW (stAddr s₀ 0) v[0]).writeW (stAddr s₀ 1) v[1]).writeW (stAddr s₀ 2) v[2]).writeW
    (stAddr s₀ 3) v[3]).writeW (stAddr s₀ 4) v[4]).writeW (stAddr s₀ 5) v[5]).writeW
    (stAddr s₀ 6) v[6]).writeW (stAddr s₀ 7) v[7])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) (State.addr (st s₀)) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (stAddr s₀ k) (32 / 8) :=
    fun k hk => contains_sub (by omega) (by omega) (hp.stAddr_eq hk)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr0 : s.gpr .r0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r1 = s.gpr .r1 + 64 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 → InRegions s.wr (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.z_setReg,
    State.load32, State.store32, subFlags, hr0,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    readW_writeW_word hp,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · simp only [writeState, Vector.getElem_zipWith]
  all_goals trivial

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [workRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  rcases hf with hf | hf <;> refine h.frame saved_slots hf fun r hr => ?_ <;> rw [List.mem_singleton.mp hr]
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by decide))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    rev (s₀.mem.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, rev_readW]
  simp only [blk, blockAt, parseBlock]
  generalize State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) from Offset.add_add _ _ 1]

theorem work_sub (p : BitVec 32) : Region.Sub (workRegion p) ⟨State.addr p, 112⟩ :=
  Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [workRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (work_sub _)
  have hblk : ∀ m, Frame [workRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev (m.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  have hr1₁ : s₁.gpr .r1 = blkAddr s₀ i := (hpub₁ .r1 (by decide)).trans hL.r1
  have hr3₁ : s₁.gpr .r3 = scr s₀ := (hpub₁ .r3 (by decide)).trans hL.r3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hp.scr_fits hr1₁ hr3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_tmp)
    (by rw [hwr₁, hL.wr]; exact hp.out_tmp)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [workRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (work_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hr0₂ : s₂.gpr .r0 = st s₀ := by rw [pub₂ .r0 (by decide), hL.r0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (State.addr (st s₀))) hR.vars hr0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_sub (by omega) (by omega) (hp.stAddr_eq hk)) hst (by decide), hm₁,
      stateAt_get hp _ hk]
  obtain ⟨hm₃, hr1₃, hr2₃, hz₃, hr0₃, hr3₃, hrd₃, hwr₃⟩ := h₃
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr2 : s₂.gpr .r2 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [pub₂ .r2 (by decide), hL.r2, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact work_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState hp (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr0₃, hr0₂], by rw [hr3₃, pub₂ .r3 (by decide), hL.r3],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState hp (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hr2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with r1 := ?_, r2 := ?_ }⟩
    · rw [hr1₃, pub₂ .r1 (by decide), hL.r1]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat _) (by omega)))
    · rw [hr2₃, hr2]

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (scr s₀)) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.z = (s₀.gpr .r2 - 0 == 0) :=
  Spill.save_slots_ok saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 104 ≤ 112) _) hp.scr_fits) (fun _ _ hd => hp.out_save (by omega))
    (WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved _ _ _ _ saved_slots

theorem saveMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved s₀⟩
  · rw [hm]; exact (saveMem_frame s₀).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame s₀).readW (contains_sub (len := 32) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressArm.post s₀ s' := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := s₀.gpr) (by rw [hc.r3]; have := hp.scr_fits; omega)
    (fun _ _ hd => by rw [hc.rd, hc.wr, hc.r3]; exact hp.in_save (by omega)) (by rw [hc.r3]; exact hc.saved)
    fun s' hs _ hm _ _ _ => WP.block_nil ⟨Spill.restored_of hs (by decide), (congrArg (stateAt · _) hm).trans hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressArm.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        r1 := by rw [hg]; simp [blkAddr]
        r2 := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified Arm.target Impl.Sha256.Arm.compress Proof.Sha256.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    first
    | exact Offset.disjoint_of_le (by decide) (by decide)
    | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

end VG.Proof.Sha256.Arm
