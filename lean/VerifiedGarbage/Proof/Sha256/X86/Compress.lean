import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.X86
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.X86.Contract
import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# SHA-256 compression function on x86 (32-bit): the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.X86

open VG VG.X86 VG.Impl.Sha256.X86
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The working variables `v` are in the scratch buffer `scr` of memory `m`, at
the offsets of round `t`. -/
def Vars (t : Nat) (scr : BitVec 32) (m : Mem) (v : HashValue) : Prop :=
  m.readW (addr scr (var t 0)) 32 = v[0] ∧ m.readW (addr scr (var t 1)) 32 = v[1] ∧
  m.readW (addr scr (var t 2)) 32 = v[2] ∧ m.readW (addr scr (var t 3)) 32 = v[3] ∧
  m.readW (addr scr (var t 4)) 32 = v[4] ∧ m.readW (addr scr (var t 5)) 32 = v[5] ∧
  m.readW (addr scr (var t 6)) 32 = v[6] ∧ m.readW (addr scr (var t 7)) 32 = v[7]

/-- The pointers, the count and `esp`: never written by the rounds. -/
def pubRegs : List Reg := [.esi, .edi, .ebp, .esp]

/-- Facts about the scratch buffer at `scr`, for a memory access `[scr + d]`. -/
structure Scratch (s : State) (scr : BitVec 32) : Prop where
  fits : scr.toNat + 112 ≤ 2 ^ 32
  rd : ∀ d, d + 4 ≤ 112 → InRegions (s.rd ++ s.wr) (addr scr d) 4
  wr : ∀ d, d + 4 ≤ 112 → InRegions s.wr (addr scr d) 4

theorem scr_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {d e : Nat} (hd : d + 4 ≤ 112)
    (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr scr e) 4 (addr scr d) 4 := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- Reading `[scr + e]` after writing `[scr + d]`. -/
theorem readW_writeW_scr {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (x : Word)
    {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr scr d) x).readW (addr scr e) 32 = m.readW (addr scr e) 32 :=
  Mem.readW_writeW_sep (scr_sep h hd he hde) (by decide)

theorem slot_lt (j : Nat) : slot j + 4 ≤ 64 := by simp only [slot]; omega

/-- The working variables move one slot along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; omega

/-- The working variables of a round are in the scratch buffer, in separate words (stated
for each pair in both orders, for rewriting). -/
theorem round_sep (t : Nat) :
    (∀ x ∈ [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7], x + 4 ≤ 112) ∧
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7].Pairwise
      (fun x y => x + 4 ≤ y ∨ y + 4 ≤ x) ∧
    [var t 7, var t 6, var t 5, var t 4, var t 3, var t 2, var t 1, var t 0].Pairwise
      fun x y => x + 4 ≤ y ∨ y + 4 ≤ x := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- Chained rotations share each intermediate XOR, avoiding a temporary register copy. -/
theorem bsig0_chain (x : Word) :
    bsig0 x = ((x.rotateRight 9 ^^^ x).rotateRight 11 ^^^ x).rotateRight 2 := by
  simp only [rotateRight_xor, rotateRight_rotateRight, bsig0]
  ac_rfl

theorem bsig1_chain (x : Word) :
    bsig1 x = ((x.rotateRight 14 ^^^ x).rotateRight 5 ^^^ x).rotateRight 6 := by
  simp only [rotateRight_xor, rotateRight_rotateRight, bsig1]
  ac_rfl

theorem maj_chain (a b c : Word) :
    VG.Spec.Sha256.maj a b c = (b ^^^ c) &&& (a ^^^ b) ^^^ b := by
  ext i
  simp only [VG.Spec.Sha256.maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

/-- The round is symbolically executed once, for any offsets `a … h` of the
working variables (which `round_sep` says are in separate words). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word) (scr : BitVec 32)
    (hS : Scratch s scr) (hv : Vars t scr s.mem v) (hesi : s.gpr .esi = scr)
    (hw : s.mem.readW (addr scr (slot t)) 32 = w)
    (hbc : s.gpr .edx = v[1] ^^^ v[2]) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) scr s'.mem (roundKW v (K t) w) ∧
      s'.gpr .edx = v[0] ^^^ v[1] ∧
      (∃ x y : Word, s'.mem = (s.mem.writeW (addr scr (var t 3)) x).writeW (addr scr (var t 7)) y) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hin := hS.rd; have hout := hS.wr
  have hrw := readW_writeW_scr hS.fits
  have hs := hin (slot t) (by have := slot_lt t; omega)
  have hsep := round_sep t
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, List.Pairwise.nil, and_true, or_false,
    forall_eq] at hsep
  simp only
    [hsep, runBlock_cons, runBlock_nil, runStep_some, exec, execAlu, execShift, readSrc, ea_at, sc,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, not_false_eq_true,
    reduceCtorEq,
    State.load32, State.store32, ite_true, ite_false,
    hesi, hin, hout, hs, hrw, Mem.readW_writeW_self32, h0, h1, h2, h3, h4, h5, h6, h7, hw, hbc,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, ⟨_, _, rfl⟩, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        not_false_eq_true, reduceCtorEq]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1_chain, ch_eq, bsig0_chain, maj_chain, BitVec.add_assoc]

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32) (hS : Scratch s scr)
    (hedi : s.gpr .edi = bp) (hesi : s.gpr .esi = scr)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (addr bp (4 * t)) 4)
    (hblk : t < 16 → bswap (s.mem.readW (addr bp (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (addr scr (slot t)) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .edx = s.gpr .edx ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hin : ∀ j, InRegions (s.rd ++ s.wr) (addr scr (slot j)) 4 :=
    fun j => hS.rd _ (by have := slot_lt j; omega)
  have hout : ∀ j, InRegions s.wr (addr scr (slot j)) 4 :=
    fun j => hS.wr _ (by have := slot_lt j; omega)
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.X86.schedule, ht, ite_true]
    simp only [runBlock_cons, runBlock_nil, runStep_some, exec, readSrc,
      ea_at, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq,
      State.load32, State.store32, hedi, hesi, hi, hout, ite_true, hb,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_⟩
    simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_setReg_of_ne, not_false_eq_true, reduceCtorEq]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha256.X86.schedule, ht, ite_false, sc]
    simp only [runBlock_cons, runBlock_nil, runStep_some, exec, execAlu,
      execShift, readSrc, ea_at, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
      RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
      RegUpd.wr_setFlags, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self,
      not_false_eq_true, reduceCtorEq, State.load32, State.store32, hesi, hin, hout,
      ite_true, ite_false, e2, e7, e15, e16, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, trivial, trivial, trivial, fun r hr => ?_⟩
    rotate_right
    · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
          not_false_eq_true, reduceCtorEq]
    rw [W_ge M (t := t) (by omega), ssig1_eq, ssig0_eq]

/-! ## The 64 rounds -/

/-- The part of the scratch buffer the rounds write: the window and the working variables. -/
abbrev workRegion (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 96⟩

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem work_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 96) :
    (workRegion scr).Contains (addr scr d) (32 / 8) := by
  rw [addr_eq (by omega)]; exact contains_offset hd (by omega)

theorem var_lt (t k : Nat) : 64 ≤ var t k ∧ var t k + 4 ≤ 96 := by
  simp only [var]; omega

/-- The variables are unaffected by a write elsewhere in the scratch buffer. -/
theorem Vars.write {t : Nat} {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {m : Mem}
    {v : HashValue} (hv : Vars t scr m v) {d : Nat} (hd : d + 4 ≤ 112)
    (hsep : ∀ k, d + 4 ≤ var t k ∨ var t k + 4 ≤ d) (x : Word) :
    Vars t scr (m.writeW (addr scr d) x) v := by
  have e : ∀ k, (m.writeW (addr scr d) x).readW (addr scr (var t k)) 32 =
      m.readW (addr scr (var t k)) 32 := fun k =>
    readW_writeW_scr h m x hd (by have := var_lt t k; omega) (hsep k)
  simp only [Vars, e]
  exact hv

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : Vars t scr s.mem (VG.Spec.Sha256.rounds H M t)
  bc : s.gpr .edx = (VG.Spec.Sha256.rounds H M t)[1] ^^^ (VG.Spec.Sha256.rounds H M t)[2]
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [workRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j

theorem Scratch.congr {s s' : State} {scr : BitVec 32} (h : Scratch s scr) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Scratch s' scr :=
  ⟨h.fits, by rw [hrd, hwr]; exact h.rd, by rw [hwr]; exact h.wr⟩

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hS : Scratch sB scr) (hedi : sB.gpr .edi = bp) (hesi : sB.gpr .esi = scr)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (addr bp (4 * t)) 4)
    (hblk : ∀ m, Frame [workRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → bswap (m.readW (addr bp (4 * t)) 32) = W M t)
    (h0 : Vars 0 scr sB.mem H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  have hfits := hS.fits
  intro t ht
  induction t with
  | zero =>
    have hi1 := hS.rd (var 0 1) (by decide)
    have hi2 := hS.rd (var 0 2) (by decide)
    have h1 := h0.2.1
    have h2 := h0.2.2.1
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, runStep_some, exec,
      execAlu, readSrc, ea_at, sc, State.load32, hesi, hi1, hi2, h1, h2, ite_true,
      RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, not_false_eq_true,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, ?_, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    · rw [rounds_zero]; exact h0
    · rw [rounds_zero]
      simp only [RegUpd.gpr_setReg_self]
    · intro r hr
      simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [RegUpd.gpr_setReg_of_ne, RegUpd.gpr_arithFlags, reduceCtorEq, not_false_eq_true]
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_edi : s.gpr .edi = bp := (hs.pub .edi (by decide)).trans hedi
    have hs_esi : s.gpr .esi = scr := (hs.pub .esi (by decide)).trans hesi
    refine WP.mono (schedule_ok t s M bp scr (hS.congr hs.rd hs.wr) hs_edi hs_esi
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hdx₁, hr₁⟩ => ?_
    have hslot := slot_lt t
    have hframe₁ : Frame [workRegion scr] sB.mem s₁.mem := by
      rw [hm₁]; exact hs.frame.writeW (List.mem_singleton_self _) _ (work_contains hfits (by omega))
    have hself : s₁.mem.readW (addr scr (slot t)) 32 = W M t := by
      rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
    have hv₁ : Vars t scr s₁.mem (VG.Spec.Sha256.rounds H M t) := by
      rw [hm₁]
      exact hs.vars.write hfits (by omega) (fun k => .inl (by have := var_lt t k; omega)) _
    have hesi₁ : s₁.gpr .esi = scr := by rw [hr₁ .esi (by decide), hs_esi]
    refine WP.mono (round_ok t s₁ _ _ scr (hS.congr (by rw [hrd₁, hs.rd]) (by rw [hwr₁, hs.wr]))
      hv₁ hesi₁ hself (hdx₁.trans hs.bc)) fun s₂ ⟨hv₂, hdx₂, ⟨x, y, hm₂⟩, hrd₂, hwr₂, hr₂⟩ => ?_
    have h3 := var_lt t 3
    have h7 := var_lt t 7
    refine ⟨?_, ?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · rw [rounds_succ, round_eq, roundKW_1, roundKW_2]; exact hdx₂
    · rw [hr₂ r hr, hr₁ r hr, hs.pub r hr]
    · rw [hm₂]
      exact (hframe₁.writeW (List.mem_singleton_self _) _ (work_contains hfits (by omega))).writeW
        (List.mem_singleton_self _) _ (work_contains hfits (by omega))
    · intro j hj hj'
      have hsj := slot_lt j
      rw [hm₂, readW_writeW_scr hfits _ _ (by omega) (by omega) (.inr (by omega)),
        readW_writeW_scr hfits _ _ (by omega) (by omega) (.inr (by omega))]
      by_cases hjt : j = t
      · subst hjt; exact hself
      · rw [hm₁, readW_writeW_scr hfits _ _ (by omega) (by omega) ?_]
        · exact hs.win j (by omega) (by omega)
        · simp only [slot] at hsj hslot ⊢; omega

end VG.Proof.Sha256.X86

/-!
# SHA-256 compression function on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.X86

open VG VG.X86 VG.Impl.Sha256.X86
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(st s₀).setWidth 64, 32⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 64 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 112⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((st s₀).setWidth 64)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := addr (st s₀) (4 * k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 :=
  rfl

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 8) :
    stAddr s₀ k = (st s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by have := h.st_fits; omega)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    addr (blkAddr s₀ i) (4 * t) =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega)]
  have e : (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    have := addr_eq (x := bp s₀) (k := 64 * i) (by omega)
    simpa only [addr] using this
  rw [e]

theorem scr_eq {d : Nat} (hd : d < 112) :
    addr (scr s₀) d = (scr s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.scr_fits; omega)

theorem scratch : Scratch s₀ (scr s₀) :=
  ⟨h.scr_fits, fun d hd => ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.scr_eq (by omega))⟩,
    fun d hd => ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.scr_eq (by omega))⟩⟩

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  simp only [Region.Contains, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  have := h.esp_fits
  rw [Offset.add_sub_add _ hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_arg {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  simp only [argR, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by omega),
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, h.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (addr (blkAddr s₀ i) (4 * t)) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem st_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 32) (he : e + 4 ≤ 32)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (st s₀) d) 4 (addr (st s₀) e) 4 := by
  rw [addr_eq (by have := hp.st_fits; omega), addr_eq (by have := hp.st_fits; omega)]
  exact Offset.sep _ hde (by omega) (by omega)

/-- Reading the hash value at offset `d` after writing it at offset `e`. -/
theorem readW_writeW_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 32) (he : e + 4 ≤ 32) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (st s₀) e) v).readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 :=
  Mem.readW_writeW_sep (st_sep hp hd he hde) (by decide)

theorem st_eq {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 32) :
    addr (st s₀) d = (st s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem st_scr_sep {s₀ : State} (hp : Pre s₀) {e d : Nat} (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    Mem.Sep (addr (st s₀) e) 4 (addr (scr s₀) d) 4 :=
  hp.st_scr.sep (contains_sub he (by omega) (st_eq hp (by omega)))
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))

/-- Reading the hash value after writing the scratch buffer. -/
theorem readW_writeW_scr_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (st s₀) e) 32 = m.readW (addr (st s₀) e) 32 :=
  Mem.readW_writeW_sep (st_scr_sep hp he hd) (by decide)

/-- Reading the scratch buffer after writing the hash value. -/
theorem readW_writeW_st_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 32) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (st s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (fun x h₁ h₂ => st_scr_sep hp he hd x h₂ h₁) (by decide)

theorem in_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions (s₀.rd ++ s₀.wr) (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem out_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions s₀.wr (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m ((st s₀).setWidth 64) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m ((st s₀).setWidth 64))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (addr (scr s₀) 96) 32 = s₀.gpr .ebx ∧ m.readW (addr (scr s₀) 100) 32 = s₀.gpr .esi ∧
  m.readW (addr (scr s₀) 104) 32 = s₀.gpr .edi ∧ m.readW (addr (scr s₀) 108) 32 = s₀.gpr .ebp

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((st s₀).setWidth 64) =
    compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (nb s₀ - i)

/-! ## One block -/

/-- Word `k` of the load: copy `state[k]` to its working variable. -/
def ld (k : Nat) : List Instr :=
  [.mov .ebx (.mem ⟨.eax, 4 * k⟩), .store ⟨.esi, 64 + 4 * k⟩ .ebx]

/-- Words `0 … j-1` of the load. -/
def ldTo (j : Nat) : List Instr := (List.range j).flatMap ld

theorem ldTo_succ (j : Nat) : ldTo (j + 1) = ldTo j ++ ld j := by
  simp [ldTo, List.range_succ, List.flatMap_append]

theorem load_eq : load = ([.mov .eax (.mem ⟨.esp, 4⟩)] : List Instr) ++ ldTo 8 := by
  decide

/-- Word `k` of the update: `state[k] := var k + state[k]`. -/
def upd (k : Nat) : List Instr :=
  [.mov .ebx (.mem ⟨.esi, 64 + 4 * k⟩), .alu .add .ebx (.mem ⟨.eax, 4 * k⟩),
   .store ⟨.eax, 4 * k⟩ .ebx]

/-- Words `0 … j-1` of the update. -/
def updTo (j : Nat) : List Instr := (List.range j).flatMap upd

theorem updTo_succ (j : Nat) : updTo (j + 1) = updTo j ++ upd j := by
  simp [updTo, List.range_succ, List.flatMap_append]

theorem update_eq : update ++ advance = ([.mov .eax (.mem ⟨.esp, 4⟩)] : List Instr) ++ (updTo 8 ++ advance) := by
  decide

theorem vars0 (scr : BitVec 32) (m : Mem) (v : HashValue) : Vars 0 scr m v ↔
    m.readW (addr scr 64) 32 = v[0] ∧ m.readW (addr scr 68) 32 = v[1] ∧
    m.readW (addr scr 72) 32 = v[2] ∧ m.readW (addr scr 76) 32 = v[3] ∧
    m.readW (addr scr 80) 32 = v[4] ∧ m.readW (addr scr 84) 32 = v[5] ∧
    m.readW (addr scr 88) 32 = v[6] ∧ m.readW (addr scr 92) 32 = v[7] := Iff.rfl

/-- Eight words written in order to the working variables. -/
def writeVars (scr : BitVec 32) (m : Mem) (v : HashValue) : Mem :=
  ((((((((m.writeW (addr scr 64) v[0]).writeW (addr scr 68) v[1]).writeW (addr scr 72) v[2]).writeW
    (addr scr 76) v[3]).writeW (addr scr 80) v[4]).writeW (addr scr 84) v[5]).writeW
    (addr scr 88) v[6]).writeW (addr scr 92) v[7])

set_option simprocs false in
theorem vars_writeVars {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (v : HashValue) :
    Vars 0 scr (writeVars scr m v) v := by
  have hrw := readW_writeW_scr h
  rw [vars0]
  simp only [writeVars]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hrw]

theorem frame_writeVars {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (v : HashValue) :
    Frame [workRegion scr] m (writeVars scr m v) := by
  have c : ∀ d, d + 4 ≤ 96 → (workRegion scr).Contains (addr scr d) (32 / 8) :=
    fun d hd => work_contains h hd
  have mm := List.mem_singleton_self (workRegion scr)
  simp only [writeVars]
  exact ((((((((Frame.refl _ _).writeW mm _ (c 64 (by omega))).writeW mm _ (c 68 (by omega))).writeW
    mm _ (c 72 (by omega))).writeW mm _ (c 76 (by omega))).writeW mm _ (c 80 (by omega))).writeW
    mm _ (c 84 (by omega))).writeW mm _ (c 88 (by omega))).writeW mm _ (c 92 (by omega))

theorem ld_ok (k : Nat) {s : State} {p q : BitVec 32} (heax : s.gpr .eax = p)
    (hesi : s.gpr .esi = q) (hi : InRegions (s.rd ++ s.wr) (addr p (4 * k)) 4)
    (ho : InRegions s.wr (addr q (64 + 4 * k)) 4) :
    WP isa (.block (ld k)) s fun s' =>
      s'.mem = s.mem.writeW (addr q (64 + 4 * k)) (s.mem.readW (addr p (4 * k)) 32) ∧
      (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ld, runBlock_cons, runBlock_nil, runStep_some, exec,
    readSrc, ea_mk, State.setReg, State.load32, State.store32, heax, hesi, hi, ho, ite_true,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The working variables at `q` after loading words `0 … j-1` of the hash value at `p`. -/
def copyWords (p q : BitVec 32) (m : Mem) : Nat → Mem
  | 0 => m
  | j + 1 => (copyWords p q m j).writeW (addr q (64 + 4 * j)) (m.readW (addr p (4 * j)) 32)

theorem copyWords_st {s₀ : State} (hp : Pre s₀) (m : Mem) {i : Nat} (hi : i < 8) :
    ∀ j ≤ 8, (copyWords (st s₀) (scr s₀) m j).readW (addr (st s₀) (4 * i)) 32 =
      m.readW (addr (st s₀) (4 * i)) 32
  | 0, _ => rfl
  | j + 1, hj => by
    rw [copyWords, readW_writeW_scr_st hp _ _ (by omega) (by omega)]
    exact copyWords_st hp m hi j (by omega)

theorem ldTo_ok {s₀ : State} (hp : Pre s₀) {s : State} (heax : s.gpr .eax = st s₀)
    (hesi : s.gpr .esi = scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∀ j ≤ 8, WP isa (.block (ldTo j)) s fun s' =>
      s'.mem = copyWords (st s₀) (scr s₀) s.mem j ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil (M := isa) ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  | j + 1, hj => by
    rw [ldTo_succ, WP.block_append_iff]
    refine WP.mono (ldTo_ok hp heax hesi hrd hwr j (by omega))
      fun s₁ ⟨hm₁, hr₁, hrd₁, hwr₁⟩ => ?_
    refine WP.mono (ld_ok j (p := st s₀) (q := scr s₀)
      (by rw [hr₁ .eax (by decide), heax]) (by rw [hr₁ .esi (by decide), hesi])
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact in_st hp (by omega))
      (by rw [hwr₁, hwr]; exact hp.scratch.wr _ (by omega))) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, hr₁ r hr], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
    rw [hm₂, hm₁, copyWords_st hp _ (by omega) j (by omega)]
    rfl

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hesp : s.gpr .esp = esp₀ s₀)
    (hesi : s.gpr .esi = scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀) :
    WP isa (.block load) s fun s₁ =>
      s₁.mem = writeVars (scr s₀) s.mem (stateAt s.mem ((st s₀).setWidth 64)) ∧
      (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  -- `mov eax, [esp + 4]`
  have h₁ : WP isa (.block [.mov .eax (.mem ⟨.esp, 4⟩)]) s fun s₁ =>
      s₁.gpr .eax = st s₀ ∧ (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, runStep_some, exec,
      readSrc, ea_mk, State.setReg, State.load32, hesp, ia, harg, ite_true, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  rw [load_eq, WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨he₁, hr₁, hm₁, hrd₁, hwr₁⟩ => ?_
  refine WP.mono (ldTo_ok hp he₁ (by rw [hr₁ .esi (by decide), hesi]) (hrd₁.trans hrd)
    (hwr₁.trans hwr) 8 (Nat.le_refl _)) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
  refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁]
    simp only [copyWords, writeVars, stateAt_get hp _ (show 0 < 8 by decide),
      stateAt_get hp _ (show 1 < 8 by decide), stateAt_get hp _ (show 2 < 8 by decide),
      stateAt_get hp _ (show 3 < 8 by decide), stateAt_get hp _ (show 4 < 8 by decide),
      stateAt_get hp _ (show 5 < 8 by decide), stateAt_get hp _ (show 6 < 8 by decide),
      stateAt_get hp _ (show 7 < 8 by decide), stAddr, Nat.reduceMul, Nat.reduceAdd]
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [hr₂ _ (by decide), hr₁ _ (by decide)]

/-- Eight words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  let a := addr (st s₀)
  ((((((((m.writeW (a 0) v[0]).writeW (a 4) v[1]).writeW (a 8) v[2]).writeW (a 12) v[3]).writeW
    (a 16) v[4]).writeW (a 20) v[5]).writeW (a 24) v[6]).writeW (a 28) v[7])

theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) ((st s₀).setWidth 64) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState, stAddr]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) (disch := decide) only [Nat.reduceMul, Mem.readW_writeW_self32,
    readW_writeW_st hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ d, d + 4 ≤ 32 → (stR s₀).Contains (addr (st s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (st_eq hp (by omega))
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 8 ?_)).writeW ?_ _
    (c 12 ?_)).writeW ?_ _ (c 16 ?_)).writeW ?_ _ (c 20 ?_)).writeW ?_ _ (c 24 ?_)).writeW ?_ _
    (c 28 ?_) <;>
  simp

theorem upd_ok (k : Nat) {s : State} {p q : BitVec 32} (heax : s.gpr .eax = p)
    (hesi : s.gpr .esi = q) (hv : InRegions (s.rd ++ s.wr) (addr q (64 + 4 * k)) 4)
    (hh : InRegions (s.rd ++ s.wr) (addr p (4 * k)) 4) (ho : InRegions s.wr (addr p (4 * k)) 4) :
    WP isa (.block (upd k)) s fun s' =>
      s'.mem = s.mem.writeW (addr p (4 * k))
        (s.mem.readW (addr q (64 + 4 * k)) 32 + s.mem.readW (addr p (4 * k)) 32) ∧
      (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [upd, runBlock_cons, runBlock_nil, runStep_some, exec,
    execAlu, readSrc, ea_mk, State.setReg, arithFlags, State.setFlags, State.load32, State.store32,
    heax, hesi, hv, hh, ho, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-- The hash value at `p` after updating words `0 … j-1` from the variables at `q`. -/
def writeWords (p q : BitVec 32) (m : Mem) : Nat → Mem
  | 0 => m
  | j + 1 => (writeWords p q m j).writeW (addr p (4 * j))
      (m.readW (addr q (64 + 4 * j)) 32 + m.readW (addr p (4 * j)) 32)

theorem writeWords_scr {s₀ : State} (hp : Pre s₀) (m : Mem) {i : Nat} (hi : i < 8) :
    ∀ j ≤ 8, (writeWords (st s₀) (scr s₀) m j).readW (addr (scr s₀) (64 + 4 * i)) 32 =
      m.readW (addr (scr s₀) (64 + 4 * i)) 32
  | 0, _ => rfl
  | j + 1, hj => by
    rw [writeWords, readW_writeW_st_scr hp _ _ (by omega) (by omega)]
    exact writeWords_scr hp m hi j (by omega)

theorem writeWords_st {s₀ : State} (hp : Pre s₀) (m : Mem) {i : Nat} (hi : i < 8) :
    ∀ j ≤ i, (writeWords (st s₀) (scr s₀) m j).readW (addr (st s₀) (4 * i)) 32 =
      m.readW (addr (st s₀) (4 * i)) 32
  | 0, _ => rfl
  | j + 1, hj => by
    rw [writeWords, readW_writeW_st hp _ _ (by omega) (by omega) (by omega)]
    exact writeWords_st hp m hi j (by omega)

theorem updTo_ok {s₀ : State} (hp : Pre s₀) {s : State} (heax : s.gpr .eax = st s₀)
    (hesi : s.gpr .esi = scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∀ j ≤ 8, WP isa (.block (updTo j)) s fun s' =>
      s'.mem = writeWords (st s₀) (scr s₀) s.mem j ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil (M := isa) ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
  | j + 1, hj => by
    rw [updTo_succ, WP.block_append_iff]
    refine WP.mono (updTo_ok hp heax hesi hrd hwr j (by omega))
      fun s₁ ⟨hm₁, hr₁, hrd₁, hwr₁⟩ => ?_
    refine WP.mono (upd_ok j (p := st s₀) (q := scr s₀)
      (by rw [hr₁ .eax (by decide), heax]) (by rw [hr₁ .esi (by decide), hesi])
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact hp.scratch.rd _ (by omega))
      (by rw [hrd₁, hwr₁, hrd, hwr]; exact in_st hp (by omega))
      (by rw [hwr₁, hwr]; exact out_st hp (by omega))) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hr₂ r hr, hr₁ r hr], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
    rw [hm₂, hm₁, writeWords_scr hp _ (by omega) j (by omega),
      writeWords_st hp _ (by omega) j (by omega)]
    rfl

theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue)
    (hv : Vars 0 (scr s₀) s.mem V) (hesp : s.gpr .esp = esp₀ s₀) (hesi : s.gpr .esi = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
      s'.zf = some (s.gpr .ebp - 1 == 0) ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  -- `mov eax, [esp + 4]`
  have h₁ : WP isa (.block [.mov .eax (.mem ⟨.esp, 4⟩)]) s fun s₁ =>
      s₁.gpr .eax = st s₀ ∧ (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, runStep_some, exec,
      readSrc, ea_mk, State.setReg, State.load32, hesp, ia, harg, ite_true, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  rw [update_eq, WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨he₁, hr₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (updTo_ok hp he₁ (by rw [hr₁ .esi (by decide), hesi]) (hrd₁.trans hrd)
    (hwr₁.trans hwr) 8 (Nat.le_refl _)) fun s₂ ⟨hm₂, hr₂, hrd₂, hwr₂⟩ => ?_
  have hr : ∀ r, r ≠ .eax → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [hr₂ r h2, hr₁ r h1]
  -- `add edi, 64; sub ebp, 1`
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runBlock_nil, runStep_some, exec,
    execAlu, readSrc, State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [hm₂, hm₁]
    rw [vars0] at hv
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
    have m0 : s.mem.readW (addr (st s₀) 0) 32 = H[0]'(by decide) := hH 0 (by decide)
    have m1 : s.mem.readW (addr (st s₀) 4) 32 = H[1]'(by decide) := hH 1 (by decide)
    have m2 : s.mem.readW (addr (st s₀) 8) 32 = H[2]'(by decide) := hH 2 (by decide)
    have m3 : s.mem.readW (addr (st s₀) 12) 32 = H[3]'(by decide) := hH 3 (by decide)
    have m4 : s.mem.readW (addr (st s₀) 16) 32 = H[4]'(by decide) := hH 4 (by decide)
    have m5 : s.mem.readW (addr (st s₀) 20) 32 = H[5]'(by decide) := hH 5 (by decide)
    have m6 : s.mem.readW (addr (st s₀) 24) 32 = H[6]'(by decide) := hH 6 (by decide)
    have m7 : s.mem.readW (addr (st s₀) 28) 32 = H[7]'(by decide) := hH 7 (by decide)
    simp only [writeWords, writeState, Nat.reduceMul, Nat.reduceAdd, v0, v1, v2, v3, v4, v5, v6,
      v7, m0, m1, m2, m3, m4, m5, m6, m7, Vector.getElem_zipWith]
  all_goals simp (config := {decide := true}) [hr]

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [workRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 96 ≤ d → d + 4 ≤ 112 →
      m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
    intro d hd hd'
    have hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
      Region.contains_self _ _
    rcases hf with hf | hf
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      rw [hp.scr_eq (by omega)]
      exact Offset.disjoint_base _ (by omega) (by omega)
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      refine Region.Disjoint.sub_left hp.st_scr.symm ?_
      rw [hp.scr_eq (by omega)]
      exact Offset.sub_base _ (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(key 96 (by omega) (by omega)).trans h1, (key 100 (by omega) (by omega)).trans h2,
    (key 104 (by omega) (by omega)).trans h3, (key 108 (by omega) (by omega)).trans h4⟩

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    bswap (s₀.mem.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, bswap_readW]
  simp only [blk, blockAt, parseBlock]
  generalize (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) from Offset.add_add _ _ 1,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) from Offset.add_add _ _ 1]

theorem work_sub (p : BitVec 32) : Region.Sub (workRegion p) ⟨p.setWidth 64, 112⟩ :=
  Region.sub_prefix (by omega)

theorem harg_of {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    m.readW (addr (esp₀ s₀) 4) 32 = st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hfits := hp.scr_fits
  refine WP.seq (WP.mono (load_ok hp hL.esp hL.esi hL.rd hL.wr (harg_of hp hL.frame))
    fun s₁ ⟨hm₁, hpub₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [workRegion (scr s₀)] s.mem s₁.mem := by rw [hm₁]; exact frame_writeVars hfits _ _
  have hwin : ∀ r' ∈ [workRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (work_sub _)
  have hblk : ∀ m, Frame [workRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap (m.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide),
      hf₁.readW (hp.blk_contains hi ht) hwin (by decide),
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  have hedi₁ : s₁.gpr .edi = blkAddr s₀ i := (hpub₁ .edi (by decide)).trans hL.edi
  have hesi₁ : s₁.gpr .esi = scr s₀ := (hpub₁ .esi (by decide)).trans hL.esi
  have hv₁ : Vars 0 (scr s₀) s₁.mem (stateAt s.mem ((st s₀).setWidth 64)) := by
    rw [hm₁]; exact vars_writeVars hfits _ _
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁
    (hp.scratch.congr (by rw [hrd₁, hL.rd]) (by rw [hwr₁, hL.wr])) hedi₁ hesi₁
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [workRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (work_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hf₂ : Frame [workRegion (scr s₀)] s.mem s₂.mem := hf₁.trans hR.frame
  have hframe₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hL.frame.trans (hf₂.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact work_sub _⟩)
  refine WP.mono (update_ok hp _ (stateAt s.mem ((st s₀).setWidth 64)) hR.vars
    (by rw [pub₂ .esp (by decide), hL.esp]) (by rw [pub₂ .esi (by decide), hL.esi])
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) (harg_of hp hframe₂) fun k hk => ?_)
    fun s₃ h₃ => ?_
  · rw [hf₂.readW (contains_sub (by omega) (by omega) (hp.stAddr_eq hk)) hst (by decide),
      stateAt_get hp _ hk]
  obtain ⟨hm₃, hedi₃, hebp₃, hz₃, hesi₃, hesp₃, hrd₃, hwr₃⟩ := h₃
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hebp : s₂.gpr .ebp - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [pub₂ .ebp (by decide), hL.ebp, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hframe₂.trans ?_
    rw [hm₃]
    exact (frame_writeState hp (Frame.refl _ _) _).sub
      fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hesi₃, pub₂ .esi (by decide), hL.esi],
      by rw [hesp₃, pub₂ .esp (by decide), hL.esp],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState hp (Frame.refl _ _) _))
      exact saved_frame hp hL.saved (.inl hf₂)
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hebp, Option.map_some]
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
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with edi := ?_, ebp := ?_ }⟩
    · rw [hedi₃, pub₂ .edi (by decide), hL.edi]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat _) (by omega)))
    · rw [hebp₃, hebp]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = [.mov .eax (.mem ⟨.esp, 16⟩), .store ⟨.eax, 96⟩ .ebx,
    .store ⟨.eax, 100⟩ .esi, .store ⟨.eax, 104⟩ .edi, .store ⟨.eax, 108⟩ .ebp,
    .mov .esi (.reg .eax), .mov .edi (.mem ⟨.esp, 8⟩), .mov .ebp (.mem ⟨.esp, 12⟩),
    .alu .test .ebp (.reg .ebp)] := rfl

/-- Reading an argument after writing the scratch buffer. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 112) (he : 4 ≤ e) (he' : e + 4 ≤ 20) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (esp₀ s₀) e) 32 = m.readW (addr (esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))) (by decide)

theorem epilogue_eq : epilogue = [.mov .ebx (.mem ⟨.esi, 96⟩), .mov .edi (.mem ⟨.esi, 104⟩),
    .mov .ebp (.mem ⟨.esi, 108⟩), .mov .esi (.mem ⟨.esi, 100⟩)] := rfl

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 96) (s₀.gpr .ebx)).writeW (addr (scr s₀) 100) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 104) (s₀.gpr .edi)).writeW (addr (scr s₀) 108) (s₀.gpr .ebp)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = scr s₀ ∧ s₁.gpr .edi = bp s₀ ∧ s₁.gpr .ebp = arg s₀ 2 ∧
      s₁.gpr .esp = esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hsa := readW_writeW_scr_arg hp
  have i8 := hp.in_arg (d := 8) (by omega) (by omega)
  have i12 := hp.in_arg (d := 12) (by omega) (by omega)
  have i16 := hp.in_arg (d := 16) (by omega) (by omega)
  have a8 : s₀.mem.readW (addr (esp₀ s₀) 8) 32 = bp s₀ := rfl
  have a12 : s₀.mem.readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := rfl
  have a16 : s₀.mem.readW (addr (esp₀ s₀) 16) 32 = scr s₀ := rfl
  have hout := hp.scratch.wr
  apply WP.of_runBlock
  rw [prologue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, execAlu, readSrc, ea_mk, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags,
    State.load32, State.store32, i8, i12, i16, a8, a12, a16, hout, hsa, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hrw := readW_writeW_scr hp.scr_fits
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hrw]

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 112 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (hp.scr_eq (by omega))
  simp only [saveMem]
  have m := List.mem_singleton_self (scrR s₀)
  exact ((((Frame.refl _ _).writeW m _ (c 96 (by omega))).writeW m _ (c 100 (by omega))).writeW
    m _ (c 104 (by omega))).writeW m _ (c 108 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = scr s₀)
    (hesp : s₁.gpr .esp = esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨hesi, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩
  · rw [hm]; exact (saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame hp).readW (contains_sub (len := 32) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ d, d + 4 ≤ 112 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
    rw [hc.rd, hc.wr]; exact hp.scratch.rd
  obtain ⟨g0, g1, g2, g3⟩ := hc.saved
  have hesi := hc.esi
  have hesp := hc.esp
  apply WP.of_runBlock
  rw [epilogue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, readSrc, ea_mk,
    RegUpd.gpr_setReg_of_ne,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, hesi, hin,
    g0, g1, g2, g3, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, hesp]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha256.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hesi, hedi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
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
        edi := by rw [hedi]; simp [blkAddr]
        ebp := by rw [hebp]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem sat_pre : Proof.Sha256.compressX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0 := by decide
  have a3 : arg satState 3 = 0x3000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha256.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  first
  | exact Offset.disjoint_of_le (by decide) (by decide)
  | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 112], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha256.compressX86.pre s₁)
    (h₂ : Proof.Sha256.compressX86.pre s₂) (hpub : Proof.Sha256.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sha256.X86.compress Proof.Sha256.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sha256.X86
