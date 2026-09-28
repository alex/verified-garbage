import Mathlib.Data.List.Nodup
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.PPC64LE

/-!
# SHA-256 compression function on PPC64LE: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha256.PPC64LE
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  (s.gpr (var t 0)).setWidth 32 = v[0] ∧ (s.gpr (var t 1)).setWidth 32 = v[1] ∧
  (s.gpr (var t 2)).setWidth 32 = v[2] ∧ (s.gpr (var t 3)).setWidth 32 = v[3] ∧
  (s.gpr (var t 4)).setWidth 32 = v[4] ∧ (s.gpr (var t 5)).setWidth 32 = v[5] ∧
  (s.gpr (var t 6)).setWidth 32 = v[6] ∧ (s.gpr (var t 7)).setWidth 32 = v[7]

/-- The pointers, the count and the nonvolatile registers the rounds do not
use: never written by the rounds. -/
def pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r2, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27, .r28, .r29, .r30, .r31]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    ([var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2, T3] ++
      pubRegs).Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  interval_cases c <;> decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the others). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : (s.gpr T0).setWidth 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hd' := List.nodup_reverse.mpr (round_nodup t)
  -- The registers the round reads and writes.
  have hs := (List.nodup_append.mp (round_nodup t)).1
  have hs' := List.nodup_reverse.mpr hs
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.PPC64LE.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2, T3, pubRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs' hd' hw ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.read, State.write, Size.bits, Size.ext,
    ite_true, ite_false, hs, hs', Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [hd']
  all_goals
    simp (config := {decide := true}) only [lo32_add, BitVec.setWidth_xor, BitVec.setWidth_and,
      BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, lis_ori', h0, h1, h2,
      h3, h4, h5, h6, h7, hw]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW, bsig1, ch_eq, bsig0, maj_eq,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] <;>
    simp (config := {failIfUnchanged := false}) only [BitVec.add_assoc]

theorem slot_ok (j : Nat) : slot j < 2 ^ 15 := by
  simp only [slot]; omega

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hr4 : s.gpr .r4 = bp) (hr6 : s.gpr .r6 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : t < 16 → rev32 (s.mem.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      (s'.gpr T0).setWidth 32 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → r ≠ .r0 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.PPC64LE.schedule, ht, ite_true, T0, T1, T2, T3]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec_li (show 4 * t < 2 ^ 15 by omega), exec_loadRev_w, exec_store_w,
      slot_ok, isa, State.write, hr4, hr6, hi, hout, ite_true,
      ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, hb,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 _ _ _ h4 => ?_⟩
    simp [h0, h4]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha256.PPC64LE.schedule, ht, ite_false, T0, T1, T2, T3]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec_load_w, exec_store_w, slot_ok, exec_add, exec_logic, exec_rotr_w,
      exec_lsr_w, isa, State.write, hr6, hin, hout, ite_true, ite_false, Option.some.injEq,
      exists_eq_left']
    simp (config := {decide := true}) only [lo32_add, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, e2, e7, e15, e16]
    have hW := W_ge M (t := t) (by omega)
    refine ⟨by rw [hW]; rfl, by rw [hW]; rfl, trivial, trivial, fun r h0 h1 h2 h3 _ => ?_⟩
    simp [h0, h1, h2, h3]

/-! ## The 64 rounds -/

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 ∧ r ≠ .r0 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 64⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 4 := by
  simp only [Region.Contains, slotAddr, slot]
  have : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize j % 16 = p at *
  rw [show scr + BitVec.ofNat 64 (4 * p) - scr = BitVec.ofNat 64 (4 * p) by bv_omega]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  intro x hx hy
  simp only [slotAddr, slot] at hx hy
  have hi : i % 16 < 16 := Nat.mod_lt _ (by omega)
  have hj : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize i % 16 = p at *
  generalize j % 16 = q at *
  bv_omega

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha256.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .r4 = bp) (hrcx : sB.gpr .r6 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .r4 = bp := (hs.pub .r4 (by decide)).trans hrsi
    have hs_rcx : s.gpr .r6 = scr := (hs.pub .r6 (by decide)).trans hrcx
    refine WP.mono (schedule_ok t s M bp scr hs_rsi hs_rcx
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha256.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha256.PPC64LE
