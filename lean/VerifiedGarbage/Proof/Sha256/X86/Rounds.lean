import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.X86

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
  intro x hx hy
  rw [addr_eq (by omega)] at hx hy
  generalize scr.setWidth 64 = a at *
  bv_omega

/-- Reading `[scr + e]` after writing `[scr + d]`. -/
theorem readW_writeW_scr {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (m : Mem) (x : Word)
    {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr scr d) x).readW (addr scr e) 32 = m.readW (addr scr e) 32 :=
  Mem.readW_writeW_sep (scr_sep h hd he hde) (by decide)

theorem slot_lt (j : Nat) : slot j + 4 ≤ 64 := by simp only [slot]; omega

set_option maxHeartbeats 0 in
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word) (scr : BitVec 32)
    (hS : Scratch s scr) (hv : Vars t scr s.mem v) (hesi : s.gpr .esi = scr)
    (hw : s.mem.readW (addr scr (slot t)) 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) scr s'.mem (roundKW v (K t) w) ∧
      (∃ x y : Word, s'.mem = (s.mem.writeW (addr scr (var t 3)) x).writeW (addr scr (var t 7)) y) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have h1 : (t + 1) % 8 = (t % 8 + 1) % 8 := by omega
  have hc : t % 8 < 8 := Nat.mod_lt _ (by omega)
  have hin := hS.rd; have hout := hS.wr
  have hrw := readW_writeW_scr hS.fits
  have hs := hin (slot t) (by have := slot_lt t; omega)
  simp only [Vars, var, h1] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86.round, var, sc]
  generalize t % 8 = c at *
  interval_cases c <;>
  simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢ <;>
  simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, runStep_some, exec, execAlu,
    execShift, readSrc, ea_at,
    State.setReg, arithFlags, State.setFlags, State.load32, State.store32, ite_true, ite_false,
    hesi, hin, hout, hs, hrw, Mem.readW_writeW_self32, h0, h1, h2, h3, h4, h5, h6, h7, hw,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨_, _, rfl⟩, trivial, trivial, by simp [pubRegs]⟩ <;>
  simp (config := {failIfUnchanged := false}) only [roundKW, bsig1_eq, ch_eq, bsig0_eq, maj_eq,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] <;>
  simp (config := {failIfUnchanged := false}) only [BitVec.add_assoc]

set_option maxHeartbeats 0 in
theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32) (hS : Scratch s scr)
    (hedi : s.gpr .edi = bp) (hesi : s.gpr .esi = scr)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (addr bp (4 * t)) 4)
    (hblk : t < 16 → bswap (s.mem.readW (addr bp (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (addr scr (slot j)) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (addr scr (slot t)) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hin : ∀ j, InRegions (s.rd ++ s.wr) (addr scr (slot j)) 4 :=
    fun j => hS.rd _ (by have := slot_lt j; omega)
  have hout : ∀ j, InRegions s.wr (addr scr (slot j)) 4 :=
    fun j => hS.wr _ (by have := slot_lt j; omega)
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha256.X86.schedule, ht, ite_true]
    simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, runStep_some, exec, readSrc,
      ea_at, State.setReg,
      State.load32, State.store32, hedi, hesi, hi, hout, ite_true, ite_false, hb,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, by simp [pubRegs]⟩
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
    simp (config := {decide := true}) only [runBlock_cons, runBlock_nil, runStep_some, exec, execAlu,
    execShift, readSrc, ea_at,
      State.setReg, arithFlags, State.setFlags, State.load32, State.store32, hesi, hin, hout,
      ite_true, ite_false, e2, e7, e15, e16, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, trivial, trivial, by simp [pubRegs]⟩
    rw [W_ge M (t := t) (by omega), ssig1_eq, ssig0_eq]

/-! ## The 64 rounds -/

/-- The part of the scratch buffer the rounds write: the window and the working variables. -/
abbrev workRegion (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 96⟩

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

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
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_edi : s.gpr .edi = bp := (hs.pub .edi (by decide)).trans hedi
    have hs_esi : s.gpr .esi = scr := (hs.pub .esi (by decide)).trans hesi
    refine WP.mono (schedule_ok t s M bp scr (hS.congr hs.rd hs.wr) hs_edi hs_esi
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
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
      hv₁ hesi₁ hself) fun s₂ ⟨hv₂, ⟨x, y, hm₂⟩, hrd₂, hwr₂, hr₂⟩ => ?_
    have h3 := var_lt t 3
    have h7 := var_lt t 7
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha256.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha256.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
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
