import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sha1.Spec
import VerifiedGarbage.Impl.Sha1.Arm
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha1.Arm.Lit

/-!
# SHA-1 compression function on ARMv7: the message schedule and the rounds
-/

namespace VG.Proof.Sha1.Arm

open VG VG.Arm VG.Impl.Sha1.Arm
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4]

/-- The pointers and the count: never written by the rounds. -/
def pubRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : BitVec 32) (j : Nat) : Addr := State.addr (scr + BitVec.ofNat 32 (slot j))

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .r4, work.getD ((1 + 5 - c) % 5) .r4,
      work.getD ((2 + 5 - c) % 5) .r4, work.getD ((3 + 5 - c) % 5) .r4,
      work.getD ((4 + 5 - c) % 5) .r4].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T1 ∧ r ≠ T2 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T1 ∧ r ≠ T2 := pubRegs_ne' r h

/-! ## One round -/

/-- `fₜ` as the code computes it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x ||| y) &&& z ||| x &&& y

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  split_ifs <;> simp only [fval, ch_eq, maj_eq, Spec.Sha1.parity]

theorem fcode_ok (g : Fn) (b c d : Reg) (s : State) (x y z : Word)
    (hbw : b ∈ work) (hcw : c ∈ work) (hdw : d ∈ work)
    (hb : s.gpr b = x) (hc : s.gpr c = y) (hd : s.gpr d = z) :
    WP isa (.block (fcode g b c d)) s fun s' =>
      s'.gpr T1 = fval g x y z ∧ (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨b1, -, -⟩ := work_ne hbw
  obtain ⟨c1, -, -⟩ := work_ne hcw
  obtain ⟨d1, -, -⟩ := work_ne hdw
  simp only [T1, T2] at b1 c1 d1 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp (config := {decide := true}) only [fcode, T1, T2, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, b1, c1, d1, hb, hc, hd,
    Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨rfl, fun r h1 h2 => by simp [h1, h2], ?_⟩ <;> trivial

theorem sum_ok (t : Nat) (a b e : Reg) (s : State) (x y z fv w : Word) (scr : BitVec 32)
    (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e)
    (ha : s.gpr a = x) (hb : s.gpr b = y) (he : s.gpr e = z) (hf : s.gpr T1 = fv)
    (hr3 : s.gpr .r3 = scr) (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) :
    WP isa (.block (sum t a b e)) s fun s' =>
      s'.gpr e = x.rotateRight 27 + fv + z + K t + w ∧
      s'.gpr b = y.rotateRight 2 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨b1, b2, -⟩ := work_ne hbw
  obtain ⟨e1, e2, -⟩ := work_ne hew
  have heb := hbe.symm
  have hs : slot t < 4096 := by simp only [slot]; omega
  simp only [slotAddr] at hin hw
  simp only [T1, T2] at b1 b2 e1 e2 hf ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [sum, T1, T2, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32,
    ite_true, ite_false, b1, b2, e1, e2, hbe, heb, ha, hb, he, hf, hr3, hin, hw, hs,
    movw_movt, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], trivial⟩

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by omega)
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by omega)
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by omega)

/-- The round is symbolically executed once per function `f`, for any
registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word) (scr : BitVec 32)
    (hv : Vars t s v) (hr3 : s.gpr .r3 = scr) (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, -, -, h04⟩, ⟨h12, h13, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  rw [Impl.Sha1.Arm.round, WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s _ _ _ m1 m2 m3 h1 h2 h3)
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s.gpr r := fun r hr =>
    hk₁ r (work_ne hr).1 (work_ne hr).2.1
  refine WP.mono (sum_ok t (var t 0) (var t 1) (var t 4) s₁ v[0] v[1] v[4] _ w scr m1 m4 h14
    (by rw [k₁ _ m0, h0]) (by rw [k₁ _ m1, h1]) (by rw [k₁ _ m4, h4]) hT1
    (by rw [hk₁ _ (by decide) (by decide), hr3]) (by rw [hrd₁, hwr₁]; exact hin)
    (by rw [hm₁, hw]))
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  refine ⟨?_, by rw [hm₂, hm₁], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], fun r hr => ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega),
      var_succ t _ (show 1 < 4 by omega), var_succ t _ (show 2 < 4 by omega),
      var_succ t _ (show 3 < 4 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, rotl5]; rfl
    · rw [hk₂ _ h04 h01 (work_ne m0).1 (work_ne m0).2.1, k₁ _ m0, h0]; rfl
    · rw [hb]; simp only [roundKW, rotl30]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).1 (work_ne m2).2.1, k₁ _ m2, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).1 (work_ne m3).2.1, k₁ _ m3, h3]; rfl
  · have hp := pubRegs_ne hr
    have hne : ∀ k, var t k ≠ r := fun k h => (work_ne (var_mem t k)).2.2 (h ▸ hr)
    rw [hk₂ r (Ne.symm (hne 4)) (Ne.symm (hne 1)) hp.1 hp.2, hk₁ r hp.1 hp.2]

/-! ## The message schedule -/

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32)
    (hr1 : s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : t < 16 → rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  have hs : ∀ j, slot j < 4096 := fun j => by simp only [slot]; omega
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    have ho : 4 * t < 4096 := by omega
    simp only [Impl.Sha1.Arm.schedule, ht, ite_true, T1, T2]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32,
      State.store32, hr1, hr3, hi, hout, ho, hs, ite_true, ite_false, hb, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, fun r h1 _ => ?_⟩
    simp [h1]
  · have hw := hwin (by omega)
    have e3 := hw (t - 3) (by omega) (by omega)
    have e8 := hw (t - 8) (by omega) (by omega)
    have e14 := hw (t - 14) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 3) = slot (t + 13) by simp only [slot]; omega] at e3
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha1.Arm.schedule, ht, ite_false, T1, T2]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      State.load32, State.store32, hr3, hin, hout, hs, ite_true, ite_false,
      e3, e8, e14, e16, Option.map_some, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    rw [rotl1] at hW
    refine ⟨by rw [hW], trivial, trivial, fun r h1 h2 => ?_⟩
    simp [h1, h2]

/-! ## The 80 rounds -/

/-- The scratch area the rounds write: the window. -/
abbrev winRegion (scr : BitVec 32) : Region := ⟨State.addr scr, 64⟩

theorem slotAddr_eq {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    slotAddr scr j = State.addr scr + BitVec.ofNat 64 (slot j) :=
  addr_add (by simp only [slot]; omega)

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem win_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    (winRegion scr).Contains (slotAddr scr j) 4 := by
  rw [slotAddr_eq h]; exact contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {i j : Nat}
    (hij : i % 16 ≠ j % 16) : Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  rw [slotAddr_eq h, slotAddr_eq h]
  simp only [slot]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hscr : scr.toNat + 112 ≤ 2 ^ 32)
    (hr1 : sB.gpr .r1 = bp) (hr3 : sB.gpr .r3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 →
      InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev (m.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
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
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1
      simp only [Vars, e] at hv ⊢
      exact hv
    have hr3₁ : s₁.gpr .r3 = scr := by
      rw [hr₁ .r3 (by decide) (by decide), hs_r3]
    have hself : s₁.mem.readW (slotAddr scr t) 32 = W M t := by
      rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
    refine WP.mono (round_ok t s₁ _ _ scr hv₁ hr3₁
      (by rw [hrd₁, hwr₁, hs.rd, hs.wr]; exact hin t) hself) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains hscr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep hscr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha1.Arm

/-!
# SHA-1 compression function on ARMv7: the whole function
-/

/-!
## SHA-1: the 32-bit ARM contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the 32-bit ARM implementations of the compression function and of
the streaming functions (`init`, `update`, `finalize`; see `VG.Spec.Sha1.Repr`),
in terms of `Spec/Sha1.lean`. The streaming contracts are those of x86-64 and
AArch64 (`Proof/Sha1/X86_64/Compress.lean`, `Proof/Sha1/AArch64/Compress.lean`),
with the arguments where AAPCS passes them.
-/

namespace VG.Proof.Sha1

open Spec.Sha1

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(20 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none of them may wrap around the end of
the (32-bit) address space. The pointers and `n` are public; the hash value
and the blocks are secret. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 20⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + 20 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 112 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      compressBlocks (stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

open VG.Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- 32-bit ARM contract for `vg_sha1_init(state: *mut [u8; 84])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (84 bytes), which may not wrap around the end of
the (32-bit) address space. The pointer is public. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    s.rd = [] ∧ s.wr = [state] ∧ (s.gpr .r0).toNat + 84 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_update(state: *mut [u8; 84], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `data`, `len` and
`scratch` are the stack arguments 0, 1 and 2. The code may read those
arguments (12 bytes at `sp`) and `data` (`len` bytes), and read and write
`state` (84 bytes) and `scratch` (160 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the data or
the arguments; the data may not overlap them either; and nothing may wrap
around the end of the (32-bit) address space. `sp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 84 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    Repr s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_finalize(state: *mut [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-1 digest of `m` to `out`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `out` and `scratch`
are the stack arguments 0 and 1. The code may read those arguments (8 bytes
at `sp`), and read and write `state` (84 bytes, whose contents on exit are
unspecified), `out` (20 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other or the arguments,
and nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the state is secret. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    let out : Region := ⟨State.addr (stackArg s 0), 20⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 84 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 20 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 20 = Spec.Sha1.hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha1


namespace VG.Proof.Sha1.Arm

open VG VG.Arm VG.Impl.Sha1.Arm
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev stR : Region := ⟨State.addr (st s₀), 20⟩
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
  st_fits : (st s₀).toNat + 20 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 5) :
    stAddr s₀ k = State.addr (st s₀) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.st_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t)) =
      State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega),
    addr_add (by omega)]

theorem in_state {k : Nat} (hk : k < 5) : InRegions (s₀.rd ++ s₀.wr) (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem out_state {k : Nat} (hk : k < 5) : InRegions s₀.wr (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega) (by simp only [slot]; omega)
    (slotAddr_eq h.scr_fits j)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega) (by simp only [slot]; omega)
    (slotAddr_eq h.scr_fits j)⟩

theorem in_save {d : Nat} (hd : d + 4 ≤ 112) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 112) : InRegions s₀.wr (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, Offset.add_ofNat_add_ofNat]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 5) (hk : k < 5) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 :=
  Offset.sep p (by omega) (by omega) (by omega)

/-- Reading word `j` of the hash value after writing word `k`. -/
theorem readW_writeW_word {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {j k : Nat} (hj : j < 5)
    (hk : k < 5) (h : j ≠ k) :
    (m.writeW (stAddr s₀ k) v).readW (stAddr s₀ j) 32 = m.readW (stAddr s₀ j) 32 := by
  rw [hp.stAddr_eq hj, hp.stAddr_eq hk]
  exact Mem.readW_writeW_sep (word_sep _ hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 5) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m (State.addr (st s₀)) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 5) :
    (stateAt m (State.addr (st s₀)))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (State.addr (scr s₀)) s₀.gpr saved

theorem saved_slots : Spill.Slots 64 100 saved := by decide

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
    .ldr .r8 .r0 (4 * 4)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .r12 .r0 (4 * 0), .dp .add .r4 .r4 (.reg .r12), .str .r4 .r0 (4 * 0),
    .ldr .r12 .r0 (4 * 1), .dp .add .r5 .r5 (.reg .r12), .str .r5 .r0 (4 * 1),
    .ldr .r12 .r0 (4 * 2), .dp .add .r6 .r6 (.reg .r12), .str .r6 .r0 (4 * 2),
    .ldr .r12 .r0 (4 * 3), .dp .add .r7 .r7 (.reg .r12), .str .r7 .r0 (4 * 3),
    .ldr .r12 .r0 (4 * 4), .dp .add .r8 .r8 (.reg .r12), .str .r8 .r0 (4 * 4),
    .dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] ∧
    s.gpr .r8 = v[4] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .r0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (State.addr (st s₀))) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32,
    hr0, h0, h1, h2, h3, h4, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 5 by decide), stateAt_get hp _ (show 1 < 5 by decide),
    stateAt_get hp _ (show 2 < 5 by decide), stateAt_get hp _ (show 3 < 5 by decide),
    stateAt_get hp _ (show 4 < 5 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Five words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  (((((m.writeW (stAddr s₀ 0) v[0]).writeW (stAddr s₀ 1) v[1]).writeW (stAddr s₀ 2) v[2]).writeW
    (stAddr s₀ 3) v[3]).writeW (stAddr s₀ 4) v[4])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) (State.addr (st s₀)) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ k, k < 5 → (stR s₀).Contains (stAddr s₀ k) (32 / 8) :=
    fun k hk => contains_sub (by omega) (by omega) (hp.stAddr_eq hk)
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr0 : s.gpr .r0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r1 = s.gpr .r1 + 64 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 5 → InRegions s.wr (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    State.load32, State.store32, subFlags, hr0,
    i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    readW_writeW_word hp,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · simp only [writeState, Vector.getElem_zipWith]
  all_goals trivial

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
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
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem win_sub (p : BitVec 32) : Region.Sub (winRegion p) ⟨State.addr p, 112⟩ :=
  Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
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
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
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
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
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
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hr2₃, hr2]

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (scr s₀)) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.z = (s₀.gpr .r2 - 0 == 0) :=
  Spill.save_slots_ok saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 100 ≤ 112) _) hp.scr_fits)
    (fun _ _ hd => hp.out_save (by omega)) (WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩)

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
    rw [(saveMem_frame s₀).readW (contains_sub (len := 20) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressArm.post s₀ s' := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := s₀.gpr) (by rw [hc.r3]; have := hp.scr_fits; omega)
    (fun _ _ hd => by rw [hc.rd, hc.wr, hc.r3]; exact hp.in_save (by omega)) (by rw [hc.r3]; exact hc.saved)
    fun s' hs _ hm _ _ _ => WP.block_nil ⟨Spill.restored_of hs (by decide), (congrArg (stateAt · _) hm).trans hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressArm.post s₀ s' := by
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
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified Arm.target Impl.Sha1.Arm.compress Proof.Sha1.compressArm := by
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
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.Arm
