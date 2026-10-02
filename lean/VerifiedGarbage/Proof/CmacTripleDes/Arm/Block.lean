import VerifiedGarbage.Proof.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# TDEA on 32-bit ARM: the passes and the block

Untrusted: everything here is checked by Lean.

As on AArch64 (`Proof/CmacTripleDes/AArch64/Block.lean`): `block` encrypts
the 64-bit block in `r0:r1` with the key schedule at `r9` (`block_ok`): `IP`
into `r7` and `r8`, three passes of sixteen rounds (`pass_ok`, the round
keys `lr` bytes apart, the halves exchanged after each pass), and `IP⁻¹`.
During the block, `r9` points to slot `kpos p j` of the key schedule before
round `j` of pass `p`. The block uses every register but `r10`.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `r9` readable, and the words
0–12 of the scratch buffer at `r10` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ len, (⟨State.addr (s.gpr .r9), len⟩ : Region) ∈ s.rd ++ s.wr ∧ 384 ≤ len ∧
    (s.gpr .r9).toNat + len ≤ 2 ^ 32
  scr : ∃ len, (⟨State.addr (s.gpr .r10), len⟩ : Region) ∈ s.wr ∧ 52 ≤ len ∧
    (s.gpr .r10).toNat + len ≤ 2 ^ 32
  disj : Region.Disjoint ⟨State.addr (s.gpr .r10), 52⟩ ⟨State.addr (s.gpr .r9), 384⟩

/-- The block's words of the scratch buffer. -/
abbrev xR (s₀ : State) : Region := ⟨State.addr (s₀.gpr .r10), 52⟩

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = s₀.gpr .r10
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (State.addr (s₀.gpr .r9))

theorem ok_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * n)) : Ok rCfg s := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, ?_, fun k hk' j hj => ?_⟩
  · simp only [rCfg] at hk'
    rw [h.wr, show rCfg.base = .r10 from rfl, h.r10]
    exact in_off hX hXw (by omega) (by omega)
  · simp only [rCfg] at hk'
    rw [h.rd, h.wr, show rCfg.ext = .r9 from rfl, hk, wordAddr, add_ofNat_ofNat]
    exact in_off hR hRw (by omega) (by omega)
  · show (s.gpr .r10).toNat + 4 * 13 ≤ 2 ^ 32
    rw [h.r10]; omega
  · simp only [rCfg] at hk' hj
    rw [show rCfg.base = .r10 from rfl, show rCfg.ext = .r9 from rfl, h.r10, hk, wordAddr, wordAddr,
      add_ofNat_ofNat]
    exact hp.disj.sep (contains_off (len := 52) (by omega) (by omega) (by omega))
      (contains_off (len := 384) (by omega) (by omega) (by omega))

theorem key_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * n)) : key48 s = ((sch s₀).getD n 0).setWidth 48 := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  have hW := (s₀.gpr .r9).isLt
  rw [scheduleAt_getD _ _ hn, setWidth48_readW]
  have rd : ∀ d, d + 4 ≤ 384 → s.mem.readW (State.addr (s₀.gpr .r9 + BitVec.ofNat 32 d)) 32 =
      s₀.mem.readW (State.addr (s₀.gpr .r9 + BitVec.ofNat 32 d)) 32 := fun d hd =>
    h.frame.readW (r := ⟨State.addr (s₀.gpr .r9 + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine (hp.disj.symm.sub_left ?_)
        rw [addr_add (by omega)]
        exact Offset.sub_base _ (by omega)) (by decide)
  have e0 : wordAddr (s.gpr .r9) 0 = State.addr (s₀.gpr .r9 + BitVec.ofNat 32 (8 * n)) := by
    rw [wordAddr, hk, add_ofNat_ofNat, show 8 * n + 4 * 0 = 8 * n by omega]
  have e1 : wordAddr (s.gpr .r9) 1 = State.addr (s₀.gpr .r9 + BitVec.ofNat 32 (8 * n + 4)) := by
    rw [wordAddr, hk, add_ofNat_ofNat]
  rw [key48, keyLo, keyHi, e0, e1, rd _ (by omega), rd _ (by omega), addr_add (by omega), addr_add (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The rounds of a pass -/

theorem roundTail_ok (s : State) :
    ∃ s', runBlock isa roundTail s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 + s.gpr .lr ∧ s'.gpr .r11 = s.gpr .r11 - 1 ∧ s'.z = (s.gpr .r11 - 1 == 0) ∧
      (∀ r, r ≠ .r9 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [roundTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      Op2.eval, Option.map_some, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags, h₁, h₂]

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 32 := if p % 2 = 1 then BitVec.ofNat 32 (2 ^ 32 - 8) else BitVec.ofNat 32 8

theorem kpos_succ_addr (a : BitVec 32) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 32 (8 * kpos p j) + stride p = a + BitVec.ofNat 32 (8 * kpos p (j + 1)) := by
  rw [BitVec.add_assoc, stride, kpos, kpos]
  congr 1
  split
  · rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [← BitVec.ofNat_add]
    congr 1

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : Same s₀ s
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * kpos p j)
  str : s.gpr .lr = stride p
  r12 : s.gpr .r12 = BitVec.ofNat 32 (3 - p)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (16 - j)
  halves : (s.gpr .r7, s.gpr .r8) = rounds (passKeys (sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (sch s₀) p j = ((sch s₀).getD (kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : PInv s₀ p lr j s) :
    WP isa (.block (round ++ roundTail)) s fun s' => s'.z = decide (j + 1 = 16) ∧ PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, e7, e8, rd₁, wr₁, sp₁, k₁, f₁⟩ := round_ok (ok_at hp h.same (kpos_lt hp3 hj) h.r9)
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ?_⟩
  obtain ⟨s₂, h₂, t9, t11, tz, tk, tsp, tm, trd, twr⟩ := roundTail_ok s₁
  have kk : ∀ r ∈ kept, s₁.gpr r = s.gpr r := k₁
  refine ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tz, kk .r11 (by simp [kept]), h.r11, ofNat_sub_one (by omega) (by omega), ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r10 (by decide) (by decide), kk .r10 (by simp [kept]), h.same.r10]
  · rw [tsp, sp₁, h.same.sp]
  · rw [trd, rd₁, h.same.rd]
  · rw [twr, wr₁, h.same.wr]
  · rw [tm]
    have hr : slotRegion rCfg s = xR s₀ := by
      simp only [slotRegion, xR]; rw [show rCfg.base = .r10 from rfl, h.same.r10]; rfl
    rw [hr] at f₁
    exact h.same.frame.trans f₁
  · rw [t9, kk .r9 (by simp [kept]), kk .lr (by simp [kept]), h.r9, h.str, kpos_succ_addr _ hp3 hj]
  · rw [tk .lr (by decide) (by decide), kk .lr (by simp [kept]), h.str]
  · rw [tk .r12 (by decide) (by decide), kk .r12 (by simp [kept]), h.r12]
  · rw [t11, kk .r11 (by simp [kept]), h.r11, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [rounds_succ, ← h.halves, tk .r7 (by decide) (by decide), tk .r8 (by decide) (by decide), e7, e8,
      key_at hp h.same (kpos_lt hp3 hj) h.r9, passKeys_at s₀ hj]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (h9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * kpos p 0))
    (hlr : s.gpr .lr = stride p) (h12 : s.gpr .r12 = BitVec.ofNat 32 (3 - p))
    (hh : (s.gpr .r7, s.gpr .r8) = lr) :
    WP isa pass s (PInv s₀ p lr 16) := by
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      Option.map_some, ite_true]
    rfl, ?_⟩)
  have g : ∀ r, r ≠ .r11 → (s.setReg .r11 16).gpr r = s.gpr r := fun r hr => gpr_setReg_of_ne _ _ hr
  have hI : PInv s₀ p lr 0 (s.setReg .r11 16) :=
    ⟨⟨by rw [g _ (by decide), h.r10], h.sp, h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h9],
      by rw [g _ (by decide), hlr], by rw [g _ (by decide), h12], by rw [gpr_setReg_self]; rfl,
      by rw [g _ (by decide), g _ (by decide), hh]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .ne) (Q := PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (roundStep_ok hp hp3 hj ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp [hz], 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

theorem passTail_ok (s : State) :
    ∃ s', runBlock isa passTail s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 + (128 - s.gpr .lr) ∧ s'.gpr .lr = 0 - s.gpr .lr ∧
      s'.gpr .r7 = s.gpr .r8 ∧ s'.gpr .r8 = s.gpr .r7 ∧ s'.gpr .r12 = s.gpr .r12 - 1 ∧
      s'.z = (s.gpr .r12 - 1 == 0) ∧
      (∀ r, r ∉ [Reg.r0, .r7, .r8, .r9, .r12, .lr] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [passTail, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Op2.eval, Option.map_some, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, subFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * kpos p 0)
  str : s.gpr .lr = stride p
  r12 : s.gpr .r12 = BitVec.ofNat 32 (3 - p)
  halves : (s.gpr .r7, s.gpr .r8) = passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : BitVec 32) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 32 (8 * kpos p 16) + (128 - stride p) = a + BitVec.ofNat 32 (8 * kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - stride p = stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' => s'.z = decide (p + 1 = 3) ∧ OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (pass_ok hp hp3 h.same h.r9 h.str h.r12 h.halves) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t9, tlr, t7, t8, t12, tz, tk, tsp, tm, trd, twr⟩ := passTail_ok s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [tz, h₁.r12, ofNat_sub_one (by omega) (by omega), ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r10 (by decide), h₁.same.r10]
  · rw [tsp, h₁.same.sp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [t9, h₁.r9, h₁.str, kpos_tail_addr _ hp3]
  · rw [tlr, h₁.str, stride_succ hp3]
  · rw [t12, h₁.r12, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [t7, t8, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {s : State} (h : OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (passBody_ok hp hp3 ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp [hz], 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- Bit `b` of a block `hi ‖ lo`, as an atom: of `hi` (input word 0) or `lo`
(input word 1). -/
def xAtom (b : Nat) : Nat := if 32 ≤ b then b - 32 else 32 + b

/-- `IP`'s high half into `r7`, its low half into `r8`. -/
def ipG7 (t : Nat) : List Nat := if t < 32 then [xAtom (ipSrc (32 + t))] else []
def ipG8 (t : Nat) : List Nat := if t < 32 then [xAtom (ipSrc t)] else []

/-- No memory. -/
def zCfg : Cfg := { base := .r10, slots := 0, ext := .r9, exts := 0 }

theorem zCfg_ok (s : State) : Ok zCfg s :=
  ⟨fun k hk => absurd hk (by simp [zCfg]), fun k hk => absurd hk (by simp [zCfg]),
    by have := (s.gpr zCfg.base).isLt; simp only [zCfg] at this ⊢; omega, fun k hk => absurd hk (by simp [zCfg])⟩

theorem frame_zCfg {s : State} {m m' : Mem} (h : Frame [slotRegion zCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, zCfg, Region.Contains]

theorem ip_check :
    check (lanes 32 6) zCfg (linExt 2) ipCode (linEnv [(.r0, 0), (.r1, 1)])
      (linPost 6 [(.r7, ipG7), (.r8, ipG8)]) = true := by
  decide +kernel

/-- `IP⁻¹(R ‖ L)` into `r0` (high word) and `r1` (low word), from `R` in `r7`
(input word 0) and `L` in `r8` (input word 1). -/
def fpG0 (t : Nat) : List Nat := if t < 32 then [xAtom (fpSrc (32 + t))] else []
def fpG1 (t : Nat) : List Nat := if t < 32 then [xAtom (fpSrc t)] else []

theorem fp_check :
    check (lanes 32 6) zCfg (linExt 2) fpCode (linEnv [(.r7, 0), (.r8, 1)])
      (linPost 6 [(.r0, fpG0), (.r1, fpG1)]) = true := by
  decide +kernel

theorem ip_kept : [Reg.r9, .r10].all (fun r => ipCode.all fun i => dstOf i != some r) = true := by decide +kernel

theorem fp_kept : [Reg.r9, .r10].all (fun r => fpCode.all fun i => dstOf i != some r) = true := by decide +kernel

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by decide

/-- A bit of `hi ‖ lo`. -/
theorem bit_xAtom (W : Nat → BitVec 32) {b : Nat} (hb : b < 64) :
    bitOf W (xAtom b) = (W 0 ++ W 1).getLsbD b := by
  rw [BitVec.getLsbD_append, xAtom]
  by_cases h : 32 ≤ b
  · rw [ite_eq_left h, ite_eq_right (by omega), bitOf, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, ite_eq_left (by omega), bitOf, show (32 + b) / 32 = 1 by omega,
      show (32 + b) % 32 = b by omega]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      (s'.gpr .r7, s'.gpr .r8) = split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r0 ++ s.gpr .r1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧
      s'.mem = s.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r0 else s.gpr .r1
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok ip_check (zCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [zCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, hoth _ (List.all_eq_true.mp ip_kept _ (by simp)),
    hoth _ (List.all_eq_true.mp ip_kept _ (by simp)), frame_zCfg hfr⟩
  have hx : W 0 ++ W 1 = s.gpr .r0 ++ s.gpr .r1 := rfl
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · rw [hout .r7 ipG7 (by simp) t ht, ipG7, ite_eq_left ht, xorBits_cons, xorBits_nil, Bool.xor_false,
      bit_xAtom W (ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      BitVec.getLsbD_ushiftRight, getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega)]
    rfl
  · rw [hout .r8 ipG8 (by simp) t ht, ipG8, ite_eq_left ht, xorBits_cons, xorBits_nil, Bool.xor_false,
      bit_xAtom W (ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      getLsbD_permute _ _ (by decide) (show t < 64 by omega)]
    rfl

theorem fp_ok (s : State) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .r0 ++ s'.gpr .r1 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r7 ++ s.gpr .r8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧
      s'.mem = s.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r7 else s.gpr .r8
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok fp_check (zCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [zCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, hoth _ (List.all_eq_true.mp fp_kept _ (by simp)),
    hoth _ (List.all_eq_true.mp fp_kept _ (by simp)), frame_zCfg hfr⟩
  have hx : W 0 ++ W 1 = s.gpr .r7 ++ s.gpr .r8 := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_append, getLsbD_permute _ _ (by decide) hj,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl]
  by_cases h32 : j < 32
  · rw [ite_eq_left h32, hout .r1 fpG1 (by simp) j h32, fpG1, ite_eq_left h32, xorBits_cons, xorBits_nil,
      Bool.xor_false, bit_xAtom W (fpSrc_lt _ hj), hx]
  · rw [ite_eq_right h32, hout .r0 fpG0 (by simp) (j - 32) (by omega), fpG0, ite_eq_left (by omega),
      xorBits_cons, xorBits_nil, Bool.xor_false, show 32 + (j - 32) = j by omega, bit_xAtom W (fpSrc_lt _ hj), hx]

/-- TDEA encryption of the block in `r0:r1` (its high and low words) with the
key schedule at `r9`, into `r0:r1`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      Same s₀ s ∧ s.gpr .r9 = s₀.gpr .r9 ∧
        s.gpr .r0 ++ s.gpr .r1 = tdes (sch s₀) (s₀.gpr .r0 ++ s₀.gpr .r1) := by
  obtain ⟨s₁, h₁, hal₁, rd₁, wr₁, sp₁, r9₁, r10₁, m₁⟩ := ip_ok s₀
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      Option.map_some, ite_true]
    rfl, ?_⟩⟩
  have g : ∀ r, r ≠ .r12 → r ≠ .lr → ((s₁.setReg .r12 3).setReg .lr 8).gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h1]
  have hO : OInv s₀ (s₀.gpr .r0 ++ s₀.gpr .r1) 0 ((s₁.setReg .r12 3).setReg .lr 8) :=
    ⟨⟨by rw [g _ (by decide) (by decide), r10₁], sp₁, rd₁, wr₁,
      by show Frame [xR s₀] s₀.mem s₁.mem; rw [m₁]; exact Frame.refl _ _⟩,
      by rw [g _ (by decide) (by decide), r9₁]; simp [kpos],
      by rw [gpr_setReg_self]; rfl,
      by rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_self]; rfl,
      by rw [g _ (by decide) (by decide), g _ (by decide) (by decide), hal₁]; rfl⟩
  refine WP.seq (WP.mono (passes_ok hp hO) fun s₃ h₃ => ?_)
  rw [WP.block_append_iff]
  let s₄ := s₃.setReg .r9 (s₃.gpr .r9 - 504)
  have h₄ : runBlock isa [.dp .sub .r9 .r9 (.imm 504)] s₃ = some s₄ := by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      Option.map_some, ite_true]
    rfl
  obtain ⟨s₅, h₅, ax₅, rd₅, wr₅, sp₅, r9₅, r10₅, m₅⟩ := fp_ok s₄
  have g₄ : ∀ r, r ≠ .r9 → s₄.gpr r = s₃.gpr r := fun r hr => gpr_setReg_of_ne _ _ hr
  refine WP.of_runBlock ⟨s₄, h₄, WP.of_runBlock ⟨s₅, h₅, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [r10₅, g₄ _ (by decide), h₃.same.r10]
  · rw [sp₅]; exact h₃.same.sp
  · rw [rd₅]; exact h₃.same.rd
  · rw [wr₅]; exact h₃.same.wr
  · rw [m₅]; exact h₃.same.frame
  · rw [r9₅, gpr_setReg_self, h₃.r9, show 8 * kpos 3 0 = 504 from rfl,
      show (504 : BitVec 32) = BitVec.ofNat 32 504 from rfl, BitVec.add_sub_cancel]
  · rw [ax₅, g₄ _ (by decide), g₄ _ (by decide), tdes_eq, ← h₃.halves]

end VG.Proof.CmacTripleDes.Arm
