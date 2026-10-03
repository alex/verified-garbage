import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# TDEA on AArch64: the passes and the block

As on x86-64 (`Proof/CmacTripleDes/X86_64/Block.lean`): `block` encrypts the
64-bit block in `x5` with the key schedule at `x14` (`block_ok`): `IP` into
`x12` and `x13`, three passes of sixteen rounds (`pass_ok`, the round keys
`x0` bytes apart, the halves exchanged after each pass), and `IP⁻¹`. During
the block, `x14` points to slot `kpos p j` of the key schedule before round
`j` of pass `p`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes

theorem ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  have : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this
    · intro he; rw [he]; rfl
  rw [bne, this]

theorem eval_nonzero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x r) s = some !decide (x = 0) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

theorem eval_zero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.zero .x r) s = some (decide (x = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all

/-- What the block needs: the key schedule at `x14` readable, and the slots
0–5 of the scratch buffer at `x15` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .x14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .x15 ∧ 48 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .x15, 48⟩ ⟨s.gpr .x14, 384⟩

/-- The slots of the broadcast inputs. -/
abbrev xR (s₀ : State) : Region := ⟨s₀.gpr .x15, 48⟩

/-- The registers of the functions that the block keeps (with `x15`). -/
def outer : List Reg := [.x1, .x2, .x3, .x4]

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  x15 : s.gpr .x15 = s₀.gpr .x15
  keep : ∀ r ∈ outer, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

theorem Same.refl (s : State) : Same s s := ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x14)

theorem wordAddr_zero (a : Addr) : wordAddr a 0 = a := by simp [wordAddr]

theorem ok_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .x14 = s₀.gpr .x14 + BitVec.ofNat 64 (8 * n)) : Ok rCfg s := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, by decide, fun k hk' j hj => ?_⟩
  · rw [h.wr]
    exact ⟨X, hX, contains_word (off := 0) (by show s.gpr .x15 = _; rw [h.x15, ← hXb]; simp)
      (by simp only [rCfg] at hk'; omega) hXl hXw⟩
  · simp only [rCfg] at hk'
    obtain rfl : k = 0 := by omega
    rw [h.rd, h.wr]
    exact ⟨R, hR, contains_word (off := 8 * n) (by show s.gpr .x14 = _; rw [hk, hRb]) (by omega) hRl hRw⟩
  · simp only [rCfg] at hk' hj
    obtain rfl : j = 0 := by omega
    rw [show rCfg.base = .x15 from rfl, show rCfg.ext = .x14 from rfl, h.x15, hk, wordAddr_zero]
    exact hp.disj.sep (slot_contains _ hk' (by decide)) (Offset.contains_base _ (by omega) (by omega))

theorem key_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .x14 = s₀.gpr .x14 + BitVec.ofNat 64 (8 * n)) : keyW s = (sch s₀).getD n 0 := by
  rw [scheduleAt_getD _ _ hn, keyW, wordAddr_zero, hk]
  refine h.frame.readW (r := ⟨s₀.gpr .x14 + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.disj.sub_right (Offset.sub_base _ (by omega))).symm

/-! ## The rounds of a pass -/

theorem roundTail_ok (s : State) :
    ∃ s', runBlock isa roundTail s = some s' ∧
      s'.gpr .x14 = s.gpr .x14 + s.gpr .x0 ∧ s'.gpr .x16 = s.gpr .x16 - 1 ∧
      (∀ r, r ≠ .x14 → r ≠ .x16 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [roundTail, runBlock_cons, exec_add, runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, State.read]
  · simp [gpr_write, h₁, h₂]

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 64 := if p % 2 = 1 then BitVec.ofNat 64 (2 ^ 64 - 8) else BitVec.ofNat 64 8

theorem kpos_succ_addr (a : Addr) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 64 (8 * kpos p j) + stride p = a + BitVec.ofNat 64 (8 * kpos p (j + 1)) := by
  rw [BitVec.add_assoc, stride, kpos, kpos]
  congr 1
  split
  · rename_i hodd
    rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [← BitVec.ofNat_add]
    congr 1

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14 + BitVec.ofNat 64 (8 * kpos p j)
  x0 : s.gpr .x0 = stride p
  x17 : s.gpr .x17 = BitVec.ofNat 64 (3 - p)
  x16 : s.gpr .x16 = BitVec.ofNat 64 (16 - j)
  halves : ((s.gpr .x12).setWidth 32, (s.gpr .x13).setWidth 32) = rounds (passKeys (sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (sch s₀) p j = ((sch s₀).getD (kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

theorem outer_kept {r : Reg} (h : r ∈ outer) : r ∈ kept := by
  simp only [outer, kept, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem outer_ne {r : Reg} (h : r ∈ outer) :
    r ≠ .x0 ∧ r ≠ .x5 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
  simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : PInv s₀ p lr j s) :
    WP isa (.block (round ++ roundTail)) s (PInv s₀ p lr (j + 1)) := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, e12, e13, rd₁, wr₁, sp₁, k₁, f₁⟩ := round_ok (ok_at hp h.same (kpos_lt hp3 hj) h.x14)
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ?_⟩
  obtain ⟨s₂, h₂, t14, t16, tk, tsp, tm, trd, twr⟩ := roundTail_ok s₁
  have kk : ∀ r ∈ kept, s₁.gpr r = s.gpr r := k₁
  refine ⟨s₂, h₂, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tk .x15 (by decide) (by decide), kk .x15 (by simp [kept]), h.same.x15]
  · obtain ⟨-, -, -, -, h14, -, h16, -⟩ := outer_ne hr
    rw [tk r h14 h16, kk r (outer_kept hr), h.same.keep r hr]
  · rw [tsp, sp₁, h.same.sp]
  · rw [trd, rd₁, h.same.rd]
  · rw [twr, wr₁, h.same.wr]
  · rw [tm]
    have hr : slotRegion rCfg s = xR s₀ := by
      simp only [slotRegion, xR]; rw [show rCfg.base = .x15 from rfl, h.same.x15]; rfl
    rw [hr] at f₁
    exact h.same.frame.trans f₁
  · rw [t14, kk .x14 (by simp [kept]), kk .x0 (by simp [kept]), h.x14, h.x0, kpos_succ_addr _ hp3 hj]
  · rw [tk .x0 (by decide) (by decide), kk .x0 (by simp [kept]), h.x0]
  · rw [tk .x17 (by decide) (by decide), kk .x17 (by simp [kept]), h.x17]
  · rw [t16, kk .x16 (by simp [kept]), h.x16, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [rounds_succ, ← h.halves, tk .x12 (by decide) (by decide), tk .x13 (by decide) (by decide), e12, e13,
      key_at hp h.same (kpos_lt hp3 hj) h.x14, passKeys_at s₀ hj]

theorem exec_sub' {s : State} {d n m : Reg} :
    exec (.sub .x d n m) s = some (s.write .x d (s.gpr n - s.gpr m)) := by
  simp [exec, State.read]

theorem exec_movz_x {s : State} {d : Reg} {imm : BitVec 16} {hw : Nat} (h : hw < 4) :
    exec (.movz .x d imm hw) s = some (s.write .x d (imm.setWidth 64 <<< (16 * hw))) := by
  simp only [exec, Size.bits, show 16 * hw < 64 by omega, ite_true]

theorem exec_mov {s : State} {d n : Reg} : exec (mov d n) s = some (s.write .x d (s.gpr n)) := by
  rw [mov, exec_addImm_x (by decide)]
  simp [State.read]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (h14 : s.gpr .x14 = s₀.gpr .x14 + BitVec.ofNat 64 (8 * kpos p 0))
    (h0 : s.gpr .x0 = stride p) (h17 : s.gpr .x17 = BitVec.ofNat 64 (3 - p))
    (hlr : ((s.gpr .x12).setWidth 32, (s.gpr .x13).setWidth 32) = lr) :
    WP isa pass s (PInv s₀ p lr 16) := by
  refine WP.seq (WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have g : ∀ r, r ≠ .x16 → (s.write .x .x16 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))).gpr r = s.gpr r :=
    fun r hr => gpr_write_of_ne _ _ _ hr
  have hI : PInv s₀ p lr 0 (s.write .x .x16 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))) :=
    ⟨⟨by rw [g _ (by decide), h.x15], fun r hr => by rw [g _ (outer_ne hr).2.2.2.2.2.2.1, h.keep r hr],
      h.sp, h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], by rw [g _ (by decide), h0],
      by rw [g _ (by decide), h17], by rw [gpr_write_self]; decide,
      by rw [g _ (by decide), g _ (by decide), hlr]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .nonzero .x .x16) (Q := PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (roundStep_ok hp hp3 hj ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x16) (x := 16 - (j + 1)) (by omega) h'.x16
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

theorem passTail_ok (s : State) :
    ∃ s', runBlock isa passTail s = some s' ∧
      s'.gpr .x14 = s.gpr .x14 + (BitVec.ofNat 64 128 - s.gpr .x0) ∧ s'.gpr .x0 = 0 - s.gpr .x0 ∧
      s'.gpr .x12 = s.gpr .x13 ∧ s'.gpr .x13 = s.gpr .x12 ∧ s'.gpr .x17 = s.gpr .x17 - 1 ∧
      (∀ r, r ∉ [Reg.x0, .x5, .x12, .x13, .x14, .x17] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [passTail, runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_cons, exec_sub', runStep_some,
      runBlock_cons, exec_add, runStep_some, runBlock_cons, exec_movz_x (by decide), runStep_some,
      runBlock_cons, exec_sub', runStep_some, runBlock_cons, exec_mov, runStep_some,
      runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, State.read]
  · simp [gpr_write]
  · simp [gpr_write]
  · simp [gpr_write, State.read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  x14 : s.gpr .x14 = s₀.gpr .x14 + BitVec.ofNat 64 (8 * kpos p 0)
  x0 : s.gpr .x0 = stride p
  x17 : s.gpr .x17 = BitVec.ofNat 64 (3 - p)
  halves : ((s.gpr .x12).setWidth 32, (s.gpr .x13).setWidth 32) =
    passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : Addr) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 64 (8 * kpos p 16) + (BitVec.ofNat 64 128 - stride p) =
      a + BitVec.ofNat 64 (8 * kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - stride p = stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem outer_notMem {r : Reg} (h : r ∈ outer) : r ∉ [Reg.x0, .x5, .x12, .x13, .x14, .x17] := by
  simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s (OInv s₀ x (p + 1)) := by
  refine WP.seq (WP.mono (pass_ok hp hp3 h.same h.x14 h.x0 h.x17 h.halves) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t14, t0, t12, t13, t17, tk, tsp, tm, trd, twr⟩ := passTail_ok s₁
  refine WP.of_runBlock ⟨s₂, h₂, ⟨⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [tk .x15 (by decide), h₁.same.x15]
  · rw [tk r (outer_notMem hr), h₁.same.keep r hr]
  · rw [tsp, h₁.same.sp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [t14, h₁.x14, h₁.x0, kpos_tail_addr _ hp3]
  · rw [t0, h₁.x0, stride_succ hp3]
  · rw [t17, h₁.x17, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [t12, t13, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {s : State} (h : OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) (.nonzero .x .x17)) s (OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .nonzero .x .x17) (Q := OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (passBody_ok hp hp3 ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x17) (x := 3 - (p + 1)) (by omega) h'.x17
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- `IP`'s high half into `x12`, its low half into `x13`, from `x5` (input word 0). -/
def ipG12 (t : Nat) : List Nat := if t < 32 then [ipSrc (32 + t)] else []
def ipG13 (t : Nat) : List Nat := if t < 32 then [ipSrc t] else []

theorem ip_check :
    check (lanes 64 6) oCfg (linExt 1) ipCode (linEnv [(.x5, 0)])
      (linPost 6 [(.x12, ipG12), (.x13, ipG13)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `x5`, from `R` in `x12` (input word 0) and `L` in `x13` (input word 1). -/
def fpG (j : Nat) : List Nat := if 32 ≤ fpSrc j then [fpSrc j - 32] else [64 + fpSrc j]

theorem fp_check :
    check (lanes 64 7) oCfg (linExt 2) fpCode (linEnv [(.x12, 0), (.x13, 1)]) (linPost 7 [(.x5, fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.x1, .x2, .x3, .x4, .x14, .x15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

theorem frame_oCfg {s : State} {m m' : Mem} (h : Frame [slotRegion oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      ((s'.gpr .x12).setWidth 32, (s'.gpr .x13).setWidth 32) =
        split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x5)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok ip_check (oCfg_ok s) (fun _ => s.gpr .x5)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp ip_kept r hr), frame_oCfg hfr⟩
  have h12 := hout .x12 ipG12 (by simp)
  have h13 := hout .x13 ipG13 (by simp)
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · have hs := ipSrc_lt (32 + t) (by omega)
    rw [BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, h12 t (by omega), ipG12, ite_eq_left ht,
      BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, BitVec.getLsbD_ushiftRight,
      Spec.TripleDes.permute, ← Spec.TripleDes.permute,
      getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs]
    rfl
  · have hs := ipSrc_lt t (by omega)
    rw [BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, h13 t (by omega), ipG13, ite_eq_left ht,
      BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      getLsbD_permute _ _ (by decide) (show t < 64 by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs]
    rfl

theorem fp_ok (s : State) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .x5 = Spec.TripleDes.permute Spec.TripleDes.fp ((s.gpr .x12).setWidth 32 ++ (s.gpr .x13).setWidth 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .x12 else s.gpr .x13
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok fp_check (oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, fun r hr => hoth r (List.all_eq_true.mp fp_kept r hr), frame_oCfg hfr⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := fpSrc_lt j hj
  rw [hout .x5 fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl, fpG]
  by_cases h32 : 32 ≤ fpSrc j
  · rw [ite_eq_left h32, ite_eq_right (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      Nat.div_eq_of_lt (show fpSrc j - 32 < 64 by omega), Nat.mod_eq_of_lt (show fpSrc j - 32 < 64 by omega),
      BitVec.getLsbD_setWidth, show fpSrc j - 32 < 32 by omega, decide_true, Bool.true_and]
    rfl
  · rw [ite_eq_right h32, ite_eq_left (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      show (64 + fpSrc j) / 64 = 1 by omega, show (64 + fpSrc j) % 64 = fpSrc j by omega,
      BitVec.getLsbD_setWidth, show fpSrc j < 32 by omega, decide_true, Bool.true_and]
    rfl

theorem blockKept_ne {r : Reg} (h : r ∈ outer) : r ∈ blockKept := by
  simp only [outer, blockKept, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp

/-- TDEA encryption of the block in `x5` (as a 64-bit integer) with the key
schedule at `x14`, into `x5`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      Same s₀ s ∧ s.gpr .x14 = s₀.gpr .x14 ∧ s.gpr .x5 = tdes (sch s₀) (s₀.gpr .x5) := by
  obtain ⟨s₁, h₁, hal₁, rd₁, wr₁, sp₁, k₁, m₁⟩ := ip_ok s₀
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_movz_x (by decide), runStep_some, runBlock_cons, exec_movz_x (by decide),
      runStep_some, runBlock_nil], ?_⟩⟩
  let s₂ := (s₁.write .x .x17 ((3 : BitVec 16).setWidth 64 <<< (16 * 0))).write .x .x0
    ((8 : BitVec 16).setWidth 64 <<< (16 * 0))
  have g : ∀ r, r ≠ .x17 → r ≠ .x0 → s₂.gpr r = s₁.gpr r := fun r h1 h2 => by
    simp only [s₂, gpr_write, h1, h2, ite_false]
  have hO : OInv s₀ (s₀.gpr .x5) 0 s₂ :=
    ⟨⟨by rw [g _ (by decide) (by decide), k₁ _ (by decide)],
      fun r hr => by
        rw [g _ (outer_ne hr).2.2.2.2.2.2.2 (outer_ne hr).1, k₁ _ (blockKept_ne hr)],
      by rw [← sp₁]; rfl, rd₁, wr₁,
      by show Frame [xR s₀] s₀.mem s₁.mem; rw [m₁]; exact Frame.refl _ _⟩,
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)]; simp [kpos],
      by simp only [s₂, gpr_write_self]; decide,
      by simp only [s₂, gpr_write, ite_true]; decide,
      by rw [g _ (by decide) (by decide), g _ (by decide) (by decide), hal₁]; rfl⟩
  refine WP.seq (WP.mono (passes_ok hp hO) fun s₃ h₃ => ?_)
  rw [WP.block_append_iff]
  obtain ⟨s₅, h₅, ax₅, rd₅, wr₅, sp₅, k₅, m₅⟩ :=
    fp_ok (s₃.write .x .x14 (s₃.read .x .x14 - BitVec.ofNat _ 504))
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil],
    WP.of_runBlock ⟨s₅, h₅, ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [k₅ _ (by decide), gpr_write_of_ne _ _ _ (by decide), h₃.same.x15]
  · rw [k₅ _ (blockKept_ne hr), gpr_write_of_ne _ _ _ (outer_ne hr).2.2.2.2.1, h₃.same.keep r hr]
  · rw [sp₅]; exact h₃.same.sp
  · rw [rd₅]; exact h₃.same.rd
  · rw [wr₅]; exact h₃.same.wr
  · rw [m₅]; exact h₃.same.frame
  · rw [k₅ _ (by decide), gpr_write_self, State.read, BitVec.setWidth_eq, BitVec.setWidth_eq, h₃.x14,
      show 8 * kpos 3 0 = 504 from rfl, BitVec.add_sub_cancel]
  · rw [ax₅, gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (by decide), tdes_eq, ← h₃.halves]

end VG.Proof.CmacTripleDes.AArch64
