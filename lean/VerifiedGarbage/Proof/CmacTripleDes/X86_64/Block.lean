import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Round
import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# TDEA on x86-64: the passes and the block

`block` encrypts the 64-bit block in `rax` with the key schedule at `r14`
(`block_ok`): `IP` into `r12` and `r13`, three passes of sixteen rounds
(`pass_ok`, the round keys `rbx` bytes apart, the halves exchanged after
each pass), and `IP⁻¹`. During the block, `r14` points to slot
`kpos p j` of the key schedule before round `j` of pass `p`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `r14` readable, and the slots
0–5 of the scratch buffer at `r15` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .r14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .r15 ∧ 48 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .r15, 48⟩ ⟨s.gpr .r14, 384⟩

/-- The slots of the broadcast inputs. -/
abbrev xR (s₀ : State) : Region := ⟨s₀.gpr .r15, 48⟩

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  r15 : s.gpr .r15 = s₀.gpr .r15
  rbp : s.gpr .rbp = s₀.gpr .rbp
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .r14)

theorem wordAddr_zero (a : Addr) : wordAddr a 0 = a := by simp [wordAddr]

theorem ok_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * n)) : Ok rCfg s := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, by decide, fun k hk' j hj => ?_⟩
  · rw [h.wr]
    exact ⟨X, hX, contains_word (off := 0) (by show s.gpr .r15 = _; rw [h.r15, ← hXb]; simp)
      (by simp only [rCfg] at hk'; omega) hXl hXw⟩
  · simp only [rCfg] at hk'
    obtain rfl : k = 0 := by omega
    rw [h.rd, h.wr]
    exact ⟨R, hR, contains_word (off := 8 * n) (by show s.gpr .r14 = _; rw [hk, hRb]) (by omega) hRl hRw⟩
  · simp only [rCfg] at hk' hj
    obtain rfl : j = 0 := by omega
    rw [show rCfg.base = .r15 from rfl, show rCfg.ext = .r14 from rfl, h.r15, hk, wordAddr_zero]
    exact hp.disj.sep (slot_contains _ hk' (by decide)) (Offset.contains_base _ (by omega) (by omega))

theorem key_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * n)) : keyW s = (sch s₀).getD n 0 := by
  rw [scheduleAt_getD _ _ hn, keyW, wordAddr_zero, hk]
  refine h.frame.readW (r := ⟨s₀.gpr .r14 + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.disj.sub_right (Offset.sub_base _ (by omega))).symm

/-! ## The rounds of a pass -/

theorem roundTail_ok (s : State) :
    ∃ s', runBlock isa roundTail s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 + s.gpr .rbx ∧ s'.gpr .r11 = s.gpr .r11 - 1 ∧
      s'.zf = some ((s.gpr .r11 - 1) == 0) ∧ (∀ r, r ≠ .r14 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [roundTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

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
  r14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * kpos p j)
  rbx : s.gpr .rbx = stride p
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (16 - j)
  halves : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = rounds (passKeys (sch s₀) p) j lr

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
    WP isa (.block (round ++ roundTail)) s fun s' =>
      s'.zf = some (decide (j + 1 = 16)) ∧ PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, e12, e13, rd₁, wr₁, k₁, f₁⟩ := round_ok (ok_at hp h.same (kpos_lt hp3 hj) h.r14)
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ?_⟩
  obtain ⟨s₂, h₂, t14, t11, tzf, tk, tm, trd, twr⟩ := roundTail_ok s₁
  have kk : ∀ r ∈ kept, s₁.gpr r = s.gpr r := k₁
  refine ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tzf, kk .r11 (by simp [kept]), h.r11, ofNat_sub_one (by omega) (by omega),
      ofNat_beq_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r15 (by decide) (by decide), kk .r15 (by simp [kept]), h.same.r15]
  · rw [tk .rbp (by decide) (by decide), kk .rbp (by simp [kept]), h.same.rbp]
  · rw [tk .rsp (by decide) (by decide), kk .rsp (by simp [kept]), h.same.rsp]
  · rw [trd, rd₁, h.same.rd]
  · rw [twr, wr₁, h.same.wr]
  · rw [tm]
    have hr : slotRegion rCfg s = xR s₀ := by
      simp only [slotRegion, xR]; rw [show rCfg.base = .r15 from rfl, h.same.r15]; rfl
    rw [hr] at f₁
    exact h.same.frame.trans f₁
  · rw [t14, kk .r14 (by simp [kept]), kk .rbx (by simp [kept]), h.r14, h.rbx, kpos_succ_addr _ hp3 hj]
  · rw [tk .rbx (by decide) (by decide), kk .rbx (by simp [kept]), h.rbx]
  · rw [tk .r10 (by decide) (by decide), kk .r10 (by simp [kept]), h.r10]
  · rw [t11, kk .r11 (by simp [kept]), h.r11, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [rounds_succ, ← h.halves, tk .r12 (by decide) (by decide), tk .r13 (by decide) (by decide), e12, e13,
      key_at hp h.same (kpos_lt hp3 hj) h.r14, passKeys_at s₀ hj]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (h14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * kpos p 0))
    (hbx : s.gpr .rbx = stride p) (h10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p))
    (hlr : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = lr) :
    WP isa pass s (PInv s₀ p lr 16) := by
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some]; rfl, ?_⟩)
  have g : ∀ r, r ≠ .r11 → (s.setReg32 .r11 (16 : BitVec 32)).gpr r = s.gpr r := fun r hr => by
    simp [State.setReg32, gpr_setReg, hr]
  have h0 : PInv s₀ p lr 0 (s.setReg32 .r11 (16 : BitVec 32)) :=
    ⟨⟨by rw [g _ (by decide), h.r15], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.rsp],
      h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], by rw [g _ (by decide), hbx],
      by rw [g _ (by decide), h10], by simp [State.setReg32, gpr_setReg],
      by rw [g _ (by decide), g _ (by decide), hlr]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .ne) (Q := PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, h0⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (roundStep_ok hp hp3 hj ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

theorem passTail_ok (s : State) :
    ∃ s', runBlock isa passTail s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 + (BitVec.ofNat 64 128 - s.gpr .rbx) ∧ s'.gpr .rbx = 0 - s.gpr .rbx ∧
      s'.gpr .r12 = s.gpr .r13 ∧ s'.gpr .r13 = s.gpr .r12 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some ((s.gpr .r10 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rax, .rbx, .r10, .r12, .r13, .r14] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [passTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, readSrc32, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      State.setReg32, ite_false, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  r14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * kpos p 0)
  rbx : s.gpr .rbx = stride p
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p)
  halves : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : Addr) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 64 (8 * kpos p 16) + (BitVec.ofNat 64 128 - stride p) =
      a + BitVec.ofNat 64 (8 * kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - stride p = stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' =>
      s'.zf = some (decide (p + 1 = 3)) ∧ OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (pass_ok hp hp3 h.same h.r14 h.rbx h.r10 h.halves) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t14, tbx, t12, t13, t10, tzf, tk, tm, trd, twr⟩ := passTail_ok s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [tzf, h₁.r10, ofNat_sub_one (by omega) (by omega), ofNat_beq_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r15 (by decide), h₁.same.r15]
  · rw [tk .rbp (by decide), h₁.same.rbp]
  · rw [tk .rsp (by decide), h₁.same.rsp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [t14, h₁.r14, h₁.rbx, kpos_tail_addr _ hp3]
  · rw [tbx, h₁.rbx, stride_succ hp3]
  · rw [t10, h₁.r10, ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [t12, t13, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {s : State} (h : OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (passBody_ok hp hp3 ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- `IP`'s high half into `r12`, its low half into `r13`, from `rax` (input word 0). -/
def ipG12 (t : Nat) : List Nat := if t < 32 then [ipSrc (32 + t)] else []
def ipG13 (t : Nat) : List Nat := if t < 32 then [ipSrc t] else []

theorem ip_check :
    check (lanes 64 6) oCfg (linExt 1) ipCode (linEnv [(.rax, 0)])
      (linPost 6 [(.r12, ipG12), (.r13, ipG13)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `rax`, from `R` in `r12` (input word 0) and `L` in `r13` (input word 1). -/
def fpG (j : Nat) : List Nat := if 32 ≤ fpSrc j then [fpSrc j - 32] else [64 + fpSrc j]

theorem fp_check :
    check (lanes 64 7) oCfg (linExt 2) fpCode (linEnv [(.r12, 0), (.r13, 1)]) (linPost 7 [(.rax, fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.rbp, .rsp, .r14, .r15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => i.dst != some r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => i.dst != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

theorem frame_oCfg {s : State} {m m' : Mem} (h : Frame [slotRegion oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      ((s'.gpr .r12).setWidth 32, (s'.gpr .r13).setWidth 32) =
        split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .rax)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok ip_check (oCfg_ok s) (fun _ => s.gpr .rax)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, fun r hr => hoth r (List.all_eq_true.mp ip_kept r hr), frame_oCfg hfr⟩
  have h12 := hout .r12 ipG12 (by simp)
  have h13 := hout .r13 ipG13 (by simp)
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
      s'.gpr .rax = Spec.TripleDes.permute Spec.TripleDes.fp ((s.gpr .r12).setWidth 32 ++ (s.gpr .r13).setWidth 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .r12 else s.gpr .r13
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok fp_check (oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, fun r hr => hoth r (List.all_eq_true.mp fp_kept r hr), frame_oCfg hfr⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := fpSrc_lt j hj
  rw [hout .rax fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
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

theorem sub504_ok (s : State) :
    ∃ s', runBlock isa [.alu .sub .r14 (.imm 504)] s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 - BitVec.ofNat 64 504 ∧ (∀ r, r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_self]; rfl
  · simp [gpr_setReg, hr]

/-- TDEA encryption of the block in `rax` (as a 64-bit integer) with the key
schedule at `r14`, into `rax`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      Same s₀ s ∧ s.gpr .r14 = s₀.gpr .r14 ∧ s.gpr .rax = tdes (sch s₀) (s₀.gpr .rax) := by
  obtain ⟨s₁, h₁, hal₁, rd₁, wr₁, k₁, m₁⟩ := ip_ok s₀
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some]; rfl, ?_⟩⟩
  have g : ∀ r, r ≠ .r10 → r ≠ .rbx →
      ((s₁.setReg32 .r10 (3 : BitVec 32)).setReg32 .rbx (8 : BitVec 32)).gpr r = s₁.gpr r := fun r h1 h2 => by
    simp [State.setReg32, gpr_setReg, h1, h2]
  have hO : OInv s₀ (s₀.gpr .rax) 0 ((s₁.setReg32 .r10 (3 : BitVec 32)).setReg32 .rbx (8 : BitVec 32)) :=
    ⟨⟨by rw [g _ (by decide) (by decide), k₁ _ (by decide)], by rw [g _ (by decide) (by decide), k₁ _ (by decide)],
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)], rd₁, wr₁,
      by show Frame [xR s₀] s₀.mem s₁.mem; rw [m₁]; exact Frame.refl _ _⟩,
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)]; simp [kpos],
      by simp [State.setReg32, gpr_setReg, stride],
      by simp [State.setReg32, gpr_setReg],
      by rw [g _ (by decide) (by decide), g _ (by decide) (by decide), hal₁]; rfl⟩
  refine WP.seq (WP.mono (passes_ok hp hO) fun s₃ h₃ => ?_)
  rw [WP.block_append_iff]
  obtain ⟨s₄, h₄, r14₄, g4, m₄, rd₄, wr₄⟩ := sub504_ok s₃
  obtain ⟨s₅, h₅, ax₅, rd₅, wr₅, k₅, m₅⟩ := fp_ok s₄
  refine WP.of_runBlock ⟨s₄, h₄, WP.of_runBlock ⟨s₅, h₅, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.r15]
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.rbp]
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.rsp]
  · rw [rd₅, rd₄, h₃.same.rd]
  · rw [wr₅, wr₄, h₃.same.wr]
  · rw [m₅, m₄]; exact h₃.same.frame
  · rw [k₅ _ (by decide), r14₄, h₃.r14, show 8 * kpos 3 0 = 504 from rfl, BitVec.add_sub_cancel]
  · rw [ax₅, g4 _ (by decide), g4 _ (by decide), tdes_eq, ← h₃.halves]

end VG.Proof.CmacTripleDes.X86_64
