import VerifiedGarbage.Proof.Poly1305.Arm.Store
import VerifiedGarbage.Proof.Poly1305.Arm.Absorb

/-!
# Poly1305 on 32-bit ARM: saving registers, the limbs of `r`, and loading the accumulator

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)

/-! ## Saving and restoring the callee-saved registers -/

/-- The registers `g` saved at `[56, 88)` of the state at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (56 + 4 * i)) 32 = g (savedReg i)

def saveList : List (Reg × Nat × Bool) := (List.range 8).map fun i => (savedReg i, 56 + 4 * i, false)

theorem saveRegs_eq : saveRegs = saveList.map (storeI .r0) := rfl

/-- The saved registers' region. -/
abbrev saveR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 56, 32⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem saveRegs_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block saveRegs) s fun s' => Saved (State.addr st) s.gpr s'.mem ∧
      Frame [saveR (State.addr st)] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [saveRegs_eq]
  refine WP.mono (stores_ok .r0 hfit rfl saveList s h0 hw (by decide) (by decide))
    fun s' ⟨hs, hf, hg, hrd, hwr, hsp⟩ => ⟨fun i hi => ?_, hf.sub fun r hr => ?_, hg, hrd, hwr, hsp⟩
  · exact hs (savedReg i, 56 + 4 * i, false) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    exact ⟨_, List.mem_singleton_self _, sub_sub _ (by simp only; omega) (by simp [ssize]; omega) (by omega)⟩

theorem restoreRegs_ok {s : State} {g : Reg → BitVec 32} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hs : Saved (State.addr st) g s.mem) :
    WP isa (.block restoreRegs) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s')
    (fun n s' hn ⟨hl, hk⟩ => ?_) 8 le_rfl s ⟨fun _ h => absurd h (by omega), Keeps.refl _ _⟩)
    fun s' h => h
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 (56 + 4 * n)) (by omega)
    (by rw [hk.gpr _ (by decide), h0]; exact ea hfit (by omega))
    (by rw [hk.rd, hk.wr]; exact inSt hw (by omega)) fun s1 u1 => WP.block_nil ⟨fun i hi => ?_,
      hk.trans (u1.keeps (hsr n hn))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hk.mem]; exact hs i hn

/-! ## The limbs of `r` -/

/-- The key's words at `[24, 40)`, clamped. -/
def cw (m : Mem) (B : Addr) (i : Nat) : BitVec 32 :=
  m.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32 &&& (if i = 0 then 0x0fffffff else 0x0ffffffc)

/-- The limbs of the clamped `r` of the key in the memory `m` of the state at `B`. -/
def rlimb (m : Mem) (B : Addr) : Nat → Nat :=
  mlimb (cw m B 0).toNat (cw m B 1).toNat (cw m B 2).toNat (cw m B 3).toNat

/-- The region `clampWords` and `setupR` write. -/
abbrev rR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 88, 36⟩

omit hfit in
theorem key_rR (B : Addr) {d : Nat} (hd : d + 4 ≤ 88) :
    (⟨B + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint (rR B) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem clampWords_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block clampWords) s fun s' =>
      (∀ i < 4, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 = cw s.mem (State.addr st) i) ∧
      KeepsF [.r1, .r2] [rR (State.addr st)] s s' := by
  have hkey : ∀ {m : Mem}, Frame [rR (State.addr st)] s.mem m → ∀ i < 4,
      m.readW (State.addr st + BitVec.ofNat 64 (24 + 4 * i)) 32 =
        s.mem.readW (State.addr st + BitVec.ofNat 64 (24 + 4 * i)) 32 := fun hf i hi =>
    hf.readW (Region.contains_self _ _) (by simpa using key_rR (State.addr st) (d := 24 + 4 * i) (by omega))
      (by decide)
  rw [clampWords]
  simp only [List.cons_append]
  refine wp_movw fun s1 u1 => wp_movt fun s2 u2 => ?_
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 24) (by omega)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), h0]; exact ea hfit (by omega))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact inSt hw (by omega)) fun s3 u3 => ?_
  refine wp_and (op2_reg _ _) fun s4 u4 => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 88) (by omega)
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), h0]; exact ea hfit (by omega))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact outSt hw (by omega)) fun s5 u5 => ?_
  refine wp_movw fun s6 u6 => wp_movt fun s7 u7 => ?_
  rw [List.nil_append]
  have v0 : s5.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 = cw s.mem (State.addr st) 0 := by
    rw [u5.mem, Mem.readW_writeW_self32, u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, u1.gpr,
      u2.mem, u1.mem]
    rfl
  have k7 : KeepsF [.r1, .r2] [rR (State.addr st)] s s7 := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u7.other _ hr.2, u6.other _ hr.2, u5.gpr, u4.other _ hr.1, u3.other _ hr.1, u2.other _ hr.2,
        u1.other _ hr.2]
    · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub _ (by omega) (by omega)
        (by omega))
    · rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  have m2 : s7.gpr .r2 = 0x0ffffffc := by rw [u7.gpr, u6.gpr]; rfl
  have m7 : s7.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 = cw s.mem (State.addr st) 0 := by
    rw [u7.mem, u6.mem]; exact v0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n + 1, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 =
      cw s.mem (State.addr st) i) ∧ s'.gpr .r2 = 0x0ffffffc ∧ KeepsF [.r1, .r2] [rR (State.addr st)] s s')
    (fun n s' hn ⟨hl, hr2, hk⟩ => ?_) 3 le_rfl s7 ⟨fun i hi => by rw [show i = 0 by omega]; exact m7,
      m2, k7⟩) fun s' ⟨hl, _, hk⟩ => ⟨hl, hk⟩
  have hs0 : s'.gpr .r0 = st := by rw [hk.gpr _ (by decide), h0]
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 (24 + 4 * (n + 1))) (by omega)
    (by rw [hs0, show 28 + 4 * n = 24 + 4 * (n + 1) by ring]; exact ea hfit (by omega))
    (by rw [hk.rd, hk.wr]; exact inSt hw (by omega)) fun s1 u1 => ?_
  refine wp_and (op2_reg _ _) fun s2 u2 => ?_
  refine wp_str (a := State.addr st + BitVec.ofNat 64 (88 + 4 * (n + 1))) (by omega)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), hs0,
      show 92 + 4 * n = 88 + 4 * (n + 1) by ring]; exact ea hfit (by omega))
    (by rw [u2.wr, u1.wr, hk.wr]; exact outSt hw (by omega)) fun s3 u3 => WP.block_nil ⟨fun i hi => ?_, ?_, ?_⟩
  · rw [u3.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), u2.mem, u1.mem]; exact hl i h'
    · rw [Mem.readW_writeW_self32, u2.gpr, u1.gpr, u1.other _ (by decide), hr2, hkey hk.frame _ (by omega),
        cw, iteF (by omega)]
  · rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), hr2]
  · refine hk.trans ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u3.gpr, u2.other _ hr.1, u1.other _ hr.1]
    · rw [u3.mem, u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub _ (by omega) (by omega)
        (by omega))
    · rw [u3.rd, u2.rd, u1.rd]
    · rw [u3.wr, u2.wr, u1.wr]
    · rw [u3.sp, u2.sp, u1.sp]

omit hfit in
theorem zeroY_ok {s : State} :
    WP isa (.block zeroY) s fun s' => (∀ k < 9, s'.gpr (yr k) = 0) ∧ Keeps yregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, s'.gpr (yr k) = 0) ∧ Keeps yregs s s')
    (fun n s' hn ⟨hz, hk⟩ => wp_mov (op2_imm (by decide)) fun s1 u1 => WP.block_nil ⟨fun k hk' => ?_,
      hk.trans (u1.keeps (yr_yregs n hn))⟩) 9 le_rfl s ⟨fun _ h => absurd h (by omega), Keeps.refl _ _⟩)
    fun s' h => h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
  · rw [u1.other _ (fun e => absurd (yr_inj _ (by omega) _ (by omega) e) (by omega))]; exact hz k h'
  · rw [u1.gpr]

/-- The stores of the limbs of `r` in `setupR`. -/
def rList : List (Reg × Nat × Bool) :=
  [(.r3, 88, false), (.r4, 92, false), (.r5, 96, false), (.r6, 100, false), (.r7, 120, true),
   (.r8, 104, false), (.r9, 108, false), (.r10, 112, false), (.r11, 116, false), (.r1, 121, true)]

omit hfit in
theorem setupR_eq : setupR = clampWords ++ zeroY ++ [.dp .add .r1 .r0 (.imm 88)] ++ addWords ++
    [.mov .r1 (.shifted .r2 .lsr 21)] ++ rList.map (storeI .r0) := rfl

omit hfit in
theorem cw_lt (m : Mem) (B : Addr) (i : Nat) : (cw m B i).toNat < 2 ^ 28 := by
  simp only [cw, BitVec.toNat_and]
  split
  · exact and_lt (by decide)
  · exact and_lt (by decide)

omit hfit in
theorem cw2_even (m : Mem) (B : Addr) : (cw m B 2).toNat % 2 = 0 := by
  simp only [cw, BitVec.toNat_and, show (2 : Nat) ≠ 0 by decide, ite_false]
  exact and_fffffffc_mod _

omit hfit in
theorem rlimb_lt (m : Mem) (B : Addr) (i : Nat) : rlimb m B i < 2 ^ 13 :=
  mlimb_lt (by have := cw_lt m B 0; omega) (by have := cw_lt m B 1; omega)
    (by have := cw_lt m B 2; omega) (by have := cw_lt m B 3; omega) i

theorem setupR_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block setupR) s fun s' => (∀ i < 10, rval s'.mem (State.addr st) i = rlimb s.mem (State.addr st) i) ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) [rR (State.addr st)] s s' := by
  rw [setupR_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (clampWords_ok hfit h0 hw) fun s1 ⟨hm1, k1⟩ => ?_
  refine WP.append zeroY_ok fun s2 ⟨hz2, k2⟩ => ?_
  have hs20 : s2.gpr .r0 = st := by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), h0]
  refine wp_add (op2_imm (by decide)) fun s3 u3 => ?_
  have hs3 : s3.gpr .r1 = st + 88 := by rw [u3.gpr, hs20]
  have hw3 : stR st ∈ s3.wr := by rw [u3.wr, k2.wr, k1.wr]; exact hw
  have hwd : ∀ i < 4, State.addr (s3.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (88 + 4 * i) := fun i hi => by
    rw [hs3, BitVec.add_assoc, show (88 : BitVec 32) = BitVec.ofNat 32 88 from rfl, ← BitVec.ofNat_add]
    exact ea hfit (by omega)
  refine WP.append (addWords_ok fun i hi => by rw [hwd i hi]; exact inSt hw3 (by omega))
    fun s4 ⟨hc4, hr4, k4⟩ => ?_
  have hword : ∀ i < 4, word s3 i = cw s.mem (State.addr st) i := fun i hi => by
    simp only [word]; rw [hwd i hi, u3.mem, k2.mem]; exact hm1 i hi
  have e4 : ∀ k < 9, (s4.gpr (yr k)).toNat = rlimb s.mem (State.addr st) k := fun k hk => by
    rw [hc4 k hk, u3.other _ (yr_ne k hk).2.1, hz2 k hk, zadd, wsum_toNat _ hk, hword 0 (by omega),
      hword 1 (by omega), hword 2 (by omega), hword 3 (by omega)]
    rfl
  refine wp_mov (op2_lsr (by omega)) fun s5 u5 => ?_
  have e5 : (s5.gpr .r1).toNat = rlimb s.mem (State.addr st) 9 := by
    rw [u5.gpr, toNat_shr, hr4, hword 3 (by omega)]; rfl
  have hs50 : s5.gpr .r0 = st := by rw [u5.other _ (by decide), k4.gpr _ (by decide), u3.other _ (by decide), hs20]
  have hw5 : stR st ∈ s5.wr := by rw [u5.wr, k4.wr]; exact hw3
  refine WP.mono (stores_ok .r0 hfit rfl rList s5 hs50 hw5 (by decide) (by decide))
    fun s6 ⟨hs6, hf6, hg6, hrd6, hwr6, hsp6⟩ => ⟨fun i hi => ?_, ?_⟩
  · have hr : ∀ k < 9, (s5.gpr (yr k)).toNat = rlimb s.mem (State.addr st) k := fun k hk => by
      rw [u5.other _ (yr_ne k hk).2.1]; exact e4 k hk
    have b4 : rlimb s.mem (State.addr st) 4 < 2 ^ 8 := by
      have := cw_lt s.mem (State.addr st) 1; have := cw2_even s.mem (State.addr st)
      simp only [rlimb, mlimb]; omega
    have b9 : rlimb s.mem (State.addr st) 9 < 2 ^ 8 := by
      have := cw_lt s.mem (State.addr st) 3
      simp only [rlimb, mlimb]; omega
    have w : ∀ (r : Reg) (o : Nat) (k : Nat), (r, o, false) ∈ rList → (s5.gpr r).toNat = rlimb s.mem (State.addr st) k →
        (s6.mem.readW (State.addr st + BitVec.ofNat 64 o) 32).toNat = rlimb s.mem (State.addr st) k :=
      fun r o k hm hv => by have := hs6 _ hm; simp only [Stored] at this; rw [this, hv]
    have b : ∀ (r : Reg) (o : Nat) (k : Nat), (r, o, true) ∈ rList → (s5.gpr r).toNat = rlimb s.mem (State.addr st) k →
        rlimb s.mem (State.addr st) k < 2 ^ 8 →
        (s6.mem (State.addr st + BitVec.ofNat 64 o)).toNat = rlimb s.mem (State.addr st) k :=
      fun r o k hm hv hb => by
        have := hs6 _ hm; simp only [Stored] at this
        rw [this, BitVec.toNat_setWidth, hv, Nat.mod_eq_of_lt hb]
    interval_cases i <;> simp only [rval, rOff, Nat.reduceEqDiff, or_self, or_false, false_or, ite_true,
      ite_false]
    · exact w .r3 88 0 (by decide) (hr 0 (by omega))
    · exact w .r4 92 1 (by decide) (hr 1 (by omega))
    · exact w .r5 96 2 (by decide) (hr 2 (by omega))
    · exact w .r6 100 3 (by decide) (hr 3 (by omega))
    · exact b .r7 120 4 (by decide) (hr 4 (by omega)) b4
    · exact w .r8 104 5 (by decide) (hr 5 (by omega))
    · exact w .r9 108 6 (by decide) (hr 6 (by omega))
    · exact w .r10 112 7 (by decide) (hr 7 (by omega))
    · exact w .r11 116 8 (by decide) (hr 8 (by omega))
    · exact b .r1 121 9 (by decide) e5 b9
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [hg6, u5.other _ hr.1, k4.gpr _ (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]), u3.other _ hr.1,
        k2.gpr _ hr.2.2.2, k1.gpr _ (by simp [hr.1, hr.2.1])]
    · have e : s5.mem = s1.mem := by rw [u5.mem, k4.mem, u3.mem, k2.mem]
      rw [e] at hf6
      refine k1.frame.trans (hf6.sub fun r hr => ?_)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hb : ∀ x ∈ rList, 88 ≤ x.2.1 ∧ x.2.1 + ssize x.2.2 ≤ 124 := by decide
      have := hb x hx
      exact ⟨_, List.mem_singleton_self _, sub_sub _ this.1 (by omega) (by omega)⟩
    · rw [hrd6, u5.rd, k4.rd, u3.rd, k2.rd, k1.rd]
    · rw [hwr6, u5.wr, k4.wr, u3.wr, k2.wr, k1.wr]
    · rw [hsp6, u5.sp, k4.sp, u3.sp, k2.sp, k1.sp]

/-! ## Loading the accumulator -/

/-- Word `i` of the state at `B`. -/
def hwd (m : Mem) (B : Addr) (i : Nat) : Nat := (m.readW (B + BitVec.ofNat 64 (4 * i)) 32).toNat

/-- The columns `loadAcc` makes of the accumulator stored in the state at `B`. -/
def accD (m : Mem) (B : Addr) : Nat → Nat := fun k =>
  if k = 9 then hwd m B 3 / 2 ^ 21 + hwd m B 4 % 4 * 2 ^ 11
  else mlimb (hwd m B 0) (hwd m B 1) (hwd m B 2) (hwd m B 3) k

omit hfit in
theorem accD_lt (m : Mem) (B : Addr) (k : Nat) : accD m B k < 2 ^ 13 := by
  have h3 : hwd m B 3 < 2 ^ 32 := BitVec.isLt _
  simp only [accD]
  split
  · omega
  · exact mlimb_lt (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) h3 k

omit hfit in
theorem val_accD (m : Mem) (B : Addr) :
    val (accD m B) = hwd m B 0 + 2 ^ 32 * hwd m B 1 + 2 ^ 64 * hwd m B 2 + 2 ^ 96 * hwd m B 3 +
      2 ^ 128 * (hwd m B 4 % 4) := by
  have hv := val_mlimb (w0 := hwd m B 0) (w1 := hwd m B 1) (w2 := hwd m B 2) (w3 := hwd m B 3)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  simp only [val, accD, Nat.reduceEqDiff, ite_true, ite_false] at hv ⊢
  simp only [mlimb] at hv ⊢
  omega

theorem loadAcc_ok {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) :
    WP isa (.block loadAcc) s fun s' => ColsD (accD s.mem (State.addr st)) (State.addr st) s' ∧
      KeepsF (.r1 :: .r2 :: .r12 :: yregs) [accR (State.addr st)] s s' := by
  rw [loadAcc]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append zeroY_ok fun s1 ⟨hz1, k1⟩ => ?_
  have hs10 : s1.gpr .r0 = st := by rw [k1.gpr _ (by decide), h0]
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  have hw2 : stR st ∈ s2.wr := by rw [u2.wr, k1.wr]; exact hw
  have hwd' : ∀ i < 4, State.addr (s2.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (4 * i) := fun i hi => by
    rw [u2.gpr, hs10]; exact ea hfit (by omega)
  refine WP.append (addWords_ok fun i hi => by rw [hwd' i hi]; exact inSt hw2 (by omega))
    fun s3 ⟨hc3, hr3, k3⟩ => ?_
  have hword : ∀ i < 4, (word s2 i).toNat = hwd s.mem (State.addr st) i := fun i hi => by
    simp only [word]; rw [hwd' i hi, u2.mem, k1.mem]; rfl
  have hs30 : s3.gpr .r0 = st := by rw [k3.gpr _ (by decide), u2.other _ (by decide), hs10]
  refine wp_mov (op2_lsr (by omega)) fun s4 u4 => ?_
  refine wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by omega)
    (by rw [u4.other _ (by decide), hs30]; exact ea hfit (off := 16) (by omega))
    (by rw [u4.rd, u4.wr, k3.rd, k3.wr]; exact inSt hw2 (off := 16) (n := 4) (by omega)) fun s5 u5 => ?_
  refine wp_mov (op2_lsl (by omega)) fun s6 u6 => wp_add (op2_lsr (by omega)) fun s7 u7 => ?_
  have v7 : (s7.gpr .r1).toNat = accD s.mem (State.addr st) 9 := by
    have e4 : (s4.gpr .r1).toNat = hwd s.mem (State.addr st) 3 / 2 ^ 21 := by
      rw [u4.gpr, toNat_shr, hr3, hword 3 (by omega)]
    have e6 : (s6.gpr .r2).toNat = hwd s.mem (State.addr st) 4 * 2 ^ 30 % 2 ^ 32 := by
      rw [u6.gpr, u5.gpr, toNat_shl, u4.mem, k3.mem, u2.mem, k1.mem]; rfl
    have h3 : hwd s.mem (State.addr st) 3 < 2 ^ 32 := BitVec.isLt _
    rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide),
      toNat_add_lt (by rw [e4, toNat_shr, e6]; omega), e4, toNat_shr, e6]
    simp only [accD, ite_true]
    omega
  have hs70 : s7.gpr .r0 = st := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      hs30]
  refine wp_str (a := State.addr st + BitVec.ofNat 64 16) (by decide)
    (by rw [hs70]; exact ea hfit (off := 16) (by omega))
    (by rw [u7.wr, u6.wr, u5.wr, u4.wr, k3.wr]; exact outSt hw2 (off := 16) (n := 4) (by omega))
    fun s8 u8 => WP.block_nil ⟨⟨fun k hk => ?_, ?_⟩, ?_⟩
  · have hne := yr_ne k hk
    rw [u8.gpr, u7.other _ hne.2.1, u6.other _ hne.2.2.1, u5.other _ hne.2.2.1, u4.other _ hne.2.1, hc3 k hk,
      u2.other _ hne.2.1, hz1 k hk, zadd, wsum_toNat _ hk, hword 0 (by omega), hword 1 (by omega),
      hword 2 (by omega), hword 3 (by omega)]
    simp only [accD, iteF (show k ≠ 9 by omega)]
  · rw [u8.mem, Mem.readW_writeW_self32]; exact v7
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [u8.gpr, u7.other _ hr.1, u6.other _ hr.2.1, u5.other _ hr.2.1, u4.other _ hr.1,
        k3.gpr _ (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]), u2.other _ hr.1, k1.gpr _ hr.2.2.2]
    · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, k3.mem, u2.mem, k1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
    · rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, k3.rd, u2.rd, k1.rd]
    · rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, k3.wr, u2.wr, k1.wr]
    · rw [u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, k3.sp, u2.sp, k1.sp]

end

end VG.Proof.Poly1305.Arm
