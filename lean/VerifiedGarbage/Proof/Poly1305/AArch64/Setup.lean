import VerifiedGarbage.Proof.Poly1305.AArch64.Common

/-!
# Poly1305 on AArch64: the coefficients and the accumulator on entry

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

set_option simprocs false in
/-- `r` clamped. -/
theorem clampR_ok (s : State) :
    WP isa (.block clampR) s fun s' =>
      s'.gpr .x14 = s.gpr .x14 &&& M0 ∧ s'.gpr .x15 = s.gpr .x15 &&& M1 ∧
      Keeps [.x14, .x15, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [clampR, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [movz_movk64']
  · rw [movz_movk64']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2]

set_option simprocs false in
/-- `sj = 5 rj`. -/
theorem times5_ok (s : State) :
    WP isa (.block times5) s fun s' =>
      v s' .x4 = (v s .x10 * 2 ^ 2 % 2 ^ 64 + v s .x10) % 2 ^ 64 ∧
      v s' .x5 = (v s .x11 * 2 ^ 2 % 2 ^ 64 + v s .x11) % 2 ^ 64 ∧
      v s' .x6 = (v s .x12 * 2 ^ 2 % 2 ^ 64 + v s .x12) % 2 ^ 64 ∧
      v s' .x7 = (v s .x13 * 2 ^ 2 % 2 ^ 64 + v s .x13) % 2 ^ 64 ∧
      Keeps [.x4, .x5, .x6, .x7] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [times5, runBlock_cons, runStep_some, runBlock_nil,
    exec_lsl_x (show 2 < 64 by decide), exec_add, v, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩ <;> try rw [add_toNat, lsl_toNat]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

/-- The memory after the coefficients are stored: `r j` at `rOff j`, `s j` at `sOff j`. -/
def coefMem (m : Mem) (st : Addr) (r s : Nat → BitVec 64) : Mem :=
  ((((((((m.writeW (off st (rOff 0)) ((r 0).setWidth 32)).writeW (off st (rOff 1))
    ((r 1).setWidth 32)).writeW (off st (rOff 2)) ((r 2).setWidth 32)).writeW (off st (rOff 3))
    ((r 3).setWidth 32)).writeW (off st (rOff 4)) ((r 4).setWidth 32)).writeW (off st (sOff 1))
    ((s 1).setWidth 32)).writeW (off st (sOff 2)) ((s 2).setWidth 32)).writeW (off st (sOff 3))
    ((s 3).setWidth 32)).writeW (off st (sOff 4)) ((s 4).setWidth 32)

/-- The registers holding `rj` and `sj` when they are stored. -/
def rv (s : State) (j : Nat) : BitVec 64 := s.gpr (D.getD j .x9)
def sv (s : State) (j : Nat) : BitVec 64 := s.gpr (H.getD (j - 1) .x4)

set_option simprocs false in
theorem storeCoefs_ok (s : State)
    (hw : ∀ d, 72 ≤ d → d + 4 ≤ 108 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 4) :
    WP isa (.block storeCoefs) s fun s' =>
      s'.mem = coefMem s.mem (s.gpr .x0) (rv s) (sv s) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have o0 := hw (72 + 4 * 0) (by omega) (by omega); have o1 := hw (72 + 4 * 1) (by omega) (by omega)
  have o2 := hw (72 + 4 * 2) (by omega) (by omega); have o3 := hw (72 + 4 * 3) (by omega) (by omega)
  have o4 := hw (72 + 4 * 4) (by omega) (by omega); have o5 := hw (88 + 4 * 1) (by omega) (by omega)
  have o6 := hw (88 + 4 * 2) (by omega) (by omega); have o7 := hw (88 + 4 * 3) (by omega) (by omega)
  have o8 := hw (88 + 4 * 4) (by omega) (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeCoefs, rOff, sOff, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, Size.bytes, State.store, State.read, Size.bits, Option.bind_some,
    o0, o1, o2, o3, o4, o5, o6, o7, o8, ite_true, Option.some.injEq, exists_eq_left']
  trivial

set_option simprocs false in
theorem coefMem_r (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {j : Nat} (hj : j < 5) :
    (coefMem m st r s).readW (off st (rOff j)) 32 = (r j).setWidth 32 := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  all_goals simp (config := {decide := true}) only [coefMem, rOff, sOff, Mem.readW_writeW_self32,
    readW32_writeW32_off]

set_option simprocs false in
theorem coefMem_s (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {j : Nat} (hj₁ : 1 ≤ j) (hj : j < 5) :
    (coefMem m st r s).readW (off st (sOff j)) 32 = (s j).setWidth 32 := by
  obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  all_goals simp (config := {decide := true}) only [coefMem, rOff, sOff, Mem.readW_writeW_self32,
    readW32_writeW32_off]

/-- The coefficients' region. -/
abbrev cR (st : Addr) : Region := ⟨off st 72, 36⟩

theorem coefMem_frame (m : Mem) (st : Addr) (r s : Nat → BitVec 64) :
    Frame [cR st] m (coefMem m st r s) := by
  have c : ∀ d, 72 ≤ d → d + 4 ≤ 108 → (cR st).Contains (off st d) (32 / 8) := fun d h₁ h₂ => by
    simp only [Region.Contains, off]
    rw [show st + BitVec.ofNat 64 d - (st + BitVec.ofNat 64 72) = BitVec.ofNat 64 (d - 72) by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  simp only [coefMem]
  refine (((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c (rOff 0) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (rOff 1) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (rOff 2) ?_ ?_)).writeW (List.mem_singleton_self _) _ (c (rOff 3) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (rOff 4) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (sOff 1) ?_ ?_)).writeW (List.mem_singleton_self _) _ (c (sOff 2) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (sOff 3) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (sOff 4) ?_ ?_)
  all_goals decide

/-- The coefficients read back. -/
theorem coefMem_coefs (m : Mem) (st : Addr) (r s : Nat → BitVec 64) (R : Nat)
    (hr : ∀ j < 5, ((r j).setWidth 32).toNat = lim R j)
    (hs : ∀ j, 1 ≤ j → j < 5 → ((s j).setWidth 32).toNat = 5 * lim R j) :
    Coefs (coefMem m st r s) st R := by
  intro k hk i hi
  by_cases h : i ≤ k
  · have e : coef k i = rOff (k - i) := ite_eq_left h
    have e' : cval R k i = lim R (k - i) := ite_eq_left h
    rw [e, e', ← hr (k - i) (by omega)]
    exact congrArg BitVec.toNat (coefMem_r m st r s (by omega))
  · have e : coef k i = sOff (k + 5 - i) := ite_eq_right h
    have e' : cval R k i = 5 * lim R (k + 5 - i) := ite_eq_right h
    rw [e, e', ← hs (k + 5 - i) (by omega) (by omega)]
    exact congrArg BitVec.toNat (coefMem_s m st r s (by omega) (by omega))

set_option simprocs false in
/-- The limbs of the stored `h` into `x4`–`x8`, from those of its low 128 bits in `x9`–`x13`. -/
theorem moveH_ok (s : State) (h16 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 16) 8) :
    WP isa (.block moveH) s fun s' =>
      v s' .x4 = v s .x9 ∧ v s' .x5 = v s .x10 ∧ v s' .x6 = v s .x11 ∧ v s' .x7 = v s .x12 ∧
      v s' .x8 = (v s .x13 + w64 s.mem (s.gpr .x0) 16 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x16] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [moveH, runBlock_cons, runStep_some, runBlock_nil,
    exec_ldr_x (show 16 % 8 = 0 ∧ 16 < 32768 by decide) h16, exec_lsl_x (show 24 < 64 by decide),
    exec_addImm_x (show 0 < 4096 by decide), exec_add, v, State.read, State.write, Size.bits,
    BitVec.setWidth_eq, add_ofNat_zero, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [add_toNat, lsl_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-! ## `setup` -/

/-- The registers `setup` writes. -/
abbrev setupRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The state after `setup`, from `s₀`. -/
structure Setup (s₀ s : State) : Prop where
  gpr : ∀ r, r ∉ setupRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mask : s.gpr .x17 = M26
  frame : Frame [cR (s₀.gpr .x0)] s₀.mem s.mem
  coefs : Coefs s.mem (s₀.gpr .x0) (Rk s₀.mem (s₀.gpr .x0))
  acc : leNum (bytesAt s₀.mem (s₀.gpr .x0) 24) < P →
    hv s = leNum (bytesAt s₀.mem (s₀.gpr .x0) 24) ∧ Bounds s

theorem times5_eq {N : Nat} (h : N < 2 ^ 26) : (N * 2 ^ 2 % 2 ^ 64 + N) % 2 ^ 64 = 5 * N := by
  omega

theorem lt5_cases {j : Nat} (h : j < 5) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
theorem lt5_cases' {j : Nat} (h₁ : 1 ≤ j) (h : j < 5) : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega

/-- The limbs of `h = W0 + 2⁶⁴ W1 + 2¹²⁸ W2 < p`, as `loadH` computes them. -/
theorem loadH_arith {W0 W1 W2 : Nat} (h0 : W0 < 2 ^ 64) (h1 : W1 < 2 ^ 64)
    (hP : W0 + 2 ^ 64 * W1 + 2 ^ 128 * W2 < P) :
    val5 (lim (W0 + 2 ^ 64 * W1) 0) (lim (W0 + 2 ^ 64 * W1) 1) (lim (W0 + 2 ^ 64 * W1) 2)
        (lim (W0 + 2 ^ 64 * W1) 3) ((lim (W0 + 2 ^ 64 * W1) 4 + W2 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64) =
      W0 + 2 ^ 64 * W1 + 2 ^ 128 * W2 ∧
    lim (W0 + 2 ^ 64 * W1) 0 < 2 ^ 26 ∧ lim (W0 + 2 ^ 64 * W1) 1 < 2 ^ 27 ∧
    lim (W0 + 2 ^ 64 * W1) 2 < 2 ^ 26 ∧ lim (W0 + 2 ^ 64 * W1) 3 < 2 ^ 26 ∧
    (lim (W0 + 2 ^ 64 * W1) 4 + W2 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64 < 2 ^ 26 := by
  have e := val5_lim (W0 + 2 ^ 64 * W1)
  have b0 := lim_lt (W0 + 2 ^ 64 * W1) (j := 0) (by omega)
  have b1 := lim_lt (W0 + 2 ^ 64 * W1) (j := 1) (by omega)
  have b2 := lim_lt (W0 + 2 ^ 64 * W1) (j := 2) (by omega)
  have b3 := lim_lt (W0 + 2 ^ 64 * W1) (j := 3) (by omega)
  have b4 := lim4_lt (N := W0 + 2 ^ 64 * W1) (by omega)
  have hW2 : W2 ≤ 3 := by simp only [P] at hP; omega
  generalize lim (W0 + 2 ^ 64 * W1) 0 = a0, lim (W0 + 2 ^ 64 * W1) 1 = a1,
    lim (W0 + 2 ^ 64 * W1) 2 = a2, lim (W0 + 2 ^ 64 * W1) 3 = a3,
    lim (W0 + 2 ^ 64 * W1) 4 = a4 at *
  simp only [val5] at e ⊢
  omega

theorem lt32 {N : Nat} (h : N < 2 ^ 26) : N < 2 ^ 32 := by omega

theorem times5_lt {N : Nat} (h : N < 2 ^ 26) : 5 * N < 2 ^ 32 := by omega

/-- A coefficient in a register, stored as a 32-bit word. -/
theorem coef_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 32) :
    (x.setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, h, Nat.mod_eq_of_lt hn]

theorem coefMem_readW_low (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {d : Nat} (hd : d + 8 ≤ 56) :
    (coefMem m st r s).readW (off st d) 64 = m.readW (off st d) 64 := by
  refine (coefMem_frame m st r s).readW (r := ⟨off st d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  intro a h₁ h₂
  simp only [Region.Contains, off] at h₁ h₂
  bv_omega

theorem setup_ok (s₀ : State) (hw : sR (s₀.gpr .x0) ∈ s₀.wr) :
    WP isa (.block setup) s₀ (Setup s₀) := by
  have i : ∀ d n, d + n ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .x0) d) n :=
    fun d n h => ⟨_, List.mem_append_right _ hw, contains_off h (by omega)⟩
  rw [setup, coeffs, loadH]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (mask_ok s₀) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := k₁.gpr'
  refine WP.block_append (WP.mono (load2_ok s₁ (n := .x0) (off := 24) (by decide) (by decide)
    (by decide) (by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact i 24 8 (by omega))
    (by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact i (24 + 8) 8 (by omega))) fun s₂ ⟨l₁, l₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (clampR_ok s₂) fun s₃ ⟨c₁, c₂, k₃⟩ => ?_)
  have k₁₃ := (k₁.trans k₂).trans k₃
  refine WP.block_append (WP.mono (split_ok s₃ (by rw [(k₂.trans k₃).gpr']; exact m₁))
    fun s₄ ⟨r0, r1, r2, r3, r4, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (times5_ok s₄) fun s₅ ⟨t1, t2, t3, t4, k₅⟩ => ?_)
  have k₁₅ := (k₁₃.trans k₄).trans k₅
  have x0₅ : s₅.gpr .x0 = s₀.gpr .x0 := k₁₅.gpr'
  have m₅ : s₅.gpr .x17 = M26 := by rw [(((k₂.trans k₃).trans k₄).trans k₅).gpr']; exact m₁
  refine WP.block_append (WP.mono (storeCoefs_ok s₅ fun d h₁ h₂ => by
    rw [k₁₅.2.2.2, x0₅]; exact ⟨_, hw, contains_off (by omega) (by omega)⟩)
    fun s₆ ⟨mm₆, g₆, rd₆, wr₆⟩ => ?_)
  have x0₆ : s₆.gpr .x0 = s₀.gpr .x0 := by rw [g₆, x0₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₁₅.2.2.1]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₁₅.2.2.2]
  refine WP.block_append (WP.mono (load2_ok s₆ (n := .x0) (off := 0) (by decide) (by decide)
    (by decide) (by rw [rd₆', wr₆', x0₆]; exact i 0 8 (by omega))
    (by rw [rd₆', wr₆', x0₆]; exact i (0 + 8) 8 (by omega))) fun s₇ ⟨l₃, l₄, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₇ (by
    rw [k₇.gpr', g₆]; exact m₅))
    fun s₈ ⟨h0, h1, h2, h3, h4, k₈⟩ => ?_)
  have k₇₈ := k₇.trans k₈
  refine WP.mono (moveH_ok s₈ (by
    rw [k₇₈.2.2.1, k₇₈.2.2.2, k₇₈.gpr', rd₆', wr₆', x0₆]; exact i 16 8 (by omega)))
    fun s₉ ⟨e0, e1, e2, e3, e4, k₉⟩ => ?_
  have k₇₉ := k₇₈.trans k₉
  have sub : ∀ r, r ∉ setupRegs → ∀ l : List Reg, (∀ x ∈ l, x ∈ setupRegs) → r ∉ l :=
    fun r hr l hl h => hr (hl r h)
  have mem₉ : s₉.mem = coefMem s₀.mem (s₀.gpr .x0) (rv s₅) (sv s₅) := by
    rw [k₇₉.2.1, mm₆, k₁₅.2.1, x0₅]
  have R_eq : v s₃ .x14 + 2 ^ 64 * v s₃ .x15 = Rk s₀.mem (s₀.gpr .x0) := by
    simp only [v, c₁, c₂, l₁, l₂, x0₁, k₁.2.1]
  have b : ∀ j < 4, lim (Rk s₀.mem (s₀.gpr .x0)) j < 2 ^ 26 := fun j hj => lim_lt _ hj
  have b4 := lim4_lt (Rk_lt s₀.mem (s₀.gpr .x0))
  have v5 : ∀ r ∈ [Reg.x9, .x10, .x11, .x12, .x13], v s₅ r = v s₄ r := fun r hr => by
    simp only [v]; rw [k₅.1 r (by revert hr; decide +revert)]
  have q0 : v s₅ .x9 = lim (Rk s₀.mem (s₀.gpr .x0)) 0 := by rw [v5 .x9 (by simp), r0, R_eq]
  have q1 : v s₅ .x10 = lim (Rk s₀.mem (s₀.gpr .x0)) 1 := by rw [v5 .x10 (by simp), r1, R_eq]
  have q2 : v s₅ .x11 = lim (Rk s₀.mem (s₀.gpr .x0)) 2 := by rw [v5 .x11 (by simp), r2, R_eq]
  have q3 : v s₅ .x12 = lim (Rk s₀.mem (s₀.gpr .x0)) 3 := by rw [v5 .x12 (by simp), r3, R_eq]
  have q4 : v s₅ .x13 = lim (Rk s₀.mem (s₀.gpr .x0)) 4 := by rw [v5 .x13 (by simp), r4, R_eq]
  have p1 : v s₅ .x4 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 1 := by
    rw [t1, ← v5 .x10 (by simp), q1, times5_eq (b 1 (by decide))]
  have p2 : v s₅ .x5 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 2 := by
    rw [t2, ← v5 .x11 (by simp), q2, times5_eq (b 2 (by decide))]
  have p3 : v s₅ .x6 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 3 := by
    rw [t3, ← v5 .x12 (by simp), q3, times5_eq (b 3 (by decide))]
  have p4 : v s₅ .x7 = 5 * lim (Rk s₀.mem (s₀.gpr .x0)) 4 := by
    rw [t4, ← v5 .x13 (by simp), q4, times5_eq (lt_trans b4 (by norm_num))]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, fun hlt => ?_⟩
  · rw [k₇₉.1 r (sub r hr _ (by decide)), g₆, k₁₅.1 r (sub r hr _ (by decide))]
  · rw [k₇₉.2.2.1, rd₆']
  · rw [k₇₉.2.2.2, wr₆']
  · rw [k₇₉.gpr', g₆]; exact m₅
  · rw [mem₉]; exact coefMem_frame _ _ _ _
  · rw [mem₉]
    refine coefMem_coefs _ _ _ _ _ (fun j hj => ?_) (fun j hj₁ hj => ?_)
    · obtain rfl | rfl | rfl | rfl | rfl := lt5_cases hj
      · exact coef_toNat q0 (lt32 (b 0 (by decide)))
      · exact coef_toNat q1 (lt32 (b 1 (by decide)))
      · exact coef_toNat q2 (lt32 (b 2 (by decide)))
      · exact coef_toNat q3 (lt32 (b 3 (by decide)))
      · exact coef_toNat q4 (lt32 (lt_trans b4 (by norm_num)))
    · obtain rfl | rfl | rfl | rfl := lt5_cases' hj₁ hj
      · exact coef_toNat p1 (times5_lt (b 1 (by decide)))
      · exact coef_toNat p2 (times5_lt (b 2 (by decide)))
      · exact coef_toNat p3 (times5_lt (b 3 (by decide)))
      · exact coef_toNat p4 (times5_lt (lt_trans b4 (by norm_num)))
  · have hs : ∀ d, d + 8 ≤ 56 → w64 s₈.mem (s₈.gpr .x0) d = w64 s₀.mem (s₀.gpr .x0) d := fun d hd => by
      simp only [w64]
      rw [k₇₈.2.1, k₇₈.gpr', mm₆, k₁₅.2.1, x0₆, x0₅]
      exact congrArg BitVec.toNat (coefMem_readW_low _ _ _ _ hd)
    have w0 : v s₇ .x14 = w64 s₀.mem (s₀.gpr .x0) 0 := by
      simp only [v, l₃]; rw [← hs 0 (by decide), k₇₈.2.1, k₇₈.gpr']
    have w1 : v s₇ .x15 = w64 s₀.mem (s₀.gpr .x0) 8 := by
      simp only [v, l₄]; rw [← hs 8 (by decide), k₇₈.2.1, k₇₈.gpr']
    rw [leNum_acc] at hlt ⊢
    rw [h4, w0, w1] at e4
    rw [hs 16 (by decide)] at e4
    rw [h0, w0, w1] at e0; rw [h1, w0, w1] at e1; rw [h2, w0, w1] at e2; rw [h3, w0, w1] at e3
    simp only [hv, Bounds, e0, e1, e2, e3, e4]
    exact loadH_arith (BitVec.isLt _) (BitVec.isLt _) hlt

end VG.Proof.Poly1305.AArch64
