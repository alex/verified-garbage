import VerifiedGarbage.Proof.Poly1305.Arm.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Poly1305.Arm.Reduce

section

/-!
# Poly1305 on 32-bit ARM: the columns of `h r`

Untrusted: everything here is checked by Lean. `multiply` computes the
columns `col h r` (`Arith.lean`) into `r3`–`r12`, row by row: row `j` loads
`h j` (two limbs are packed in each word at `[0, 20)`) and adds its products
with the limbs of `r` (at `rOff i`) to the columns (`mac_step`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- Limb `i` of `r` as `loadR i` loads it from the memory `m` of the state at `B`. -/
def rval (m : Mem) (B : Addr) (i : Nat) : Nat :=
  if i = 4 ∨ i = 9 then (m (B + BitVec.ofNat 64 (rOff i))).toNat
  else (m.readW (B + BitVec.ofNat 64 (rOff i)) 32).toNat

theorem rOff_lt : ∀ i < 10, rOff i + 4 ≤ 128 := by decide +kernel

/-- The bound on the limbs of `h` that are multiplied. -/
abbrev Hb : Nat := 2 ^ 13 + 2 ^ 9

theorem col_lt {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {k : Nat}
    (hk : k < 10) : col h r k ≤ 3564723200 := by
  have := col_le (h := h) (r := r) (R := 2 ^ 13 - 1) hh (fun i hi => by have := hr i hi; omega) hk
  simp only [Hb] at this
  omega

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem macCore_ok {i : Nat} (hi : i < 10) {X : Reg} (hX2 : X ≠ .r2)
    {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hb : (s.gpr X).toNat + (s.gpr .r1).toNat * rval s.mem (State.addr st) i < 2 ^ 32) :
    WP isa (.block [loadR i, .mul .r2 .r1 .r2, .dp .add X X (.reg .r2)]) s fun s' =>
      (s'.gpr X).toNat = (s.gpr X).toNat + (s.gpr .r1).toNat * rval s.mem (State.addr st) i ∧
        Keeps [.r2, X] s s' := by
  have hro := rOff_lt i hi
  have hA : State.addr (s.gpr .r0 + BitVec.ofNat 32 (rOff i)) = State.addr st + BitVec.ofNat 64 (rOff i) := by
    rw [h0]; exact ea hfit (by omega)
  have finish : ∀ s1 : State, ∀ v : BitVec 32, Upd s s1 .r2 v → v.toNat = rval s.mem (State.addr st) i →
      WP isa (.block [.mul .r2 .r1 .r2, .dp .add X X (.reg .r2)]) s1 fun s' =>
        (s'.gpr X).toNat = (s.gpr X).toNat + (s.gpr .r1).toNat * rval s.mem (State.addr st) i ∧
          Keeps [.r2, X] s s' := fun s1 v u1 hv =>
    wp_mul fun s2 u2 => wp_add (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨by
      have e1 : s1.gpr .r1 = s.gpr .r1 := u1.other _ (by decide)
      have eX : s1.gpr X = s.gpr X := u1.other _ hX2
      have hp : (s2.gpr .r2).toNat = (s.gpr .r1).toNat * rval s.mem (State.addr st) i := by
        rw [u2.gpr, u1.gpr, e1, toNat_mul_lt (by rw [hv]; omega), hv]
      rw [u3.gpr, u2.other _ hX2, eX, toNat_add_lt (by rw [hp]; exact hb), hp],
      (u1.keeps (by simp)).trans ((u2.keeps (by simp)).trans (u3.keeps (by simp)))⟩
  by_cases h49 : i = 4 ∨ i = 9
  · simp only [loadR, h49, ite_true]
    refine wp_ldrb (by omega) hA (inSt hw (by omega)) fun s1 u1 => finish s1 _ u1 ?_
    simp only [rval, h49, ite_true]
    rfl
  · simp only [loadR, h49, ite_false]
    refine wp_ldr (by omega) hA (inSt hw (by omega)) fun s1 u1 => finish s1 _ u1 ?_
    simp only [rval, h49, ite_false]

/-- In row `j`, after the products of `r i` for `i < n`, relative to the state
`s₀` in which the multiplication starts. -/
structure MI (h r : Nat → Nat) (s₀ : State) (j n : Nat) (s : State) : Prop where
  cols : ∀ k < 10, (s.gpr (xr k)).toNat = psum h r j n k
  a : (s.gpr .r1).toNat = if 0 < j ∧ 10 - j < n then 5 * h j else h j
  keeps : Keeps work s₀ s

theorem mac_step {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : stR st ∈ s₀.wr) (hR : ∀ i < 10, rval s₀.mem (State.addr st) i = r i)
    {j : Nat} (hj : j < 10) (n : Nat) (s : State) (hn : n < 10) (hs : MI h r s₀ j n s) :
    WP isa (.block (mac j n)) s (MI h r s₀ j (n + 1)) := by
  have hs0 : s.gpr .r0 = st := by rw [hs.keeps.gpr _ (by decide), h0]
  have hsw : stR st ∈ s.wr := by rw [hs.keeps.wr]; exact hw
  have hRs : rval s.mem (State.addr st) n = r n := by rw [hs.keeps.mem]; exact hR n hn
  set k₀ := (n + j) % 10 with hk₀
  have hk₀10 : k₀ < 10 := Nat.mod_lt _ (by omega)
  have hX := xr_ne k₀ hk₀10
  -- The core, from a state with `r1 = a` and the columns and memory of `s`.
  have core : ∀ s1 : State, Keeps [.r1] s s1 →
      (s1.gpr .r1).toNat = (if n + j < 10 then h j else 5 * h j) →
      (s1.gpr .r1).toNat = (if 0 < j ∧ 10 - j < n + 1 then 5 * h j else h j) →
      WP isa (.block [loadR n, .mul .r2 .r1 .r2, .dp .add (xr k₀) (xr k₀) (.reg .r2)]) s1
        (MI h r s₀ j (n + 1)) := by
    intro s1 k1 ha ha'
    have hc1 : ∀ k < 10, (s1.gpr (xr k)).toNat = psum h r j n k := fun k hk => by
      rw [k1.gpr _ (by simpa using (xr_ne k hk).2.1)]; exact hs.cols k hk
    have e := psum_step h r hj hn hk₀10
    rw [iteT hk₀] at e
    have hle := psum_le_col h r (j := j) (n := n + 1) (k := k₀) hj
    have hcol := col_lt hh hr hk₀10
    refine WP.mono (macCore_ok hfit hn hX.2.2 (by rw [k1.gpr _ (by decide), hs0])
      (by rw [k1.wr]; exact hsw) ?_) fun s2 ⟨e2, k2⟩ => ⟨fun k hk => ?_, ?_, ?_⟩
    · rw [k1.mem, hRs, hc1 _ hk₀10, ha, ← e]; omega
    · by_cases ek : k = k₀
      · subst ek; rw [e2, k1.mem, hRs, hc1 _ hk₀10, ha, e]
      · rw [k2.gpr _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨(xr_ne k hk).2.2, fun h' => ek (xr_inj _ hk _ hk₀10 h')⟩), hc1 k hk]
        have e' := psum_step h r hj hn hk (k := k)
        rw [iteF (by rw [← hk₀]; exact ek)] at e'
        exact e'.symm
    · rw [k2.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, hX.2.1.symm⟩)]; exact ha'
    · exact hs.keeps.trans ((k1.mono (by simp [work])).trans (k2.mono fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · decide
        · exact xr_work _ hk₀10))
  have hj' : h j ≤ 2 ^ 13 + 2 ^ 9 := hh j hj
  by_cases h5 : 0 < j ∧ n + j = 10
  · simp only [mac]
    rw [iteT h5, List.cons_append, List.nil_append]
    refine wp_add (op2_lsl (by omega)) fun s1 u1 => core s1 (u1.keeps (by simp)) ?_ ?_
    · have ha := hs.a
      rw [iteF (by omega)] at ha
      rw [u1.gpr, toNat_add_lt (by rw [toNat_shl, ha]; omega), toNat_shl, ha, iteF (by omega)]
      omega
    · have ha := hs.a
      rw [iteF (by omega)] at ha
      rw [u1.gpr, toNat_add_lt (by rw [toNat_shl, ha]; omega), toNat_shl, ha, iteT (by omega)]
      omega
  · simp only [mac, h5, ite_false, List.nil_append]
    refine core s (Keeps.refl _ _) ?_ ?_
    · rw [hs.a]; split <;> split <;> omega
    · rw [hs.a]; split <;> split <;> omega

/-- `h`, two limbs per word, at `[0, 20)` of the state at `B`. -/
def HMem (h : Nat → Nat) (m : Mem) (B : Addr) : Prop :=
  ∀ i < 5, (m.readW (B + BitVec.ofNat 64 (4 * i)) 32).toNat = h (2 * i) + 2 ^ 16 * h (2 * i + 1)

theorem loadH_ok {h : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) {j : Nat} (hj : j < 10) {s : State}
    (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr) (hH : HMem h s.mem (State.addr st)) :
    WP isa (.block (loadH j)) s fun s' => (s'.gpr .r1).toNat = h j ∧ Keeps [.r1] s s' := by
  have hb : ∀ j < 10, h j < 2 ^ 16 := fun j hj => by have := hh j hj; simp only [Hb] at this; omega
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  · have hw' := hH i (by omega)
    simp only [loadH, show 2 * i % 2 = 0 by omega, ite_true]
    refine wp_ldr (by omega) (by rw [h0, show 2 * (2 * i) = 4 * i by omega]; exact ea hfit (by omega))
      (inSt hw (by omega)) fun s1 u1 => wp_mov (op2_lsl (by omega)) fun s2 u2 =>
        wp_mov (op2_lsr (by omega)) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp)).trans
          ((u2.keeps (by simp)).trans (u3.keeps (by simp)))⟩
    rw [u3.gpr, u2.gpr, u1.gpr, toNat_shr, toNat_shl, hw']
    have := hb (2 * i) (by omega); have := hb (2 * i + 1) (by omega)
    omega
  · have hw' := hH i (by omega)
    simp only [loadH, show (2 * i + 1) % 2 = 1 by omega, show 1 ≠ 0 by omega, ite_false,
      show 2 * i + 1 - 1 = 2 * i by omega]
    refine wp_ldr (by omega) (by rw [h0, show 2 * (2 * i) = 4 * i by omega]; exact ea hfit (by omega))
      (inSt hw (by omega)) fun s1 u1 => wp_mov (op2_lsr (by omega)) fun s2 u2 =>
        WP.block_nil ⟨?_, (u1.keeps (by simp)).trans (u2.keeps (by simp))⟩
    rw [u2.gpr, u1.gpr, toNat_shr, hw']
    have := hb (2 * i) (by omega)
    omega

theorem row_ok {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : stR st ∈ s₀.wr) (hR : ∀ i < 10, rval s₀.mem (State.addr st) i = r i)
    (hH : HMem h s₀.mem (State.addr st)) (j : Nat) (s : State) (hj : j < 10)
    (hs : (∀ k < 10, (s.gpr (xr k)).toNat = psum h r j 0 k) ∧ Keeps work s₀ s) :
    WP isa (.block (row j)) s fun s' =>
      (∀ k < 10, (s'.gpr (xr k)).toNat = psum h r (j + 1) 0 k) ∧ Keeps work s₀ s' := by
  obtain ⟨hc, hk⟩ := hs
  rw [row]
  refine WP.append (loadH_ok hfit hh hj (by rw [hk.gpr _ (by decide), h0]) (by rw [hk.wr]; exact hw)
    (by rw [hk.mem]; exact hH)) fun s1 ⟨ha, k1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (MI h r s₀ j) (fun n s' hn hs' =>
    mac_step hfit hh hr h0 hw hR hj n s' hn hs') 10 (Nat.le_refl _) s1 ⟨fun k hk' => ?_, ?_, ?_⟩)
    fun s' hs' => ⟨fun k hk' => by rw [hs'.cols k hk', psum_row], hs'.keeps⟩
  · rw [k1.gpr _ (by simpa using (xr_ne k hk').2.1)]; exact hc k hk'
  · rw [ha, iteF (by omega)]
  · exact hk.trans (k1.mono (by simp [work]))

omit hfit in
theorem zeroX_ok {s : State} :
    WP isa (.block zeroX) s fun s' => (∀ k < 10, (s'.gpr (xr k)).toNat = 0) ∧ Keeps work s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, (s'.gpr (xr k)).toNat = 0) ∧ Keeps work s s')
    (fun n s' hn ⟨hz, hk⟩ => wp_mov (op2_imm (by decide)) fun s1 u1 => WP.block_nil ⟨fun k hk' => ?_,
      hk.trans (u1.keeps (xr_work n hn))⟩) 10 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega), Keeps.refl _ _⟩)
    fun s' h => h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
  · rw [u1.other _ (fun e => absurd (xr_inj _ (by omega) _ hn e) (by omega))]; exact hz k h'
  · rw [u1.gpr]; rfl

theorem multiply_ok {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : stR st ∈ s₀.wr) (hR : ∀ i < 10, rval s₀.mem (State.addr st) i = r i)
    (hH : HMem h s₀.mem (State.addr st)) :
    WP isa (.block multiply) s₀ fun s' =>
      (∀ k < 10, (s'.gpr (xr k)).toNat = col h r k) ∧ Keeps work s₀ s' := by
  rw [multiply]
  refine WP.append zeroX_ok fun s1 ⟨hz, k1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun j s => (∀ k < 10, (s.gpr (xr k)).toNat = psum h r j 0 k) ∧ Keeps work s₀ s)
    (fun j s hj hs => row_ok hfit hh hr h0 hw hR hH j s hj hs) 10 (Nat.le_refl _) s1
    ⟨fun k hk => by rw [hz k hk, psum_zero], k1⟩)
    fun s' ⟨hc, hk⟩ => ⟨fun k hk' => by rw [hc k hk', psum_ten], hk⟩

end

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: absorbing a block

Untrusted: everything here is checked by Lean. `absorb pad` adds the 16
bytes at `r1` (and `2¹²⁸` if `pad`) to the columns `D` (`D 0`–`D 8` in
`r3`–`r11`, `D 9` at `[16, 20)` of the state: `ColsD`), carries them into
`h`, packs `h` into `[0, 20)` and multiplies it by `r` (`absorb_ok`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)

/-- The columns `D`: `D 0`–`D 8` in `r3`–`r11`, `D 9` at `[16, 20)` of the state at `B`. -/
def ColsD (D : Nat → Nat) (B : Addr) (s : State) : Prop :=
  (∀ k < 9, (s.gpr (yr k)).toNat = D k) ∧ (s.mem.readW (B + BitVec.ofNat 64 16) 32).toNat = D 9

/-- The 128-bit number at `r1`, as `addWords` reads it. -/
def msgVal (s : State) : Nat :=
  (word s 0).toNat + 2 ^ 32 * (word s 1).toNat + 2 ^ 64 * (word s 2).toNat + 2 ^ 96 * (word s 3).toNat

/-- `s'` is `s` but for the registers `ws`, the flags and the memory in `F`. -/
structure KeepsF (ws : List Reg) (F : List Region) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  frame : Frame F s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.keepsF {ws : List Reg} {s s' : State} (h : Keeps ws s s') (F : List Region) :
    KeepsF ws F s s' := ⟨h.gpr, h.mem ▸ Frame.refl _ _, h.rd, h.wr, h.sp⟩

theorem KeepsF.trans {ws : List Reg} {F : List Region} {s₁ s₂ s₃ : State} (h₁ : KeepsF ws F s₁ s₂)
    (h₂ : KeepsF ws F s₂ s₃) : KeepsF ws F s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₁.frame.trans h₂.frame, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem KeepsF.mono {ws ws' : List Reg} {F : List Region} {s s' : State} (h : KeepsF ws F s s')
    (hs : ∀ r ∈ ws, r ∈ ws') : KeepsF ws' F s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.frame, h.rd, h.wr, h.sp⟩

/-- `[0, 20)` of the state. -/
abbrev accR (B : Addr) : Region := ⟨B, 20⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- After packing `i` words of `H`. -/
structure PI (H : Nat → Nat) (st : BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  mem : ∀ i' < i, (s.mem.readW (State.addr st + BitVec.ofNat 64 (4 * i')) 32).toNat =
    H (2 * i') + 2 ^ 16 * H (2 * i' + 1)
  cols : ∀ k < 10, 2 * i ≤ k → (s.gpr (yr k)).toNat = H k
  keeps : KeepsF work [accR (State.addr st)] s₀ s

theorem pack_step {H : Nat → Nat} (hH : ∀ k < 10, H k < 2 ^ 16) {s₀ : State} (h0 : s₀.gpr .r0 = st)
    (hw : stR st ∈ s₀.wr) (i : Nat) (s : State) (hi : i < 5) (hs : PI H st s₀ i s) :
    WP isa (.block [.dp .add (yr (2 * i)) (yr (2 * i)) (.shifted (yr (2 * i + 1)) .lsl 16),
      .str (yr (2 * i)) .r0 (4 * i)]) s (PI H st s₀ (i + 1)) := by
  have hs0 : s.gpr .r0 = st := by rw [hs.keeps.gpr _ (by decide), h0]
  have hsw : stR st ∈ s.wr := by rw [hs.keeps.wr]; exact hw
  have hne : yr (2 * i) ≠ yr (2 * i + 1) := fun e => absurd (yr_inj _ (by omega) _ (by omega) e) (by omega)
  refine wp_add (op2_lsl (by omega)) fun s1 u1 => ?_
  have hv : (s1.gpr (yr (2 * i))).toNat = H (2 * i) + 2 ^ 16 * H (2 * i + 1) := by
    have a := hs.cols (2 * i) (by omega) (Nat.le_refl _)
    have b := hs.cols (2 * i + 1) (by omega) (by omega)
    have := hH (2 * i) (by omega); have := hH (2 * i + 1) (by omega)
    rw [u1.gpr, toNat_add_lt (by rw [toNat_shl, a, b]; omega), toNat_shl, a, b]
    omega
  refine wp_str (off := 4 * i) (a := State.addr st + BitVec.ofNat 64 (4 * i)) (by omega) (by rw [u1.other _ (yr_ne' (2 * i) (by omega)).1.symm, hs0]; exact ea hfit (off := 4 * i) (by omega))
    (by rw [u1.wr]; exact outSt hsw (off := 4 * i) (n := 4) (by omega)) fun s2 u2 => WP.block_nil ⟨fun i' hi' => ?_, ?_, ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | rfl
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), u1.mem]; exact hs.mem i' h'
    · rw [Mem.readW_writeW_self32]; exact hv
  · intro k hk hk'
    rw [u2.gpr, u1.other _ (fun e => absurd (yr_inj _ hk _ (by omega) e) (by omega))]
    exact hs.cols k hk (by omega)
  · refine hs.keeps.trans ⟨fun r hr => ?_, ?_, u2.rd.trans u1.rd, u2.wr.trans u1.wr, u2.sp.trans u1.sp⟩
    · rw [u2.gpr, u1.other _ (fun e => hr (by rw [e]; exact yr_work _ (by omega)))]
    · rw [u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (contains_off (by omega) (by omega))

theorem pack_ok {H : Nat → Nat} (hH : ∀ k < 10, H k < 2 ^ 16) {s : State} (h0 : s.gpr .r0 = st)
    (hw : stR st ∈ s.wr) (hc : Cols H s) :
    WP isa (.block pack) s fun s' => HMem H s'.mem (State.addr st) ∧
      KeepsF work [accR (State.addr st)] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (PI H st s) (fun i s' hi hs => pack_step hfit hH h0 hw i s'
    hi hs) 5 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega), fun k hk _ => hc k hk,
      (Keeps.refl _ _).keepsF _⟩) fun s' h => ⟨h.mem, h.keeps⟩

end

theorem accR_disjoint (B : Addr) {a n : Nat} (ha : 20 ≤ a) (hn : a + n ≤ 128) :
    (⟨B + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (accR B) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem rval_frame {m m' : Mem} {B : Addr} (hf : Frame [accR B] m m') {i : Nat} (hi : i < 10) :
    rval m' B i = rval m B i := by
  have hro := rOff_lt i hi
  have h88 : 88 ≤ rOff i := by have : ∀ i < 10, 88 ≤ rOff i := by decide +kernel
                               exact this i hi
  simp only [rval]
  split
  · congr 1
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact accR_disjoint B (a := rOff i) (n := 1) (by omega) (by omega) _
      (Region.contains_self _ _ |>.byte (by simp)) hc
  · rw [hf.readW (r := ⟨B + BitVec.ofNat 64 (rOff i), 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]; exact accR_disjoint B (by omega) (by omega)) (by decide)]

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The columns after adding a block: `D` plus the limbs of the block and, if `pad`, `2¹²⁸`. -/
def addE (D : Nat → Nat) (w : Nat → Nat) (pad : Bool) : Nat → Nat :=
  fun k => D k + mlimb (w 0) (w 1) (w 2) (w 3) k + if k = 9 ∧ pad = true then 2 ^ 11 else 0

theorem absorb_ok (pad : Bool) {R D : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13)
    (hD : ∀ k < 10, D k ≤ 3564723200) {s : State} (h0 : s.gpr .r0 = st) (hw : stR st ∈ s.wr)
    (hRm : ∀ i < 10, rval s.mem (State.addr st) i = R i) (hc : ColsD D (State.addr st) s)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorb pad)) s fun s' => ∃ D', ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
      val D' % P = (val D + msgVal s + if pad then 2 ^ 128 else 0) * val R % P ∧
      KeepsF work [accR (State.addr st)] s s' := by
  have hw4 : ∀ i, (word s i).toNat < 2 ^ 32 := fun i => (word s i).isLt
  have hEb : ∀ k < 10, addE D (fun i => (word s i).toNat) pad k < 2 ^ 32 - 2 ^ 19 := fun k hk => by
    have := hD k hk; have := mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
    simp only [addE]; split <;> omega
  rw [absorb]
  simp only [List.append_assoc]
  refine WP.append (addWords_ok hin) fun s1 ⟨hc1, hr2, k1⟩ => ?_
  have e1 : ∀ k < 9, (s1.gpr (yr k)).toNat = addE D (fun i => (word s i).toNat) pad k := fun k hk => by
    have := hD k (by omega); have := mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
    rw [hc1 k hk, toNat_add_lt (by rw [wsum_toNat _ hk, hc.1 k hk]; omega), wsum_toNat _ hk, hc.1 k hk]
    simp only [addE, iteF (show ¬(k = 9 ∧ pad = true) by omega), Nat.add_zero]
  have hs10 : s1.gpr .r0 = st := by rw [k1.gpr _ (by decide), h0]
  have hsw1 : stR st ∈ s1.wr := by rw [k1.wr]; exact hw
  -- `addTop pad`: column 9 into `r1`.
  have top : WP isa (.block (addTop pad ++ (carryFold ++ (pack ++ (multiply ++ [.str .r12 .r0 d9Off]))))) s1
      (fun s' => ∃ D', ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
        val D' % P = (val D + msgVal s + if pad then 2 ^ 128 else 0) * val R % P ∧
        KeepsF work [accR (State.addr st)] s s') := by
    -- After `addTop`: the columns `E` in registers, the memory of `s`.
    have rest : ∀ s2 : State, Cols (addE D (fun i => (word s i).toNat) pad) s2 →
        KeepsF work [accR (State.addr st)] s s2 → s2.mem = s.mem →
        WP isa (.block (carryFold ++ (pack ++ (multiply ++ [.str .r12 .r0 d9Off])))) s2
          (fun s' => ∃ D', ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
            val D' % P = (val D + msgVal s + if pad then 2 ^ 128 else 0) * val R % P ∧
            KeepsF work [accR (State.addr st)] s s') := by
      intro s2 hc2 k2 hm2
      have hs20 : s2.gpr .r0 = st := by rw [k2.gpr _ (by decide), h0]
      obtain ⟨hv, -, hf0, hf1, hfj⟩ := fold_facts _ hEb
      have hH : ∀ k < 10, fold (addE D (fun i => (word s i).toNat) pad) k ≤ Hb := fun k hk => by
        simp only [Hb]
        rcases Nat.lt_or_ge k 2 with h | h
        · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> omega
        · have := hfj k h hk; omega
      have hH16 : ∀ k < 10, fold (addE D (fun i => (word s i).toNat) pad) k < 2 ^ 16 := fun k hk => by
        have := hH k hk; simp only [Hb] at this; omega
      refine WP.append (carryFold_ok hEb hc2) fun s3 ⟨hc3, _, k3⟩ => ?_
      have hs30 : s3.gpr .r0 = st := by rw [k3.gpr _ (by decide), hs20]
      have hw3 : stR st ∈ s3.wr := by rw [k3.wr, k2.wr]; exact hw
      refine WP.append (pack_ok hfit hH16 hs30 hw3 hc3) fun s4 ⟨hHm, k4⟩ => ?_
      have hs40 : s4.gpr .r0 = st := by rw [k4.gpr _ (by decide), hs30]
      have hw4' : stR st ∈ s4.wr := by rw [k4.wr]; exact hw3
      have hR4 : ∀ i < 10, rval s4.mem (State.addr st) i = R i := fun i hi => by
        rw [rval_frame k4.frame hi, k3.mem, hm2]; exact hRm i hi
      refine WP.append (multiply_ok hfit hH hR hs40 hw4' hR4 hHm) fun s5 ⟨hx5, k5⟩ => ?_
      have hs50 : s5.gpr .r0 = st := by rw [k5.gpr _ (by decide), hs40]
      refine wp_str (off := d9Off) (a := State.addr st + BitVec.ofNat 64 16) (by decide)
        (by rw [hs50]; exact ea hfit (off := 16) (by omega))
        (by rw [k5.wr]; exact outSt hw4' (off := 16) (n := 4) (by omega)) fun s6 u6 => WP.block_nil ?_
      refine ⟨col (fold (addE D (fun i => (word s i).toNat) pad)) R, ⟨fun k hk => ?_, ?_⟩,
        fun k hk => col_lt hH hR hk, ?_, ?_⟩
      · rw [u6.gpr, yr_eq_xr k hk]; exact hx5 k (by omega)
      · rw [u6.mem, Mem.readW_writeW_self32]; exact hx5 9 (by omega)
      · rw [val_col, Nat.mul_mod, hv, ← Nat.mul_mod]
        refine congrArg (· % P) (congrArg (· * val R) ?_)
        have hm := val_mlimb (hw4 0) (hw4 1) (hw4 2) (hw4 3)
        simp only [val, addE, msgVal] at hm ⊢
        cases pad <;> simp <;> omega
      · have k6 : KeepsF work [accR (State.addr st)] s5 s6 := by
          refine ⟨fun r _ => by rw [u6.gpr], ?_, u6.rd, u6.wr, u6.sp⟩
          rw [u6.mem]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
        exact k2.trans (((k3.keepsF _).mono (by simp [work, cregs, yregs])).trans (k4.trans
          ((k5.keepsF _).trans k6)))
    rw [addTop]
    simp only [List.append_assoc, List.cons_append]
    refine wp_ldr (off := d9Off) (a := State.addr st + BitVec.ofNat 64 16) (by decide)
      (by rw [hs10]; exact ea hfit (off := 16) (by omega)) (inSt hsw1 (off := 16) (n := 4) (by omega))
      fun s2 u2 => wp_add (op2_lsr (by omega)) fun s3 u3 => ?_
    have hD9 := hD 9 (by omega)
    have v3 : (s3.gpr .r1).toNat = D 9 + (word s 3).toNat / 2 ^ 21 := by
      have e2 : (s2.gpr .r1).toNat = D 9 := by rw [u2.gpr, k1.mem]; exact hc.2
      rw [u3.gpr, u2.other .r2 (by decide), hr2, toNat_add_lt (by rw [e2, toNat_shr]; have := hw4 3; omega),
        e2, toNat_shr]
    have k3 : KeepsF work [accR (State.addr st)] s s3 :=
      (k1.keepsF _).mono (by simp [work, yregs]) |>.trans
        (((u2.keeps (ws := [.r1]) (by simp)).trans (u3.keeps (by simp))).keepsF _ |>.mono (by simp [work]))
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, k1.mem]
    have c3 : ∀ j < 9, (s3.gpr (yr j)).toNat = addE D (fun i => (word s i).toNat) pad j := fun j hj => by
      rw [u3.other _ (yr_ne j hj).2.1, u2.other _ (yr_ne j hj).2.1]; exact e1 j hj
    cases pad
    · simp only [Bool.false_eq_true, ite_false, List.nil_append]
      refine rest s3 (fun j hj => ?_) k3 m3
      rcases Nat.lt_or_ge j 9 with h | h
      · exact c3 j h
      · rw [show j = 9 by omega, yr9, v3]; simp [addE, mlimb]
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine wp_add (op2_imm (by decide)) fun s4 u4 => rest s4 (fun j hj => ?_)
        (k3.trans ((u4.keeps (ws := [.r1]) (by simp)).keepsF _ |>.mono (by simp [work]))) (by rw [u4.mem, m3])
      rcases Nat.lt_or_ge j 9 with h | h
      · rw [u4.other _ (yr_ne j h).2.1]; exact c3 j h
      · have e2048 : (2048 : BitVec 32).toNat = 2048 := rfl
        rw [show j = 9 by omega, yr9, u4.gpr, toNat_add_lt (by rw [v3, e2048]; have := hw4 3; omega), v3,
          e2048]
        simp [addE, mlimb]
  exact top

end

end VG.Proof.Poly1305.Arm
