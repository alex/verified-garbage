import VerifiedGarbage.Proof.Poly1305.Arm.Common

/-!
# Poly1305 on 32-bit ARM: the columns of `h r`

Untrusted: everything here is checked by Lean. `multiply` computes the
columns `col h r` (`Arith.lean`) into `r3`–`r12`, row by row: row `j` loads
`h j` (two limbs are packed in each word at `[0, 20)`) and adds its products
with the limbs of `r` (at `rOff i`) to the columns (`mac_step`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- Limb `i` of `r` as `loadR i` loads it from the memory `m` of the state at `B`. -/
def rval (m : Mem) (B : Addr) (i : Nat) : Nat :=
  if i = 4 ∨ i = 9 then (m (B + BitVec.ofNat 64 (rOff i))).toNat
  else (m.readW (B + BitVec.ofNat 64 (rOff i)) 32).toNat

theorem rOff_lt : ∀ i < 10, rOff i + 4 ≤ 128 := by decide

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
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · have hw' := hH i (by omega)
    simp only [loadH, show 2 * i % 2 = 0 by omega, ite_true]
    refine wp_ldr (by omega) (by rw [h0, show 2 * (2 * i) = 4 * i by ring]; exact ea hfit (by omega))
      (inSt hw (by omega)) fun s1 u1 => wp_mov (op2_lsl (by omega)) fun s2 u2 =>
        wp_mov (op2_lsr (by omega)) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp)).trans
          ((u2.keeps (by simp)).trans (u3.keeps (by simp)))⟩
    rw [u3.gpr, u2.gpr, u1.gpr, toNat_shr, toNat_shl, hw']
    have := hb (2 * i) (by omega); have := hb (2 * i + 1) (by omega)
    omega
  · have hw' := hH i (by omega)
    simp only [loadH, show (2 * i + 1) % 2 = 1 by omega, show 1 ≠ 0 by omega, ite_false,
      show 2 * i + 1 - 1 = 2 * i by omega]
    refine wp_ldr (by omega) (by rw [h0, show 2 * (2 * i) = 4 * i by ring]; exact ea hfit (by omega))
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
    mac_step hfit hh hr h0 hw hR hj n s' hn hs') 10 le_rfl s1 ⟨fun k hk' => ?_, ?_, ?_⟩)
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
      hk.trans (u1.keeps (xr_work n hn))⟩) 10 le_rfl s ⟨fun _ h => absurd h (by omega), Keeps.refl _ _⟩)
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
    (fun j s hj hs => row_ok hfit hh hr h0 hw hR hH j s hj hs) 10 le_rfl s1
    ⟨fun k hk => by rw [hz k hk, psum_zero], k1⟩)
    fun s' ⟨hc, hk⟩ => ⟨fun k hk' => by rw [hc k hk', psum_ten], hk⟩

end

end VG.Proof.Poly1305.Arm
