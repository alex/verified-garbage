import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_rej_ntt_poly`

Untrusted: everything here is checked by Lean. The 336 iterations of the
loop on the 1008 bytes `X` at `bP` store the coefficients that `rnFold`
samples from them at `aP` (`loop_ok`): iteration `t` starts from `LAt t`,
with those of the first `3t` bytes stored. A coefficient is stored as
coefficient `j` whether it is accepted or not (`Stored` constrains only the
first `j`). The loop reads only the output, and writes only `a`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample.RejNtt

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_movk1 wp_addImm wp_subImm wp_strw
  wp_ldrb wp_sub wp_add wp_lsr wp_lsl wp_and ptr_zero ptr_add toNat_sub_n toNat_add_n toNat_lsl_n
  toNat_and_mask toNat_byte toNat_lsr count_loop eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (coeffAt Zq q)
open VG.Spec.Sha3 (bytesAt)

/-- What the loop needs of the state it starts from: the 1008 bytes `X` at
`bP = x25 + 840`, which it may read, and `a` at `aP = x26`, which it may
write. -/
structure LPre (X : List Byte) (bP aP : Addr) (s : State) : Prop where
  buf : ∀ p < 1008, s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0
  inb : ∀ p < 1008, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 1008⟩ : Region).Disjoint (polyR aP)
  x25 : s.gpr .x25 + BitVec.ofNat 64 840 = bP
  x26 : s.gpr .x26 = aP

/-- The coefficients sampled from the first `3t` bytes. -/
abbrev Lt (X : List Byte) (t : Nat) : List Zq := rnFold [] (X.take (3 * t))

theorem Lt_length_le (X : List Byte) (t : Nat) : (Lt X t).length ≤ 256 := rnFold_length_le (by simp) _

/-- The registers the loop writes. -/
abbrev lRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15]

/-- At the start of iteration `t`, from the loop's entry state `s₀`. -/
structure LAt (X : List Byte) (bP aP : Addr) (s₀ : State) (t : Nat) (s : State) : Prop where
  keep : Keep lRegs s₀ s
  frame : Frame [polyR aP] s₀.mem s.mem
  x2 : s.gpr .x2 = bP + BitVec.ofNat 64 (3 * t)
  x3 : s.gpr .x3 = coeffAddr aP (Lt X t).length
  x4 : (s.gpr .x4).toNat = 256 - (Lt X t).length
  x5 : (s.gpr .x5).toNat = 336 - t
  x9 : (s.gpr .x9).toNat = q
  x10 : (s.gpr .x10).toNat = 127
  st : Stored s.mem aP (Lt X t)

theorem q_eq : q = 8380417 := rfl

/-- The byte `p` of the output, in any state of the loop. -/
theorem LAt.byte {X : List Byte} {bP aP : Addr} {s₀ : State} (hp : LPre X bP aP s₀) {t : Nat} {s : State}
    (h : LAt X bP aP s₀ t s) {p : Nat} (hp' : p < 1008) : s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0 := by
  rw [← hp.buf p hp']
  exact h.frame _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.disj _ (Offset.contains_base _ (by omega) (by omega))

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

/-- `v - b` of numbers below `2⁶³`, negative exactly when `v < b`. -/
theorem lt_bit {a b : BitVec 64} {v w : Nat} (ha : a.toNat = v) (hb : b.toNat = w) (hv : v < 2 ^ 63)
    (hw : w < 2 ^ 63) : ((a - b) >>> 63).toNat = if v < w then 1 else 0 := by
  rw [toNat_lsr, BitVec.toNat_sub, ha, hb]
  split <;> omega

/-- A coefficient stored past the ones sampled keeps them. -/
theorem stored_past {m : Mem} {p : Addr} {L : List Zq} (h : Stored m p L) {k : Nat} (hk : L.length ≤ k)
    (hk' : k < 256) (v : BitVec 32) : Stored (m.writeW (coeffAddr p k) v) p L := fun i hi => by
  rw [coeffAt_writeW _ _ (by omega) hk', ite_eq_right (by omega)]
  exact h i hi

/-- The value of the 3 bytes `b₀, b₁, b₂` at `x2` into `x11`. -/
theorem chunk_ok {s : State} {b₀ b₁ b₂ : Byte}
    (h₀ : s.mem (s.gpr .x2) = b₀) (h₁ : s.mem (s.gpr .x2 + 1) = b₁) (h₂ : s.mem (s.gpr .x2 + 2) = b₂)
    (i₀ : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1) (i₁ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + 1) 1)
    (i₂ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + 2) 1) (h10 : (s.gpr .x10).toNat = 127) :
    WP isa (.block rnChunk) s fun s' => Only [.x6, .x7, .x8, .x2, .x5, .x11] s s' ∧
      s'.gpr .x2 = s.gpr .x2 + 3 ∧ s'.gpr .x5 = s.gpr .x5 - 1 ∧ (s'.gpr .x11).toNat = rnZ b₀ b₁ b₂ := by
  refine wp_ldrb (a := s.gpr .x2) (by decide) (ptr_zero _) i₀ fun s₁ o₁ e₁ => ?_
  refine wp_ldrb (a := s.gpr .x2 + 1) (by decide) (by rw [o₁.get .x2]; rfl) (by rw [o₁.rd, o₁.wr]; exact i₁)
    fun s₂ o₂ e₂ => ?_
  refine wp_ldrb (a := s.gpr .x2 + 2) (by decide) (by rw [o₂.get .x2, o₁.get .x2]; rfl)
    (by rw [o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact i₂) fun s₃ o₃ e₃ => ?_
  refine wp_addImm (by decide) fun s₄ o₄ e₄ => wp_subImm (by decide) fun s₅ o₅ e₅ => wp_and fun s₆ o₆ e₆ =>
    wp_lsl (by decide) fun s₇ o₇ e₇ => wp_lsl (by decide) fun s₈ o₈ e₈ => wp_add fun s₉ o₉ e₉ =>
    wp_add fun s₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k := (((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans
    o₉).trans o₁₀).mono (rs' := [.x6, .x7, .x8, .x2, .x5, .x11]) (by decide)
  have hb : b₀.toNat < 256 := b₀.isLt
  have hb1 : b₁.toNat < 256 := b₁.isLt
  have hb2 : b₂.toNat < 256 := b₂.isLt
  have v6 : (s₈.gpr .x6).toNat = b₀.toNat := by
    rw [o₈.get .x6, o₇.get .x6, o₆.get .x6, o₅.get .x6, o₄.get .x6, o₃.get .x6, o₂.get .x6, e₁,
      toNat_byte, h₀]
  have c7 : (s₇.gpr .x7).toNat = b₁.toNat := by
    rw [o₇.get .x7, o₆.get .x7, o₅.get .x7, o₄.get .x7, o₃.get .x7, e₂, toNat_byte, o₁.mem, h₁]
  have v7 : (s₈.gpr .x7).toNat = 256 * b₁.toNat := by
    have hl : (s₇.gpr .x7).toNat * 2 ^ 8 < 2 ^ 64 := by rw [c7]; simp only [Nat.reducePow]; omega
    rw [e₈, toNat_lsl_n hl, c7]
    omega
  have v8a : (s₆.gpr .x8).toNat = b₂.toNat % 128 := by
    have m : (s₅.gpr .x10).toNat = 2 ^ 7 - 1 := by
      rw [o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, o₁.get .x10, h10]
    rw [e₆, toNat_and_mask _ _ m, o₅.get .x8, o₄.get .x8, e₃, toNat_byte, o₂.mem, o₁.mem, h₂]
  have v8 : (s₇.gpr .x8).toNat = 65536 * (b₂.toNat % 128) := by
    have hl : (s₆.gpr .x8).toNat * 2 ^ 16 < 2 ^ 64 := by rw [v8a]; simp only [Nat.reducePow]; omega
    rw [e₇, toNat_lsl_n hl, v8a]
    omega
  refine ⟨k, by rw [o₁₀.get .x2, o₉.get .x2, o₈.get .x2, o₇.get .x2, o₆.get .x2, o₅.get .x2, e₄,
    o₃.get .x2, o₂.get .x2, o₁.get .x2]; rfl,
    by rw [o₁₀.get .x5, o₉.get .x5, o₈.get .x5, o₇.get .x5, o₆.get .x5, e₅, o₄.get .x5, o₃.get .x5,
      o₂.get .x5, o₁.get .x5]; rfl, ?_⟩
  have v11 : (s₉.gpr .x11).toNat = b₀.toNat + 256 * b₁.toNat := by
    rw [e₉, toNat_add_n (by rw [v6, v7]; omega), v6, v7]
  rw [e₁₀, toNat_add_n (by rw [v11, o₉.get .x8, o₈.get .x8, v8]; omega), v11, o₉.get .x8, o₈.get .x8, v8]
  unfold rnZ; omega


/-- The coefficients after trying the value `z`. -/
abbrev acc (L : List Zq) (z : Nat) : List Zq := if z < q then L ++ [Fin.ofNat q z] else L

theorem acc_length (L : List Zq) (z : Nat) : (acc L z).length = L.length + if z < q then 1 else 0 := by
  unfold acc; split <;> simp

/-- Storing `x11` as coefficient `j`, and counting it if it is less than
`q`. -/
theorem accept_ok {aP : Addr} {L : List Zq} {z : Nat} {u : State} (hz : (u.gpr .x11).toNat = z)
    (hz' : z < 2 ^ 23) (h9 : (u.gpr .x9).toNat = q) (h3 : u.gpr .x3 = coeffAddr aP L.length)
    (h4 : (u.gpr .x4).toNat = 256 - L.length) (hl : L.length < 256) (hst : Stored u.mem aP L)
    (hw : InRegions u.wr (coeffAddr aP L.length) 4) :
    WP isa (.block rnAccept) u fun u' => Keep [.x3, .x4, .x13, .x14, .x15] u u' ∧
      Frame [polyR aP] u.mem u'.mem ∧ u'.gpr .x3 = coeffAddr aP (acc L z).length ∧
      (u'.gpr .x4).toNat = 256 - (acc L z).length ∧ Stored u'.mem aP (acc L z) := by
  refine wp_sub fun u₁ h₁ e₁ => wp_lsr (by decide) fun u₂ h₂ e₂ => ?_
  have v14 : (u₂.gpr .x14).toNat = if z < q then 1 else 0 := by
    rw [e₂, e₁]; exact lt_bit hz h9 (by omega) (by rw [q_eq]; omega)
  refine wp_strw (a := coeffAddr aP L.length) (by decide)
    (by rw [h₂.get .x3, h₁.get .x3, h3, ptr_zero]) (by rw [h₂.wr, h₁.wr]; exact hw) fun u₃ h₃ =>
    wp_lsl (by decide) fun u₄ h₄ e₄ => wp_add fun u₅ h₅ e₅ => wp_sub fun u₆ h₆ e₆ => wp_nil ?_
  have k₆ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).mono (rs' := [.x3, .x4, .x13, .x14, .x15]) (by decide)
  have m₆ : u₆.mem = u.mem.writeW (coeffAddr aP L.length) ((u.gpr .x11).setWidth 32) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.get .x11, h₁.get .x11, h₂.mem, h₁.mem]
  have x14 : u₅.gpr .x14 = u₂.gpr .x14 := by rw [h₅.get .x14, h₄.get .x14, h₃.gpr]
  have x15 : u₄.gpr .x15 = BitVec.ofNat 64 (4 * if z < q then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    have hl : (u₃.gpr .x14).toNat * 2 ^ 2 < 2 ^ 64 := by rw [h₃.gpr, v14]; split <;> decide
    rw [e₄, toNat_lsl_n hl, h₃.gpr, v14, BitVec.toNat_ofNat]
    split <;> decide
  have c4 : (u₅.gpr .x4).toNat = 256 - L.length := by
    rw [h₅.get .x4, h₄.get .x4, h₃.gpr, h₂.get .x4, h₁.get .x4, h4]
  refine ⟨k₆, ?_, ?_, ?_, ?_⟩
  · rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hl)
  · rw [h₆.get .x3, e₅, h₄.get .x3, h₃.gpr, h₂.get .x3, h₁.get .x3, h3, x15, coeffAddr, coeffAddr,
      ptr_add, acc_length, Nat.mul_add]
  · have hx : (u₅.gpr .x14).toNat ≤ (u₅.gpr .x4).toNat := by rw [x14, v14, c4]; split <;> omega
    rw [e₆, toNat_sub_n hx, c4, x14, v14, acc_length]
    omega
  · rw [m₆]
    unfold acc
    split
    · rename_i hq
      have hw : (u.gpr .x11).setWidth 32 = zw (Fin.ofNat q z) := by
        apply BitVec.eq_of_toNat_eq
        rw [zw_toNat, BitVec.toNat_setWidth, hz, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt hq]
      rw [hw]; exact stored_snoc hst hl _
    · exact stored_past hst (Nat.le_refl _) hl _

/-- An iteration, from `LAt t`. -/
theorem step_ok {X : List Byte} (hX : X.length = 1008) {bP aP : Addr} {s₀ : State} (hp : LPre X bP aP s₀)
    {t : Nat} (ht : t < 336) {s : State} (h : LAt X bP aP s₀ t s) :
    WP isa rnBody s fun s' => LAt X bP aP s₀ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 336) := by
  have hin : ∀ k < 3, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 k) 1 := fun k hk => by
    rw [h.keep.rd, h.keep.wr, h.x2, ptr_add]; exact hp.inb _ (by omega)
  have hb : ∀ k < 3, s.mem (s.gpr .x2 + BitVec.ofNat 64 k) = X.getD (3 * t + k) 0 := fun k hk => by
    rw [h.x2, ptr_add]; exact h.byte hp (by omega)
  have e0 : s.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 0 := (ptr_zero _).symm
  have hL : Lt X (t + 1) = rnStep (Lt X t) (X.getD (3 * t) 0) (X.getD (3 * t + 1) 0) (X.getD (3 * t + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (t + 1) = 3 * t + 3 by omega, take_add_three _ (by rw [hX]; omega),
      rnFold_snoc _ (by rw [List.length_take, hX]; omega)]
  refine WP.seq (WP.mono (chunk_ok (b₀ := X.getD (3 * t) 0) (b₁ := X.getD (3 * t + 1) 0)
    (b₂ := X.getD (3 * t + 2) 0) (by rw [e0, hb 0 (by omega)]; rfl) (hb 1 (by omega)) (hb 2 (by omega))
    (by rw [e0]; exact hin 0 (by omega)) (hin 1 (by omega)) (hin 2 (by omega)) h.x10)
    fun s₁ ⟨o₁, x2, x5, x11⟩ => ?_)
  have hz : rnZ (X.getD (3 * t) 0) (X.getD (3 * t + 1) 0) (X.getD (3 * t + 2) 0) < 2 ^ 23 := by
    unfold rnZ
    have := (X.getD (3 * t) 0).isLt
    have := (X.getD (3 * t + 1) 0).isLt
    simp only [Nat.reducePow] at *
    omega
  have g3 : s₁.gpr .x3 = s.gpr .x3 := o₁.get .x3
  have g4 : s₁.gpr .x4 = s.gpr .x4 := o₁.get .x4
  have g9 : s₁.gpr .x9 = s.gpr .x9 := o₁.get .x9
  have g10 : s₁.gpr .x10 = s.gpr .x10 := o₁.get .x10
  have n2 : s₁.gpr .x2 = bP + BitVec.ofNat 64 (3 * (t + 1)) := by
    rw [x2, h.x2, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, ptr_add, Nat.mul_succ]
  have n5 : (s₁.gpr .x5).toNat = 336 - (t + 1) := by
    rw [x5, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have c : (s₁.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 336 := by rw [n5]; omega
  have hl := Lt_length_le X t
  by_cases hf : (Lt X t).length = 256
  · refine WP.ite true (by rw [eval_zero, eq_zero_iff, g4, h.x4, hf]; rfl) (fun _ => wp_nil ?_)
      (fun h => nomatch h)
    have e : Lt X (t + 1) = Lt X t := by
      rw [hL, rnStep, ite_eq_right (by simp only [VG.Spec.MlDsa.n]; omega)]
    exact ⟨⟨(h.keep.trans o₁.keep).mono, by rw [o₁.mem]; exact h.frame, n2, by rw [e, g3, h.x3],
      by rw [e, g4, h.x4], n5, by rw [g9, h.x9], by rw [g10, h.x10],
      by rw [e, o₁.mem]; exact h.st⟩, c⟩
  · refine WP.ite false (by rw [eval_zero, eq_zero_iff, g4, h.x4]; simp; omega)
      (fun h => nomatch h) (fun _ => WP.mono (accept_ok (L := Lt X t) (aP := aP) x11 hz (by rw [g9, h.x9])
        (by rw [g3, h.x3]) (by rw [g4, h.x4]) (by omega) (by rw [o₁.mem]; exact h.st)
        (by rw [o₁.wr, h.keep.wr]; exact hp.ina _ (by omega))) fun s₂ ⟨k₂, f₂, x3, x4, st⟩ => ?_)
    have e : acc (Lt X t) (rnZ (X.getD (3 * t) 0) (X.getD (3 * t + 1) 0) (X.getD (3 * t + 2) 0)) =
        Lt X (t + 1) := by
      rw [hL, rnStep, ite_eq_left (by simp only [VG.Spec.MlDsa.n]; omega)]
    rw [e] at x3 x4 st
    exact ⟨⟨((h.keep.trans o₁.keep).trans k₂).mono, h.frame.trans (by rw [← o₁.mem]; exact f₂),
      by rw [k₂.get .x2, n2], x3, x4, by rw [k₂.get .x5, n5], by rw [k₂.get .x9, g9, h.x9],
      by rw [k₂.get .x10, g10, h.x10], st⟩, by rw [k₂.get .x5]; exact c⟩


/-- `q` into `r`. -/
theorem movQ_ok {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → (s'.gpr r).toNat = q → WP isa (.block is) s' Q) :
    WP isa (.block (movQ r ++ is)) s Q := by
  refine wp_movz fun s₁ h₁ e₁ => wp_movk1 fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono fun _ h => by
    simp only [List.mem_append, List.mem_singleton, or_self] at h; simp [h]) ?_
  rw [e₂, e₁]; rfl

/-- The 336 iterations, from the loop's setup: the coefficients `rnFold`
samples from the 1008 bytes stored. -/
theorem loop_ok {X : List Byte} (hX : X.length = 1008) {bP aP : Addr} {s₀ : State} (hp : LPre X bP aP s₀) :
    WP isa rnLoop s₀ (LAt X bP aP s₀ 336) := by
  refine WP.seq (wp_addImm (by decide) fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => movQ_ok fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_)
  have k₆ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep)
  have m₆ : s₆.mem = s₀.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have i₀ : LAt X bP aP s₀ 0 s₆ := ⟨k₆.mono, by rw [m₆]; exact Frame.refl _ _,
    by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁, hp.x25, Nat.mul_zero, ptr_zero],
    by rw [h₆.get .x3, h₅.get .x3, h₄.get .x3, h₃.get .x3, e₂, h₁.get .x26, hp.x26]
       simp [coeffAddr, Lt, rnFold],
    by rw [h₆.get .x4, h₅.get .x4, h₄.get .x4, e₃]; simp [Lt, rnFold],
    by rw [h₆.get .x5, h₅.get .x5, e₄]; rfl, by rw [h₆.get .x9, e₅],
    by rw [e₆]; rfl, by simp only [Lt, Nat.mul_zero, List.take_zero, rnFold]; exact stored_nil _ _⟩
  exact count_loop (by decide) (LAt X bP aP s₀) (fun t ht s h => step_ok hX hp ht h) i₀

/-- The coefficients sampled from the 1008 bytes, after the loop. -/
theorem Lt_336 {X : List Byte} (hX : X.length = 1008) : Lt X 336 = rnFold [] X := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [hX])]

end VG.Proof.MlDsa.AArch64.Sample.RejNtt
