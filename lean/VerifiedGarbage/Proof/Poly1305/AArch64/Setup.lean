import VerifiedGarbage.Proof.Poly1305.AArch64.Steps
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

section

/-!
# Poly1305 on AArch64: absorbing a block

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

/-- The coefficient of `hi` in `dk`: `r(k-i)` or `5 r(k+5-i)`, for the limbs of `R`. -/
def cval (R k i : Nat) : Nat := if i ≤ k then lim R (k - i) else 5 * lim R (k + 5 - i)

/-- The coefficients stored in the state at `st`, for the clamped `R`. -/
def Coefs (m : Mem) (st : Addr) (R : Nat) : Prop :=
  ∀ k < 5, ∀ i < 5, (m.readW (st + BitVec.ofNat 64 (coef k i)) 32).toNat = cval R k i

/-- The coefficient words may be read. -/
def CoefIn (s : State) : Prop :=
  ∀ off, 72 ≤ off → off + 4 ≤ 108 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 4

/-- `dk`, from the limbs of `h` in `s`. -/
def dform (s : State) (R k : Nat) : Nat :=
  v s .x4 * cval R k 0 + ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * cval R k (i + 1)).sum

theorem dreg_facts : ∀ k < 5, ∀ j < 5, j ≠ k → D.getD j .x9 ≠ D.getD k .x9 ∧ D.getD j .x9 ≠ .x14 := by
  decide

theorem hreg_facts : ∀ i < 5, H.getD i .x4 ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14] := by decide +kernel

theorem dreg_mem : ∀ n < 5, D.getD n .x9 ∈ [Reg.x9, .x10, .x11, .x12, .x13, .x14] := by decide +kernel

theorem prods_ok (s : State) (R : Nat) (hco : Coefs s.mem (s.gpr .x0) R) (hc : CoefIn s) :
    ∀ n ≤ 5, WP isa (.block ((List.range n).flatMap dsum)) s fun s' =>
      (∀ k < n, v s' (D.getD k .x9) = dform s R k % 2 ^ 64) ∧
      Keeps [.x9, .x10, .x11, .x12, .x13, .x14] s s' := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun k hk => absurd hk (by omega), Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.gpr'
    have hc₁ : CoefIn s₁ := fun off h₁ h₂ => by
      rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact hc off h₁ h₂
    refine WP.mono (dsum_ok s₁ (by omega) hc₁) fun s₂ ⟨e₂, k₂⟩ => ⟨fun k hk => ?_, ?_⟩
    · have hH : ∀ i < 5, v s₁ (H.getD i .x4) = v s (H.getD i .x4) := fun i hi => by
        simp only [v]
        rw [k₁.1 _ (hreg_facts i hi)]
      have hW : ∀ i < 5, word s₁ (coef n i) = cval R n i := fun i hi => by
        simp only [word, x0₁, k₁.2.1]; exact hco n (by omega) i hi
      by_cases hkn : k = n
      · subst hkn
        have h0 : v s₁ .x4 = v s .x4 := hH 0 (by omega)
        have hs : ((List.range 4).map fun i => v s₁ (H.getD (i + 1) .x4) * word s₁ (coef k (i + 1))) =
            ((List.range 4).map fun i => v s (H.getD (i + 1) .x4) * cval R k (i + 1)) := by
          refine List.map_congr_left fun i hi => ?_
          have hi := List.mem_range.mp hi
          rw [hW (i + 1) (by omega), hH (i + 1) (by omega)]
        rw [e₂, hW 0 (by omega), h0, hs, dform]
      · obtain ⟨g1, g2⟩ := dreg_facts n (by omega) k (by omega) hkn
        rw [show v s₂ (D.getD k .x9) = v s₁ (D.getD k .x9) by
          simp only [v]; rw [k₂.1 _ (not_mem2 g2 g1)]]
        exact e₁ k (by omega)
    · refine (k₁.trans k₂).mono fun r hr => ?_
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp
        · exact dreg_mem n (by omega)

section
variable (s : State) (R : Nat)
theorem dform0 : dform s R 0 = v s .x4 * lim R 0 + (v s .x5 * (5 * lim R 4) +
    (v s .x6 * (5 * lim R 3) + (v s .x7 * (5 * lim R 2) + (v s .x8 * (5 * lim R 1) + 0)))) := rfl
theorem dform1 : dform s R 1 = v s .x4 * lim R 1 + (v s .x5 * lim R 0 +
    (v s .x6 * (5 * lim R 4) + (v s .x7 * (5 * lim R 3) + (v s .x8 * (5 * lim R 2) + 0)))) := rfl
theorem dform2 : dform s R 2 = v s .x4 * lim R 2 + (v s .x5 * lim R 1 +
    (v s .x6 * lim R 0 + (v s .x7 * (5 * lim R 4) + (v s .x8 * (5 * lim R 3) + 0)))) := rfl
theorem dform3 : dform s R 3 = v s .x4 * lim R 3 + (v s .x5 * lim R 2 +
    (v s .x6 * lim R 1 + (v s .x7 * lim R 0 + (v s .x8 * (5 * lim R 4) + 0)))) := rfl
theorem dform4 : dform s R 4 = v s .x4 * lim R 4 + (v s .x5 * lim R 3 +
    (v s .x6 * lim R 2 + (v s .x7 * lim R 1 + (v s .x8 * lim R 0 + 0)))) := rfl
end

theorem products_ok (s : State) (R : Nat) (hco : Coefs s.mem (s.gpr .x0) R) (hc : CoefIn s) :
    WP isa (.block products) s fun s' =>
      v s' .x9 = dform s R 0 % 2 ^ 64 ∧ v s' .x10 = dform s R 1 % 2 ^ 64 ∧
      v s' .x11 = dform s R 2 % 2 ^ 64 ∧ v s' .x12 = dform s R 3 % 2 ^ 64 ∧
      v s' .x13 = dform s R 4 % 2 ^ 64 ∧ Keeps [.x9, .x10, .x11, .x12, .x13, .x14] s s' :=
  WP.mono (prods_ok s R hco hc 5 (Nat.le_refl _)) fun _ ⟨e, k⟩ =>
    ⟨e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), k⟩

/-- `h += 2¹²⁸` if `pad`. -/
theorem padOpt_ok (s : State) (pad : Bool) :
    WP isa (.block (if pad then padBit else [])) s fun s' =>
      v s' .x8 = (v s .x8 + 2 ^ 24 * pad.toNat) % 2 ^ 64 ∧ Keeps [.x8, .x16] s s' := by
  cases pad
  · show WP isa (.block []) s _
    refine WP.block_nil ⟨?_, Keeps.refl _ _⟩
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, v]
    exact (Nat.mod_eq_of_lt (s.gpr .x8).isLt).symm
  · show WP isa (.block padBit) s _
    exact WP.mono (padBit_ok s) fun s' ⟨e, k⟩ => ⟨by rw [e]; rfl, k⟩

/-- The limbs of `h` between blocks. -/
def Bounds (s : State) : Prop :=
  v s .x4 < 2 ^ 26 ∧ v s .x5 < 2 ^ 27 ∧ v s .x6 < 2 ^ 26 ∧ v s .x7 < 2 ^ 26 ∧ v s .x8 < 2 ^ 26

/-- `h`, from its limbs. -/
abbrev hv (s : State) : Nat := val5 (v s .x4) (v s .x5) (v s .x6) (v s .x7) (v s .x8)

/-- The registers `absorb` writes. -/
abbrev absorbRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16]

/-- The 64-bit word at `p + d`, as a number. -/
abbrev w64 (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

theorem absorb_eq (pad : Bool) : absorb pad = load2 .x1 0 ++ (split ++ (addLimbs ++
    ((if pad then padBit else []) ++ (products ++ carry)))) := by
  simp only [absorb, addBlock, List.append_assoc]

/-- Absorbing the block at `x1`: from `h` within `Bounds`, the new `h` is
congruent to `(h + m + pad · 2¹²⁸) R` modulo `p`, and within `Bounds`. -/
theorem absorb_ok (s : State) (pad : Bool) {R : Nat} (hR : R < 2 ^ 128) (hm : s.gpr .x17 = M26)
    (hco : Coefs s.mem (s.gpr .x0) R) (hc : CoefIn s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (0 + 8)) 8) :
    WP isa (.block (absorb pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (w64 s.mem (s.gpr .x1) 0 + 2 ^ 64 * w64 s.mem (s.gpr .x1) 8 +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps absorbRegs s s' := by
  rw [absorb_eq]
  refine WP.block_append (WP.mono (load2_ok s (by decide) (by decide) (by decide) h0 h8)
    fun s₁ ⟨l1, l2, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₁ (by rw [k₁.gpr']; exact hm))
    fun s₂ ⟨m0, m1, m2, m3, m4, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (addLimbs_ok s₂) fun s₃ ⟨a0, a1, a2, a3, a4, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (padOpt_ok s₃ pad) fun s₄ ⟨p4, k₄⟩ => ?_)
  have k₁₄ := ((k₁.trans k₂).trans k₃).trans k₄
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 := k₁₄.gpr'
  refine WP.block_append (WP.mono (products_ok s₄ R (by rw [k₁₄.2.1, x0₄]; exact hco)
    (fun off h₁ h₂ => by rw [k₁₄.2.2.1, k₁₄.2.2.2, x0₄]; exact hc off h₁ h₂))
    fun s₅ ⟨d0, d1, d2, d3, d4, k₅⟩ => ?_)
  refine WP.mono (carry_ok s₅ (by rw [(k₁₄.trans k₅).gpr']; exact hm)) fun s₆ ⟨hcar, k₆⟩ => ?_
  refine ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_, (((k₁₄.trans k₅).trans k₆).mono (by decide))⟩
  -- The block, as a number `N`, and its limbs.
  have hN := val5_lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15)
  have hNlt : v s₁ .x14 + 2 ^ 64 * v s₁ .x15 < 2 ^ 128 := by
    have := (s₁.gpr .x14).isLt; have := (s₁.gpr .x15).isLt; simp only [v]; omega
  have n0 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 0) (by omega)
  have n1 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 1) (by omega)
  have n2 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 2) (by omega)
  have n3 := lim_lt (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) (j := 3) (by omega)
  have n4 := lim4_lt hNlt
  -- `h + m` in `s₄`.
  have h4₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], v s₂ r = v s r := fun r hr => by
    simp only [v]; rw [k₂.1 r (by revert hr; decide +revert), k₁.1 r (by revert hr; decide +revert)]
  have hp : pad.toNat ≤ 1 := by cases pad <;> decide
  rw [h4₂ .x4 (by simp), m0] at a0; rw [h4₂ .x5 (by simp), m1] at a1
  rw [h4₂ .x6 (by simp), m2] at a2; rw [h4₂ .x7 (by simp), m3] at a3
  rw [h4₂ .x8 (by simp), m4] at a4
  have e0 : v s₄ .x4 = v s .x4 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 0 := by
    rw [show v s₄ .x4 = v s₃ .x4 by simp only [v]; rw [k₄.gpr'], a0]; omega_using [b0, n0]
  have e1 : v s₄ .x5 = v s .x5 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 1 := by
    rw [show v s₄ .x5 = v s₃ .x5 by simp only [v]; rw [k₄.gpr'], a1]; omega_using [b1, n1]
  have e2 : v s₄ .x6 = v s .x6 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 2 := by
    rw [show v s₄ .x6 = v s₃ .x6 by simp only [v]; rw [k₄.gpr'], a2]; omega_using [b2, n2]
  have e3 : v s₄ .x7 = v s .x7 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 3 := by
    rw [show v s₄ .x7 = v s₃ .x7 by simp only [v]; rw [k₄.gpr'], a3]; omega_using [b3, n3]
  have e4 : v s₄ .x8 = v s .x8 + lim (v s₁ .x14 + 2 ^ 64 * v s₁ .x15) 4 + 2 ^ 24 * pad.toNat := by
    rw [p4, a4]; omega_using [b4, n4, hp]
  -- The sums of products.
  obtain ⟨q0, q1, q2, q3, q4, hq⟩ := dsum_arith (a0 := v s₄ .x4) (a1 := v s₄ .x5) (a2 := v s₄ .x6)
    (a3 := v s₄ .x7) (a4 := v s₄ .x8) (by omega_using [e0, b0, n0]) (by omega_using [e1, b1, n1])
    (by omega_using [e2, b2, n2]) (by omega_using [e3, b3, n3]) (by omega_using [e4, b4, n4, hp]) hR
  rw [dform0] at d0; rw [dform1] at d1; rw [dform2] at d2; rw [dform3] at d3; rw [dform4] at d4
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q0 (by decide))] at d0
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q1 (by decide))] at d1
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q2 (by decide))] at d2
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q3 (by decide))] at d3
  rw [Nat.mod_eq_of_lt (Nat.lt_trans q4 (by decide))] at d4
  obtain ⟨hv₆, c0, c1, c2, c3, c4⟩ := hcar (by rw [d0]; exact q0) (by rw [d1]; exact q1)
    (by rw [d2]; exact q2) (by rw [d3]; exact q3) (by rw [d4]; exact q4)
  refine ⟨?_, c0, c1, c2, c3, c4⟩
  rw [hv, hv₆, d0, d1, d2, d3, d4, hq]
  have hw : w64 s.mem (s.gpr .x1) 0 + 2 ^ 64 * w64 s.mem (s.gpr .x1) 8 =
      v s₁ .x14 + 2 ^ 64 * v s₁ .x15 := by
    simp only [v, w64, l1, l2]
  have ha : val5 (v s₄ .x4) (v s₄ .x5) (v s₄ .x6) (v s₄ .x7) (v s₄ .x8) =
      hv s + (w64 s.mem (s.gpr .x1) 0 + 2 ^ 64 * w64 s.mem (s.gpr .x1) 8 + 2 ^ 128 * pad.toNat) := by
    rw [hw, ← hN]
    simp only [hv, val5, e0, e1, e2, e3, e4]
    omega
  rw [ha]

end VG.Proof.Poly1305.AArch64

end

section

/-!
# Poly1305 on AArch64: the final reduction

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

/-- `h` reduced fully, into normalized limbs. -/
theorem reduce_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block reduce) s fun s' =>
      (Bounds s → Norm (hv s) (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s s' := by
  rw [reduce]
  refine WP.block_append (WP.mono (reduceA_ok s hm) fun s₁ ⟨h₁, k₁⟩ => ?_)
  refine WP.mono (select_ok s₁) fun s₂ ⟨c4, c5, c6, c7, c8, k₂⟩ => ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_,
    (k₁.trans k₂).mono (by decide)⟩
  rcases h₁ b0 b1 b2 b3 b4 with ⟨hz, hn⟩ | ⟨ho, hn⟩
  · have hz := eq_zero_of_toNat hz
    simp only [v, c4, c5, c6, c7, c8, hz, select_zero]
    exact hn
  · have ho := eq_ones_of_toNat ho
    simp only [v, c4, c5, c6, c7, c8, ho, select_ones]
    exact hn

end VG.Proof.Poly1305.AArch64

end

section

/-!
# Poly1305 on AArch64: the state in memory

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := Offset.contains_base base h hd

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (off p d) n (off p e) k := Offset.sep p h (by omega) (by omega)

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by omega) (by omega) h) (by decide)

theorem readW32_writeW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  Mem.readW_writeW_sep (sep_off p hd he (by omega) (by omega) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The working space. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) := by
  intro a ha
  simp only [Region.Contains, off] at *
  bv_omega

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> intro a h₁ h₂ <;>
    simp only [Region.Contains, off] at h₁ h₂ <;> bv_omega

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (hR st).Contains (off st d) 8 :=
  contains_off h (by omega)

/-! ## The accumulator and the key as numbers -/

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := Offset.add_add p d e

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = w64 m st 0 + 2 ^ 64 * w64 m st 8 + 2 ^ 128 * w64 m st 16 := by
  rw [Poly1305.leNum_bytesAt_24, w64, add_ofNat_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _),
    List.take_of_length_le (by rw [Poly1305.length_bytesAt])]
  congr 1
  simp only [off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = w64 m p 0 + 2 ^ 64 * w64 m p 8 := by
  rw [Poly1305.leNum_bytesAt_16, w64, add_ofNat_zero]
  rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamping masks. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The clamped `r` of the key in the state. -/
abbrev Rk (m : Mem) (st : Addr) : Nat :=
  (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) = Rk m st := by
  rw [key_take, leNum_key, w64, w64, off, add_ofNat_zero, add_ofNat_add, Poly1305.clamp_words]

theorem Rk_lt (m : Mem) (st : Addr) : Rk m st < 2 ^ 128 := by
  have := (m.readW (off st 24) 64 &&& M0).isLt
  have := (m.readW (off st 32) 64 &&& M1).isLt
  simp only [Rk]
  omega

end VG.Proof.Poly1305.AArch64

end

/-!
# Poly1305 on AArch64: the coefficients and the accumulator on entry

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

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
    rw [t4, ← v5 .x13 (by simp), q4, times5_eq (Nat.lt_trans b4 (by decide))]
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
      · exact coef_toNat q4 (lt32 (Nat.lt_trans b4 (by decide)))
    · obtain rfl | rfl | rfl | rfl := lt5_cases' hj₁ hj
      · exact coef_toNat p1 (times5_lt (b 1 (by decide)))
      · exact coef_toNat p2 (times5_lt (b 2 (by decide)))
      · exact coef_toNat p3 (times5_lt (b 3 (by decide)))
      · exact coef_toNat p4 (times5_lt (Nat.lt_trans b4 (by decide)))
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
