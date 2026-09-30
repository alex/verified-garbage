import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Bits

/-!
# ML-DSA on AArch64: the loops over the groups

Untrusted: everything here is checked by Lean. `packLoop_ok`: the loop of
`packBody` writes the packing of the values of the 256 coefficients at
`f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for each field of
the bytes at `v`, `fin`'s coefficient of it. Both for any width and any
`ld` or `fin`, from the group lemmas of `Stream.lean`.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_movImm toNat_imm toNat_sub_n toNat_ofNat_lt BytesUpTo
  BytesUpTo.zero BytesUpTo.eq ptr_add ptr_zero ptr_next count_loop)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD)
open VG.Proof.MlDsa.Pack

/-- The value of each coefficient is less than `2ᵈ`, and the groups tile the
polynomial and the output. -/
structure Shape (d c nb : Nat) : Prop where
  d1 : 1 ≤ d
  d20 : d ≤ 20
  dc : d * c = 8 * nb
  c0 : 0 < c
  c8 : c ≤ 8
  cN : c * (256 / c) = 256
  bN : nb * (256 / c) = 32 * d

theorem Shape.nb20 {d c nb : Nat} (h : Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega

theorem Shape.group {d c nb : Nat} (h : Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem Shape.G {d c nb : Nat} (h : Shape d c nb) : 0 < 256 / c ∧ 256 / c ≤ 256 :=
  ⟨Nat.div_pos (by have := h.c8; omega) h.c0, Nat.div_le_self _ _⟩

/-- The registers the loops write. -/
abbrev packRegs : List Reg := [.x0, .x2, .x9, .x10, .x11, .x14]
abbrev unpackRegs : List Reg := [.x0, .x4, .x9, .x10, .x11, .x14, .x15]

/-- A counter set to `n < 2¹⁶` with `movz`. -/
theorem movz_toNat {n : Nat} (h : n < 2 ^ 16) : ((BitVec.ofNat 16 n).setWidth 64).toNat = n := by
  rw [toNat_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The counter after one more group. -/
theorem count_step {x : BitVec 64} {N g : Nat} (h : x.toNat = N - g) (hg : g < N) :
    (x - BitVec.ofNat 64 1).toNat = N - (g + 1) := by
  rw [toNat_sub_n (by rw [h, toNat_ofNat_lt (by decide)]; omega), h, toNat_ofNat_lt (by decide)]
  omega

/-! ## Packing -/

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

theorem vals_lt {F : BitVec 32 → Nat} {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

theorem vals_getD (F : BitVec 32 → Nat) (m : Mem) (f : Addr) {i : Nat} (hi : i < 256) :
    (vals F m f).getD i 0 = F (coeffAt m f i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} {K12 K13 : BitVec 64} (hld : LdOk ld F K12 K13)
  {d c nb : Nat} (hs : Shape d c nb) {f o : Addr} {s₀ sE : State} (hin : polyRegion f ∈ s₀.rd ++ s₀.wr)
  (hout : (⟨o, 32 * d⟩ : Region) ∈ s₀.wr) (hsep : Region.Disjoint (polyRegion f) ⟨o, 32 * d⟩)
  (hF : ∀ i < 256, F (coeffAt s₀.mem f i) < 2 ^ d)
include hld hs hin hout hsep hF

/-- After `g` groups. -/
structure PInv (g : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = f + BitVec.ofNat 64 (4 * c * g)
  x2 : s.gpr .x2 = o + BitVec.ofNat 64 (nb * g)
  x11 : (s.gpr .x11).toNat = 256 / c - g
  x12 : s.gpr .x12 = K12
  x13 : s.gpr .x13 = K13
  out : BytesUpTo s.mem o (32 * d) (nb * g) (fun k => (bitsToBytes (fieldBits d (vals F s₀.mem f)))[k]!)
    fun k => s₀.mem (o + BitVec.ofNat 64 k)
  frame : Frame [⟨o, 32 * d⟩] s₀.mem s.mem
  keep : Keep packRegs sE s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem packStep {g : Nat} (hg : g < 256 / c) {s : State}
    (hI : PInv (F := F) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (f := f) (o := o) (s₀ := s₀)
      (sE := sE) g s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv (F := F) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (f := f) (o := o) (s₀ := s₀)
        (sE := sE) (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 256 / c) := by
  obtain ⟨hcg, hbg⟩ := hs.group hg
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j, s.gpr .x0 + BitVec.ofNat 64 (4 * j) = coeffAddr f (c * g + j) := fun j => by
    rw [hI.x0, ptr_add, coeffAddr, Nat.mul_add, Nat.mul_assoc]
  refine WP.mono (packBody_ok hld (gb := nb * g) (N := 32 * d) (o := o) (m₀ := s₀.mem)
    (V := fun j => F (coeffAt s₀.mem f (c * g + j))) hs.d20 hs.dc hs.c8 hbg (by omega)
    (fun j hj => hF _ (by omega)) (fun t ht => ?_) s hI.x12 hI.x13
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact ⟨_, hin, coeff_contains f (by omega)⟩)
    (fun j hj m hm => by
      rw [ha j, ← coeffAt_eq]
      exact congrArg F (coeffAt_frame hm (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by omega)))
    hI.x2 (by rw [hI.wr]; exact hout) hI.out hI.frame)
    fun s' ⟨hw', hf', x0', x2', x11', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hf', (hI.keep.trans k').mono, ?_, ?_⟩, ?_⟩
  · -- The bytes of the group.
    rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (vals_lt hF) ht (by omega),
      take_drop_eq _ 0 (by simp; omega)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    exact vals_getD F s₀.mem f (by have := List.mem_range.mp hj; omega)
  · rw [x0', hI.x0, ptr_add, Nat.mul_succ]
  · rw [x2', hI.x2, ptr_next]
  · rw [x11']; exact count_step hI.x11 hg
  · rw [k'.get .x12, hI.x12]
  · rw [k'.get .x13, hI.x13]
  · rw [Nat.mul_succ]; exact hw'
  · rw [k'.rd, hI.rd]
  · rw [k'.wr, hI.wr]
  · rw [x11', count_step hI.x11 hg]; omega

theorem packLoop_ok {s : State} (h0 : s.gpr .x0 = f) (h2 : s.gpr .x2 = o) (h12 : s.gpr .x12 = K12)
    (h13 : s.gpr .x13 = K13) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem o (32 * d) = bitsToBytes (fieldBits d (vals F s₀.mem f)) ∧
        Frame [⟨o, 32 * d⟩] s₀.mem s'.mem ∧ Keep packRegs s s' := by
  obtain ⟨hG0, hG⟩ := hs.G
  refine WP.seq (wp_movz fun s₁ o₁ e₁ => wp_nil ?_)
  refine WP.mono (count_loop hG0
    (PInv (F := F) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (f := f) (o := o) (s₀ := s₀) (sE := s))
    (fun g hg s hI => packStep hld hs hin hout hsep hF hg hI) ?_)
    fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  · refine ⟨by rw [o₁.get .x0, h0, Nat.mul_zero, ptr_zero], by rw [o₁.get .x2, h2, Nat.mul_zero, ptr_zero],
      by rw [e₁, movz_toNat (by omega), Nat.sub_zero], by rw [o₁.get .x12, h12], by rw [o₁.get .x13, h13],
      ?_, by rw [o₁.mem, hm]; exact Frame.refl _ _, o₁.keep.mono, by rw [o₁.rd, hrd], by rw [o₁.wr, hwr]⟩
    rw [o₁.mem, hm, Nat.mul_zero]; exact BytesUpTo.zero _
  · have hB : nb * (256 / c) = 32 * d := hs.bN
    have hout' := hI.out
    rw [hB] at hout'
    exact hout'.eq (pack_length d _ (by simp)) fun _ _ => rfl

end

/-! ## Unpacking -/

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {K12 K13 : BitVec 64} {d c nb : Nat}
  (hfin : FinOk fin d W K12 K13) (hs : Shape d c nb) {v p : Addr} {s₀ sE : State}
  (hin : (⟨v, 32 * d⟩ : Region) ∈ s₀.rd ++ s₀.wr) (hout : polyRegion p ∈ s₀.wr)
  (hsep : Region.Disjoint ⟨v, 32 * d⟩ (polyRegion p))
include hfin hs hin hout hsep

/-- After `g` groups. -/
structure UInv (g : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = v + BitVec.ofNat 64 (nb * g)
  x4 : s.gpr .x4 = p + BitVec.ofNat 64 (4 * (c * g))
  x11 : (s.gpr .x11).toNat = 256 / c - g
  x12 : s.gpr .x12 = K12
  x13 : s.gpr .x13 = K13
  x15 : (s.gpr .x15).toNat = 2 ^ d - 1
  out : CoeffsUpTo s.mem p (c * g) (fun k => W (inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d))
    fun k => coeffAt s₀.mem p k
  frame : Frame [polyRegion p] s₀.mem s.mem
  keep : Keep unpackRegs sE s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem unpackStep {g : Nat} (hg : g < 256 / c) {s : State}
    (hI : UInv (W := W) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (v := v) (p := p) (s₀ := s₀)
      (sE := sE) g s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv (W := W) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (v := v) (p := p) (s₀ := s₀)
        (sE := sE) (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 256 / c) := by
  obtain ⟨hcg, hbg⟩ := hs.group hg
  have hnb := hs.nb20
  have hd20 := hs.d20
  have hb : ∀ t, s.gpr .x0 + BitVec.ofNat 64 t = v + BitVec.ofNat 64 (nb * g + t) := fun t => by
    rw [hI.x0, ptr_add]
  have hlt : ∀ a ∈ (bytesAt s₀.mem v (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine WP.mono (unpackBody_ok hfin (gc := c * g) (p := p) (m₀ := s₀.mem)
    (B := fun t => (s₀.mem (v + BitVec.ofNat 64 (nb * g + t))).toNat) hs.d20 hs.dc hs.c8 hcg
    (fun j hj => ?_) s hI.x12 hI.x13 hI.x15
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact ⟨_, hin, Offset.contains_base v (by omega) (by omega)⟩)
    (fun t ht m hm => by
      rw [hb]
      refine congrArg BitVec.toNat (hm _ fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ (Offset.contains_base v (by omega) (by omega)))
    hI.x4 (by rw [hI.wr]; exact hout) hI.out hI.frame)
    fun s' ⟨hw', hf', x0', x4', x11', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hf', (hI.keep.trans k').mono, ?_, ?_⟩, ?_⟩
  · -- The coefficients of the group.
    have e := digits_group (g := g) hs.dc hlt hj
    rw [take_drop_eq _ 0 (by rw [List.length_map, Spec.Sha3.bytesAt, List.length_map, List.length_range]; omega)]
      at e
    have hB : ((List.range nb).map fun t => ((bytesAt s₀.mem v (32 * d)).map (·.toNat)).getD (nb * g + t) 0) =
        (List.range nb).map fun t => (s₀.mem (v + BitVec.ofNat 64 (nb * g + t))).toNat :=
      List.map_congr_left fun t ht => by
        rw [getD_map_toNat, bytesAt_getD _ _ (by have := List.mem_range.mp ht; omega)]
    rw [hB] at e
    rw [e]
  · rw [x0', hI.x0, ptr_next]
  · rw [x4', hI.x4, ptr_add, Nat.mul_succ, Nat.mul_add]
  · rw [x11']; exact count_step hI.x11 hg
  · rw [k'.get .x12, hI.x12]
  · rw [k'.get .x13, hI.x13]
  · rw [k'.get .x15, hI.x15]
  · rw [Nat.mul_succ]; exact hw'
  · rw [k'.rd, hI.rd]
  · rw [k'.wr, hI.wr]
  · rw [x11', count_step hI.x11 hg]; omega

theorem unpackLoop_ok {s : State} (h0 : s.gpr .x0 = v) (h4 : s.gpr .x4 = p) (h12 : s.gpr .x12 = K12)
    (h13 : s.gpr .x13 = K13) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem p k = W (inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion p] s₀.mem s'.mem ∧ Keep unpackRegs s s' := by
  obtain ⟨hG0, hG⟩ := hs.G
  have hd20 := hs.d20
  have hp : 2 ^ d - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hd20; omega
  refine WP.seq ?_
  rw [← List.append_nil [Instr.movz .x .x11 _ 0]]
  refine wp_movImm fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ => wp_nil ?_
  refine WP.mono (count_loop hG0
    (UInv (W := W) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (v := v) (p := p) (s₀ := s₀) (sE := s))
    (fun g hg s hI => unpackStep hfin hs hin hout hsep hg hI) ?_)
    fun s' hI => ⟨fun k hk => ?_, hI.frame, hI.keep⟩
  · have k₂ := o₁.trans o₂
    refine ⟨by rw [k₂.get .x0, h0, Nat.mul_zero, ptr_zero],
      by rw [k₂.get .x4, h4, Nat.mul_zero, Nat.mul_zero, ptr_zero],
      by rw [e₂, movz_toNat (by omega), Nat.sub_zero], by rw [k₂.get .x12, h12], by rw [k₂.get .x13, h13],
      by rw [o₂.get .x15, e₁, toNat_ofNat_lt hp], ?_, by rw [k₂.mem, hm]; exact Frame.refl _ _, k₂.keep.mono,
      by rw [k₂.rd, hrd], by rw [k₂.wr, hwr]⟩
    rw [k₂.mem, hm, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · have hout' := hI.out
    rw [hs.cN] at hout'
    exact hout'.all hk

end

end VG.Proof.MlDsa.AArch64.Pack
