import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.Encode

/-!
# ML-DSA on x86-64: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr Written Written.step ptr_step
  wp_counted WP.keep)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length bytes_map_take_drop)
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

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The registers a loop writes. -/
abbrev packRegs : List Reg := [.rax, .rcx, .rdi, .r8, .r10, .r11]
abbrev unpackRegs : List Reg := [.rax, .rcx, .rsi, .rdi, .r10, .r11]

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d c nb : Nat} (hs : Shape d c nb)
  {f o : Addr} {s₀ sE : State} (hin : polyRegion f ∈ s₀.rd ++ s₀.wr) (hout : (⟨o, 32 * d⟩ : Region) ∈ s₀.wr)
  (hsep : Region.Disjoint (polyRegion f) ⟨o, 32 * d⟩) (hF : ∀ i < 256, F (coeffAt s₀.mem f i) < 2 ^ d)
include hld hs hin hout hsep hF

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

omit hld hs hin hout hsep hF in
theorem vals_lt {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

/-- After `i` groups. -/
structure PInv (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = f + BitVec.ofNat 64 (4 * c * i)
  r8 : s.gpr .r8 = o + BitVec.ofNat 64 (nb * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨o, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < nb * i, s.mem (o + BitVec.ofNat 64 k) = (bitsToBytes (fieldBits d (vals F s₀.mem f)))[k]!
  keep : Keep packRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : PInv (f := f) (o := o) (s₀ := s₀) (sE := sE) (F := F) (d := d) (c := c) (nb := nb) i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv (f := f) (o := o) (s₀ := s₀) (sE := sE) (F := F) (d := d) (c := c) (nb := nb) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j < c, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr f (c * i + j) := fun j _ => by
    rw [hI.rdi, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .r8 + BitVec.ofNat 64 t = o + BitVec.ofNat 64 (nb * i + t) := fun t => by
    rw [hI.r8, off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 = coeffAt s₀.mem f (c * i + j) :=
    fun j hj => by
      rw [ha j hj]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega)
  refine WP.mono (packBody_ok hld hs.d20 hs.dc hs.c8 s
    (fun j hj => by rw [ha j hj, hI.rd, hI.wr]; exact inRegions_of hin (coeff_contains f (by omega)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hout (Offset.contains_base o (by omega) (by omega)))
    (fun j hj => by
      rw [ha j hj, hI.r8]
      exact (hsep.sub_left (Offset.sub_base f (by omega))).sub_right (Offset.sub_base o (by omega)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega)))
    fun s' ⟨hW, di', r8', cx', z', k'⟩ => ⟨?_, cx', z'⟩
  have hW' : Written s.mem s'.mem (o + BitVec.ofNat 64 (nb * i)) nb
      fun t => (bitsToBytes (fieldBits d (vals F s₀.mem f)))[nb * i + t]! := by
    rw [← hI.r8]
    refine hW.congr fun t ht => ?_
    rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (vals_lt hF) ht (by omega),
      take_drop_eq _ 0 (by simp; omega)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    have hj := List.mem_range.mp hj
    rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hW' hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega),
    (hI.keep.trans k').mono (by decide)⟩
  · rw [di', hI.rdi]; exact ptr_step _ i (4 * c)
  · rw [r8', hI.r8]; exact ptr_step _ i nb
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]

theorem packLoop_ok {s : State} (hdi : s.gpr .rdi = f) (h8 : s.gpr .r8 = o) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem o (32 * d) = bitsToBytes (fieldBits d (vals F s₀.mem f)) ∧
        Frame [⟨o, 32 * d⟩] s₀.mem s'.mem ∧ Keep packRegs s s' := by
  have h0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have hN0 : 0 < 256 / c := Nat.div_pos (by have := hs.c8; omega) h0
  refine WP.mono (wp_counted (N := 256 / c)
    (v := BitVec.ofNat 32 (256 / c)) (by rw [BitVec.toNat_ofNat]; omega) hN0
    (PInv (f := f) (o := o) (s₀ := s₀) (sE := s) (F := F) (d := d) (c := c) (nb := nb))
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₂.mono (by decide)⟩)
    fun i hi s hI => packStep hld hs hin hout hsep hF hi hI)
    fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  · rw [k₂.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), h8]; simp
  · rw [k₂.2.1, hrd]
  · rw [k₂.2.2, hwr]
  · rw [m₂, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk)

end

/-! ## Unpacking -/

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} (hfin : FinOk fin d W)
  (hs : Shape d c nb) {v p : Addr} {s₀ sE : State} (hin : (⟨v, 32 * d⟩ : Region) ∈ s₀.rd ++ s₀.wr)
  (hout : polyRegion p ∈ s₀.wr) (hsep : Region.Disjoint ⟨v, 32 * d⟩ (polyRegion p))
include hfin hs hin hout hsep

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

/-- After `i` groups. -/
structure UInv (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = v + BitVec.ofNat 64 (nb * i)
  rsi : s.gpr .rsi = p + BitVec.ofNat 64 (4 * c * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [polyRegion p] s₀.mem s.mem
  done : ∀ k < c * i, coeffAt s.mem p k = W (inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)
  keep : Keep unpackRegs sE s

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State}
    (hI : UInv (v := v) (p := p) (s₀ := s₀) (sE := sE) (W := W) (d := d) (c := c) (nb := nb) i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv (v := v) (p := p) (s₀ := s₀) (sE := sE) (W := W) (d := d) (c := c) (nb := nb) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j, s.gpr .rsi + BitVec.ofNat 64 (4 * j) = coeffAddr p (c * i + j) := fun j => by
    rw [hI.rsi, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .rdi + BitVec.ofNat 64 t = v + BitVec.ofNat 64 (nb * i + t) := fun t => by
    rw [hI.rdi, off_add]
  have hsub : Region.Sub ⟨s.gpr .rsi, 4 * c⟩ (polyRegion p) := by
    rw [hI.rsi]; exact Offset.sub_base p (by rw [Nat.mul_assoc]; omega)
  refine WP.mono (unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 s
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact inRegions_of hin (Offset.contains_base v (by omega) (by omega)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hout (coeff_contains p (by omega)))
    (fun t ht => by
      rw [hb]
      exact (hsep.sub_left (Offset.sub_base v (by omega))).sub_right hsub))
    fun s' ⟨hw, hf, di', si', cx', z', k'⟩ => ⟨?_, cx', z'⟩
  -- The bytes of the group, on entry.
  have hB : (List.range nb).map (fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) =
      (((bytesAt s₀.mem v (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
    rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega)]
    refine List.map_congr_left fun t ht => ?_
    have ht := List.mem_range.mp ht
    rw [getD_map_toNat, bytesAt_getD _ _ (by omega), hb]
    refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep _ (Offset.contains_base v (by omega) (by omega))
  have hlt : ∀ a ∈ (bytesAt s₀.mem v (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine ⟨?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_), fun k hk => ?_,
    (hI.keep.trans k').mono (by decide)⟩
  · rw [di', hI.rdi]; exact ptr_step _ i nb
  · rw [si', hI.rsi]; exact ptr_step _ i (4 * c)
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  by_cases hk' : k < c * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [hI.rsi]
    exact Offset.disjoint p (by rw [Nat.mul_assoc]; omega) (by omega) (by rw [Nat.mul_assoc]; omega)
  · -- Written by this group.
    have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega
    have := hw (k - c * i) hj
    rw [ha, show c * i + (k - c * i) = k by omega, hB, digits_group hs.dc hlt hj,
      show c * i + (k - c * i) = k by omega] at this
    rw [coeffAt_eq, this]

theorem unpackLoop_ok {s : State} (hdi : s.gpr .rdi = v) (hsi : s.gpr .rsi = p) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem p k = W (inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion p] s₀.mem s'.mem ∧ Keep unpackRegs s s' := by
  have h0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have hN0 : 0 < 256 / c := Nat.div_pos (by have := hs.c8; omega) h0
  refine WP.mono (wp_counted (N := 256 / c)
    (v := BitVec.ofNat 32 (256 / c)) (by rw [BitVec.toNat_ofNat]; omega) hN0
    (UInv (v := v) (p := p) (s₀ := s₀) (sE := s) (W := W) (d := d) (c := c) (nb := nb))
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₂.mono (by decide)⟩)
    fun i hi s hI => unpackStep hfin hs hin hout hsep hi hI)
    fun s' hI => ⟨fun k hk' => hI.done k (by rw [hs.cN]; exact hk'), hI.frame, hI.keep⟩
  · rw [k₂.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), hsi]; simp
  · rw [k₂.2.1, hrd]
  · rw [k₂.2.2, hwr]
  · rw [m₂, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.X86_64.Pack
