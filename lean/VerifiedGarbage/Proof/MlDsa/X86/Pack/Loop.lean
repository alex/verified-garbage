import VerifiedGarbage.Proof.MlDsa.X86.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA on x86 (32-bit): the loops over the groups, as pieces

Untrusted: everything here is checked by Lean. In a leaf (whose frame's
push leaves the state `P0 s₀`), once the input pointer `iP s₀` is in `esi`
and the output pointer `oP s₀` in `edi` (`Start`):

* `packLoop_piece`: the loop of `packBody` writes the packing of the values
  of the 256 coefficients at `iP s₀`;
* `unpackLoop_piece`: the loop of `unpackBody` writes, for each field of
  the bytes at `iP s₀`, `fin`'s coefficient of it.

Both for any width and any `ld` or `fin`, from the group lemmas of
`Stream.lean`, and constant time: every address depends only on `esp`,
`esi`, `edi` and `ecx`, which correctness determines from the public
pointers (`Piece.countLoop`, given the taint analysis of the loop body).
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.taint Piece.countLoop Piece.seq P0 E0 P0_esp LeafEnd ea_off addr_add
  cnt_next cnt_ne)
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length)
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

theorem Shape.nb0 {d c nb : Nat} (h : Shape d c nb) : 0 < nb := by
  have := h.d1; have := h.c0; have := h.dc
  have : 0 < d * c := Nat.mul_pos (by omega) (by omega)
  omega

theorem Shape.group {d c nb : Nat} (h : Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem Shape.N {d c nb : Nat} (h : Shape d c nb) : 0 < 256 / c ∧ 256 / c ≤ 256 :=
  ⟨Nat.div_pos (by have := h.c8; omega) h.c0, Nat.div_le_self _ _⟩

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The loop condition after the counter counted down. -/
theorem ecx_ne {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) {s s' : State}
    (hc : s.gpr .ecx = BitVec.ofNat 32 (N - i)) (hz : s'.zf = some (s.gpr .ecx - 1 == 0)) :
    eval .ne s' = some (decide (i + 1 < N)) := by
  simp only [eval, hz, hc]; exact cnt_ne hi hN

section
variable (iP oP : State → BitVec 32)

/-- The input pointer, as an address. -/
abbrev iA (s₀ : State) : Addr := (iP s₀).setWidth 64
/-- The output pointer, as an address. -/
abbrev oA (s₀ : State) : Addr := (oP s₀).setWidth 64

/-- In a leaf, once its pointers are loaded. -/
structure Start (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = iP s₀
  edi : s.gpr .edi = oP s₀

end

/-- The registers correctness determines in a loop. -/
abbrev loopRegs : List Reg := [.esp, .esi, .edi, .ecx]

/-! ## Packing -/

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

theorem vals_lt {F : BitVec 32 → Nat} {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

section
variable (F : BitVec 32 → Nat) (d c nb : Nat) (iP oP : State → BitVec 32)

/-- The packing of the values of the coefficients at `iP s₀`. -/
abbrev packed (s₀ : State) : List Byte := bitsToBytes (fieldBits d (vals F (P0 s₀).mem (iA iP s₀)))

/-- What the pack loop needs of the layout. -/
structure PackOk (s₀ : State) : Prop where
  inR : polyRegion (iA iP s₀) ∈ (P0 s₀).rd ++ (P0 s₀).wr
  outR : (⟨oA oP s₀, 32 * d⟩ : Region) ∈ (P0 s₀).wr
  sep : Region.Disjoint (polyRegion (iA iP s₀)) ⟨oA oP s₀, 32 * d⟩
  ifit : (iP s₀).toNat + 1024 ≤ 2 ^ 32
  ofit : (oP s₀).toNat + 32 * d ≤ 2 ^ 32
  lt : ∀ i < 256, F (coeffAt (P0 s₀).mem (iA iP s₀) i) < 2 ^ d

/-- After `i` groups. -/
structure PInv (s₀ : State) (i : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = iP s₀ + BitVec.ofNat 32 (4 * c * i)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (nb * i)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 / c - i)
  frame : Frame [⟨oA oP s₀, 32 * d⟩] (P0 s₀).mem s.mem
  done : ∀ k < nb * i, s.mem (oA oP s₀ + BitVec.ofNat 64 k) = (packed F d iP s₀)[k]!

end

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} {d c nb : Nat} {iP oP : State → BitVec 32}

theorem packStep (hld : LdOk ld F) (hs : Shape d c nb) {s₀ : State} (hk : PackOk F d iP oP s₀) {i : Nat}
    (hi : i < 256 / c) {s : State} (hI : PInv F d c nb iP oP s₀ i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv F d c nb iP oP s₀ (i + 1) s' ∧ eval .ne s' = some (decide (i + 1 < 256 / c)) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hN := hs.N.2
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have fi := hk.ifit
  have fo := hk.ofit
  have ha : ∀ j < c, addr (s.gpr .esi) (4 * j) = coeffAddr (iA iP s₀) (c * i + j) := fun j _ => by
    rw [hI.esi, addr_add (by rw [Nat.mul_assoc]; omega)]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have ho : (s.gpr .edi).setWidth 64 = oA oP s₀ + BitVec.ofNat 64 (nb * i) := by
    rw [hI.edi]; exact ea_off (by omega)
  have hb : ∀ t, (s.gpr .edi).setWidth 64 + BitVec.ofNat 64 t = oA oP s₀ + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ho, off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (addr (s.gpr .esi) (4 * j)) 32 = coeffAt (P0 s₀).mem (iA iP s₀) (c * i + j) :=
    fun j hj => by
      rw [ha j hj]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hk.sep)
        (by omega)
  refine WP.mono (packBody_ok hld hs.d20 hs.dc s (by rw [hI.edi, toNat_add_fit (by omega)]; omega)
    (fun j hj => by rw [ha j hj, hI.rd, hI.wr]; exact inRegions_of hk.inR (coeff_contains _ (by omega)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hk.outR (Offset.contains_base _ (by omega) (by omega)))
    (fun j hj => by
      rw [ha j hj, ho]
      exact (hk.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)))
    (fun j hj => by rw [hw j hj]; exact hk.lt _ (by omega)))
    fun s' ⟨hW, si', di', cx', z', k'⟩ => ⟨?_, ecx_ne hi (by omega) hI.ecx z'⟩
  have hW' : Written s.mem s'.mem (oA oP s₀ + BitVec.ofNat 64 (nb * i)) nb
      fun t => (packed F d iP s₀)[nb * i + t]! := by
    rw [← ho]
    refine hW.congr fun t ht => ?_
    rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (vals_lt hk.lt) ht (by omega),
      take_drop_eq _ 0 (by simp; omega)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    have hj := List.mem_range.mp hj
    rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hW' hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega)⟩
  · rw [k'.gpr (by decide), hI.esp]
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · rw [si', hI.esi]; exact ptr_step _ i (4 * c)
  · rw [di', hI.edi]; exact ptr_step _ i nb
  · rw [cx', hI.ecx]; exact cnt_next hi

variable {Pre : State → Prop} {Pub : State → State → Prop} {X : State → Prop}

/-- All the groups: the bytes of the packing. -/
theorem packLoop_piece (hld : LdOk ld F) (hs : Shape d c nb) (iP oP : State → BitVec 32)
    (hok : ∀ s₀, Pre s₀ → X s₀ → PackOk F d iP oP s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀' ∧ iP s₀ = iP s₀' ∧ oP s₀ = oP s₀')
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr loopRegs) (.block (packBody ld d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => Start iP oP s₀ s ∧ X s₀)
      (fun s₀ s => (LeafEnd s₀ [⟨oA oP s₀, 32 * d⟩] s ∧ bytesAt s.mem (oA oP s₀) (32 * d) = packed F d iP s₀) ∧
        X s₀) (packLoop ld d c nb) := by
  have hN := hs.N
  refine (Piece.seq (B := fun s₀ s => PInv F d c nb iP oP s₀ 0 s ∧ X s₀)
    (Piece.taint [] (fun s₀ s _ ⟨h, hx⟩ => ?wp) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht₁)
    (Piece.countLoop hN.1 (fun i s₀ s => PInv F d c nb iP oP s₀ i s ∧ X s₀) loopRegs
      (fun i hi s₀ s h₀ ⟨h, hx⟩ => (packStep hld hs (hok s₀ h₀ hx) hi h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hx⟩, e⟩)
      (fun i _ s₀ s₀' s s' h₀ h₀' hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?regs) ht₂)).mono (fun _ _ _ h => h) ?post
  case wp =>
    xrun
    refine ⟨⟨?_, h.rd, h.wr, ?_, ?_, ?_, by rw [setReg_mem, h.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩, hx⟩ <;>
    simp (config := { decide := true }) only [setReg_gpr, ite_true, ite_false, h.esp, h.esi, h.edi,
      Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
  case regs =>
    obtain ⟨e₀, e₁, e₂⟩ := hpub _ _ h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.esp, h'.esp, P0_esp, P0_esp, e₀]
    · rw [h.esi, h'.esi, e₁]
    · rw [h.edi, h'.edi, e₂]
    · rw [h.ecx, h'.ecx]
  case post =>
    intro s₀ s h₀ ⟨h, hx⟩
    refine ⟨⟨⟨h.frame, h.esp, h.rd, h.wr⟩, bytesAt_eq! (pack_length d _ (by simp)) fun k hk => h.done k ?_⟩, hx⟩
    rw [hs.bN]; exact hk

end

/-! ## Unpacking -/

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

section
variable (W : Nat → BitVec 32) (d c nb : Nat) (iP oP : State → BitVec 32)

/-- What the unpack loop needs of the layout. -/
structure UnpackOk (s₀ : State) : Prop where
  inR : (⟨iA iP s₀, 32 * d⟩ : Region) ∈ (P0 s₀).rd ++ (P0 s₀).wr
  outR : polyRegion (oA oP s₀) ∈ (P0 s₀).wr
  sep : Region.Disjoint ⟨iA iP s₀, 32 * d⟩ (polyRegion (oA oP s₀))
  ifit : (iP s₀).toNat + 32 * d ≤ 2 ^ 32
  ofit : (oP s₀).toNat + 1024 ≤ 2 ^ 32

/-- After `i` groups. -/
structure UInv (s₀ : State) (i : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = iP s₀ + BitVec.ofNat 32 (nb * i)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (4 * c * i)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 / c - i)
  frame : Frame [polyRegion (oA oP s₀)] (P0 s₀).mem s.mem
  done : ∀ k < c * i, coeffAt s.mem (oA oP s₀) k = W (inNum (P0 s₀).mem (iA iP s₀) d / 2 ^ (d * k) % 2 ^ d)

end

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} {iP oP : State → BitVec 32}

theorem unpackStep (hfin : FinOk fin d W) (hs : Shape d c nb) {s₀ : State} (hk : UnpackOk d iP oP s₀)
    {i : Nat} (hi : i < 256 / c) {s : State} (hI : UInv W d c nb iP oP s₀ i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv W d c nb iP oP s₀ (i + 1) s' ∧ eval .ne s' = some (decide (i + 1 < 256 / c)) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hN := hs.N.2
  have hnb := hs.nb20
  have hd20 := hs.d20
  have hc0 := hs.c0
  have fi := hk.ifit
  have fo := hk.ofit
  have ho : (s.gpr .edi).setWidth 64 = oA oP s₀ + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.edi]; exact ea_off (by rw [Nat.mul_assoc]; omega)
  have ha : ∀ j, (s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * j) = coeffAddr (oA oP s₀) (c * i + j) :=
    fun j => by rw [ho, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t < nb, addr (s.gpr .esi) t = iA iP s₀ + BitVec.ofNat 64 (nb * i + t) := fun t ht => by
    rw [hI.esi]; exact addr_add (by omega)
  have hsub : Region.Sub ⟨(s.gpr .edi).setWidth 64, 4 * c⟩ (polyRegion (oA oP s₀)) := by
    rw [ho]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega)
  refine WP.mono (unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 s
    (by rw [hI.edi, toNat_add_fit (by rw [Nat.mul_assoc]; omega)]; rw [Nat.mul_assoc]; omega)
    (fun t ht => by rw [hb t ht, hI.rd, hI.wr]; exact inRegions_of hk.inR (Offset.contains_base _ (by omega) (by omega)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hk.outR (coeff_contains _ (by omega)))
    (fun t ht => by
      rw [hb t ht]
      exact (hk.sep.sub_left (Offset.sub_base _ (by omega))).sub_right hsub))
    fun s' ⟨hw, hf, si', di', cx', z', k'⟩ => ⟨?_, ecx_ne hi (by omega) hI.ecx z'⟩
  -- The bytes of the group, on entry.
  have hB : (List.range nb).map (fun t => (s.mem (addr (s.gpr .esi) t)).toNat) =
      (((bytesAt (P0 s₀).mem (iA iP s₀) (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
    rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega)]
    refine List.map_congr_left fun t ht => ?_
    have ht := List.mem_range.mp ht
    rw [getD_map_toNat, bytesAt_getD _ _ (by omega), hb t ht]
    refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact hk.sep _ (Offset.contains_base _ (by omega) (by omega))
  have hlt : ∀ a ∈ (bytesAt (P0 s₀).mem (iA iP s₀) (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_), fun k hk => ?_⟩
  · rw [k'.gpr (by decide), hI.esp]
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · rw [si', hI.esi]; exact ptr_step _ i nb
  · rw [di', hI.edi]; exact ptr_step _ i (4 * c)
  · rw [cx', hI.ecx]; exact cnt_next hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  by_cases hk' : k < c * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [ho]
    exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega) (by omega) (by rw [Nat.mul_assoc]; omega)
  · -- Written by this group.
    have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega
    have := hw (k - c * i) hj
    rw [ha, show c * i + (k - c * i) = k by omega, hB, digits_group hs.dc hlt hj,
      show c * i + (k - c * i) = k by omega] at this
    rw [coeffAt_eq, this]

variable {Pre : State → Prop} {Pub : State → State → Prop} {X : State → Prop}

/-- All the groups: `fin`'s coefficient of each field. -/
theorem unpackLoop_piece (hfin : FinOk fin d W) (hs : Shape d c nb) (iP oP : State → BitVec 32)
    (hok : ∀ s₀, Pre s₀ → X s₀ → UnpackOk d iP oP s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀' ∧ iP s₀ = iP s₀' ∧ oP s₀ = oP s₀')
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr loopRegs) (.block (unpackBody fin d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => Start iP oP s₀ s ∧ X s₀)
      (fun s₀ s => (LeafEnd s₀ [polyRegion (oA oP s₀)] s ∧
        ∀ k < 256, coeffAt s.mem (oA oP s₀) k = W (inNum (P0 s₀).mem (iA iP s₀) d / 2 ^ (d * k) % 2 ^ d)) ∧
        X s₀) (unpackLoop fin d c nb) := by
  have hN := hs.N
  refine (Piece.seq (B := fun s₀ s => UInv W d c nb iP oP s₀ 0 s ∧ X s₀)
    (Piece.taint [] (fun s₀ s _ ⟨h, hx⟩ => ?wp) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht₁)
    (Piece.countLoop hN.1 (fun i s₀ s => UInv W d c nb iP oP s₀ i s ∧ X s₀) loopRegs
      (fun i hi s₀ s h₀ ⟨h, hx⟩ => (unpackStep hfin hs (hok s₀ h₀ hx) hi h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hx⟩, e⟩)
      (fun i _ s₀ s₀' s s' h₀ h₀' hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?regs) ht₂)).mono (fun _ _ _ h => h) ?post
  case wp =>
    xrun
    refine ⟨⟨?_, h.rd, h.wr, ?_, ?_, ?_, by rw [setReg_mem, h.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩, hx⟩ <;>
    simp (config := { decide := true }) only [setReg_gpr, ite_true, ite_false, h.esp, h.esi, h.edi,
      Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
  case regs =>
    obtain ⟨e₀, e₁, e₂⟩ := hpub _ _ h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.esp, h'.esp, P0_esp, P0_esp, e₀]
    · rw [h.esi, h'.esi, e₁]
    · rw [h.edi, h'.edi, e₂]
    · rw [h.ecx, h'.ecx]
  case post =>
    intro s₀ s h₀ ⟨h, hx⟩
    exact ⟨⟨⟨h.frame, h.esp, h.rd, h.wr⟩, fun k hk => h.done k (by rw [hs.cN]; exact hk)⟩, hx⟩

end

end VG.Proof.MlDsa.X86.Pack
