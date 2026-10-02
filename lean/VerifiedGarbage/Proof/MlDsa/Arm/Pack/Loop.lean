import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.Pack.Mem

/-!
# ML-DSA on 32-bit ARM: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`, and for any
state that permits the accesses: they change only the output, the registers of
`packRegs` or `unpackRegs` and the flags.
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- The value of each coefficient is less than `2ᵈ`, the groups tile the
polynomial and the output, and the immediates of the loop are encodable. -/
structure Shape (d c nb : Nat) : Prop where
  d1 : 1 ≤ d
  d20 : d ≤ 20
  dc : d * c = 8 * nb
  c0 : 0 < c
  c8 : c ≤ 8
  cN : c * (256 / c) = 256
  bN : nb * (256 / c) = 32 * d
  e4c : encodable (BitVec.ofNat 32 (4 * c)) = true
  enb : encodable (BitVec.ofNat 32 nb) = true
  eN : encodable (BitVec.ofNat 32 (256 / c)) = true

theorem Shape.nb20 {d c nb : Nat} (h : Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega

theorem Shape.nb0 {d c nb : Nat} (h : Shape d c nb) : 0 < nb := by
  have := Nat.mul_le_mul h.d1 h.c0; have := h.dc; omega

theorem Shape.group {d c nb : Nat} (h : Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ptr_step (p : BitVec 32) (i c : Nat) :
    p + BitVec.ofNat 32 (c * i) + BitVec.ofNat 32 c = p + BitVec.ofNat 32 (c * (i + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add]

theorem ptr_toNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) : (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The registers a loop writes. -/
abbrev packRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12]
abbrev unpackRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12]

/-- `mov r, #N`. -/
theorem movN_ok (r : Reg) (N : Nat) (hN : encodable (BitVec.ofNat 32 N) = true) (s : State) :
    WP isa (.block [.mov r (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      (s'.gpr r = BitVec.ofNat 32 N ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  refine WP.keep _ ?_ (by simp [writesOnly, dstOf])
  run_block [hN, and_true]

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : LdOk ld V) {d c nb : Nat} (hs : Shape d c nb)
  {pf po : BitVec 32} {m₀ : Mem} {rd wr : List Region} {sE : State}
  (hin : polyRegion (State.addr pf) ∈ rd ++ wr) (hout : (⟨State.addr po, 32 * d⟩ : Region) ∈ wr)
  (hsep : Region.Disjoint (polyRegion (State.addr pf)) ⟨State.addr po, 32 * d⟩)
  (fitF : pf.toNat + 1024 ≤ 2 ^ 32) (fitO : po.toNat + 32 * d ≤ 2 ^ 32)
  (hF : ∀ i < 256, V (coeffAt m₀ (State.addr pf) i) < 2 ^ d)
include hld hs hin hout hsep fitF fitO hF

/-- The values of the coefficients. -/
abbrev vals (V : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => V (coeffAt m f i)

omit hld hs hin hout hsep fitF fitO hF in
theorem vals_lt {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, V (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals V m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

omit hld hs hin hout hsep fitF fitO hF in
/-- After `i` groups. -/
structure PInv (V : BitVec 32 → Nat) (d c nb : Nat) (pf po : BitVec 32) (m₀ : Mem) (rd wr : List Region)
    (sE : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf + BitVec.ofNat 32 (4 * c * i)
  r2 : s.gpr .r2 = po + BitVec.ofNat 32 (nb * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (1 * (256 / c - i))
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [⟨State.addr po, 32 * d⟩] m₀ s.mem
  done : ∀ k < nb * i, s.mem (State.addr po + BitVec.ofNat 64 k) =
    (bitsToBytes (fieldBits d (vals V m₀ (State.addr pf))))[k]!
  keep : Keep packRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : PInv V d c nb pf po m₀ rd wr sE i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv V d c nb pf po m₀ rd wr sE (i + 1) s' ∧ s'.z = decide (i + 1 = 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ex : State.addr (s.gpr .r0) = State.addr pf + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.r0]; exact addr_add (by rw [Nat.mul_assoc]; omega)
  have ey : State.addr (s.gpr .r2) = State.addr po + BitVec.ofNat 64 (nb * i) := by
    rw [hI.r2]; exact addr_add (by omega)
  have ha : ∀ j, State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) = coeffAddr (State.addr pf) (c * i + j) :=
    fun j => by rw [ex, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, State.addr (s.gpr .r2) + BitVec.ofNat 64 t = State.addr po + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ey, off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32 =
      coeffAt m₀ (State.addr pf) (c * i + j) :=
    fun j hj => by
      rw [ha j]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega)
  refine WP.mono (packBody_ok hld hs.d20 hs.dc hs.c8 hs.e4c hs.enb s
    (by rw [hI.r0, ptr_toNat (by rw [Nat.mul_assoc]; omega)]; rw [Nat.mul_assoc]; omega)
    (by rw [hI.r2, ptr_toNat (by omega)]; omega)
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact inRegions_of hin (coeff_contains _ (by omega)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hout (Offset.contains_base _ (by omega) (by omega)))
    (by
      rw [ex, ey]
      exact (hsep.sub_left (Offset.sub_base _ (by rw [Nat.mul_assoc]; omega))).sub_right
        (Offset.sub_base _ (by omega)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega)))
    fun s' ⟨hW, x', y', c', z', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r0]; exact ptr_step _ i (4 * c)
  · rw [y', hI.r2]; exact ptr_step _ i nb
  · rw [c', hI.r1]; exact count_sub (k := 1) hi
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2.1, hI.wr]
  · refine hI.frame.trans (hW.1.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [ey]; exact Offset.sub_base _ (by omega)⟩
  · have hE : (bitsToBytes (fieldBits d (vals V m₀ (State.addr pf))))[k]! = _ := rfl
    by_cases hk' : k < nb * i
    · -- Written before.
      rw [← hI.done k hk']
      refine hW.1 _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [ey] at hc
      exact Offset.disjoint (State.addr po) (d := k) (n := 1) (e := nb * i) (k := nb) (by omega) (by omega)
        (by omega) _ (Region.contains_self _ _) hc
    · -- Written by this group.
      have ht : k - nb * i < nb := by rw [Nat.mul_succ] at hk; omega
      have := hW.2 (k - nb * i) ht
      rw [hb, show nb * i + (k - nb * i) = k by omega] at this
      have e : k = nb * i + (k - nb * i) := by omega
      rw [this]
      conv => rhs; rw [e]
      rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (vals_lt hF) ht (by omega),
        take_drop_eq _ 0 (by simp; omega)]
      refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * (k - nb * i)))) (List.map_congr_left fun j hj => ?_)
      have hj := List.mem_range.mp hj
      rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
  · rw [z', hI.r1]; exact count_z (k := 1) hi (by decide) (by omega)

theorem packLoop_ok {s : State} (h0 : s.gpr .r0 = pf) (h2 : s.gpr .r2 = po) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem (State.addr po) (32 * d) = bitsToBytes (fieldBits d (vals V m₀ (State.addr pf))) ∧
        Frame [⟨State.addr po, 32 * d⟩] m₀ s'.mem ∧ Keep packRegs s s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  have hN0 : 0 < 256 / c := Nat.div_pos (by omega) h0'
  unfold packLoop
  refine WP.seq (WP.mono (movN_ok .r1 _ hs.eN s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_ne (PInv V d c nb pf po m₀ rd wr s) hN0
    (fun i hi s' hI => packStep hld hs hin hout hsep fitF fitO hF hi hI)
    (fun s' hI => ⟨bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk),
      hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₁.mono (by decide)⟩
  · rw [k₁.gpr (by decide), h0]; simp
  · rw [k₁.gpr (by decide), h2]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2.1, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

/-! ## Unpacking -/

/-- The number whose bytes are the `32 d` bytes of the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

/-- After `i` groups. -/
structure UInv (W : Nat → BitVec 32) (d c nb : Nat) (pv pp : BitVec 32) (m₀ : Mem) (rd wr : List Region)
    (sE : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pv + BitVec.ofNat 32 (nb * i)
  r1 : s.gpr .r1 = pp + BitVec.ofNat 32 (4 * c * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 / c - i))
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [polyRegion (State.addr pp)] m₀ s.mem
  done : ∀ k < c * i, coeffAt s.mem (State.addr pp) k = W (inNum m₀ (State.addr pv) d / 2 ^ (d * k) % 2 ^ d)
  keep : Keep unpackRegs sE s

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} (hfin : FinOk fin d W)
  (hs : Shape d c nb) {pv pp : BitVec 32} {m₀ : Mem} {rd wr : List Region} {sE : State}
  (hin : (⟨State.addr pv, 32 * d⟩ : Region) ∈ rd ++ wr) (hout : polyRegion (State.addr pp) ∈ wr)
  (hsep : Region.Disjoint ⟨State.addr pv, 32 * d⟩ (polyRegion (State.addr pp)))
  (fitV : pv.toNat + 32 * d ≤ 2 ^ 32) (fitP : pp.toNat + 1024 ≤ 2 ^ 32)
include hfin hs hin hout hsep fitV fitP

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : UInv W d c nb pv pp m₀ rd wr sE i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv W d c nb pv pp m₀ rd wr sE (i + 1) s' ∧ s'.z = decide (i + 1 = 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ex : State.addr (s.gpr .r0) = State.addr pv + BitVec.ofNat 64 (nb * i) := by
    rw [hI.r0]; exact addr_add (by omega)
  have ep : State.addr (s.gpr .r1) = State.addr pp + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.r1]; exact addr_add (by rw [Nat.mul_assoc]; omega)
  have ha : ∀ j, State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j) = coeffAddr (State.addr pp) (c * i + j) :=
    fun j => by rw [ep, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, State.addr (s.gpr .r0) + BitVec.ofNat 64 t = State.addr pv + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ex, off_add]
  have hsub : Region.Sub ⟨State.addr (s.gpr .r1), 4 * c⟩ (polyRegion (State.addr pp)) := by
    rw [ep]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega)
  refine WP.mono (unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 hs.enb hs.e4c s
    (by rw [hI.r0, ptr_toNat (by omega)]; omega)
    (by rw [hI.r1, ptr_toNat (by rw [Nat.mul_assoc]; omega)]; rw [Nat.mul_assoc]; omega)
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact inRegions_of hin (Offset.contains_base _ (by omega) (by omega)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hout (coeff_contains _ (by omega)))
    (by rw [ex]; exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right hsub))
    fun s' ⟨hw, hf, x', p', c', z', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_),
      fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r0]; exact ptr_step _ i nb
  · rw [p', hI.r1]; exact ptr_step _ i (4 * c)
  · rw [c', hI.r2]; exact count_sub (k := 1) hi
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2.1, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  · -- The bytes of the group, on entry.
    have hB : (List.range nb).map (fun t => (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) =
        (((bytesAt m₀ (State.addr pv) (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
      rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega)]
      refine List.map_congr_left fun t ht => ?_
      have ht := List.mem_range.mp ht
      rw [getD_map_toNat, bytesAt_getD _ _ (by omega), hb]
      refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ (Offset.contains_base _ (by omega) (by omega))
    have hlt : ∀ a ∈ (bytesAt m₀ (State.addr pv) (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
    by_cases hk' : k < c * i
    · -- Written before.
      rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
      refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [ep]
      exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega) (by omega) (by rw [Nat.mul_assoc]; omega)
    · -- Written by this group.
      have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega
      have := hw (k - c * i) hj
      rw [ha, show c * i + (k - c * i) = k by omega, hB, digits_group hs.dc hlt hj,
        show c * i + (k - c * i) = k by omega] at this
      rw [coeffAt_eq, this]
  · rw [z', hI.r2]; exact count_z (k := 1) hi (by decide) (by omega)

theorem unpackLoop_ok {s : State} (h0 : s.gpr .r0 = pv) (h1 : s.gpr .r1 = pp) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem (State.addr pp) k = W (inNum m₀ (State.addr pv) d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion (State.addr pp)] m₀ s'.mem ∧ Keep unpackRegs s s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  have hN0 : 0 < 256 / c := Nat.div_pos (by omega) h0'
  unfold unpackLoop
  refine WP.seq (WP.mono (movN_ok .r2 _ hs.eN s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_ne (UInv W d c nb pv pp m₀ rd wr s) hN0
    (fun i hi s' hI => unpackStep hfin hs hin hout hsep fitV fitP hi hI)
    (fun s' hI => ⟨fun k hk => hI.done k (by rw [hs.cN]; exact hk), hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₁.mono (by decide)⟩
  · rw [k₁.gpr (by decide), h0]; simp
  · rw [k₁.gpr (by decide), h1]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2.1, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.Arm.Pack
