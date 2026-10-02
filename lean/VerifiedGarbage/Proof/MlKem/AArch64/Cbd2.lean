import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/-!
# ML-KEM on AArch64: `vg_mlkem_cbd2`

Two coefficients per byte (`samplePolyCBD2_val`): the sums of the pairs of
bits of a byte `v`, `s = (v & 0x55) + ((v >> 1) & 0x55)`, are `x` and `y` of
both nibbles (`sums`, checked for every byte by the kernel).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_cbd2(b = x0, f = x1)`: writes
`SamplePolyCBD₂` of the 128 bytes at `b` to `f`, reduced. The code may read
`b` and write `f`, which do not overlap. -/
def cbd2AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 128⟩] ∧ s.wr = [⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x1, 1024⟩
  post s s' := PolyIs s'.mem (s.gpr .x1) (samplePolyCBD 2 (bytesAt s.mem (s.gpr .x0) 128))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Cbd2

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The sums of pairs of bits of a byte. -/
def sums (v : Nat) : Nat := (v &&& 85) + (v / 2 &&& 85)

theorem sums_ok : ∀ v < 256, sums v % 4 = cbdX v ∧ sums v / 4 % 4 = cbdY v ∧
    sums v / 16 % 4 = cbdX (v / 16) ∧ sums v / 64 = cbdY (v / 16) ∧ sums v < 256 := by
  decide +kernel

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev bR : Region := ⟨bP s₀, 128⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) 128
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((samplePolyCBD 2 (B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

theorem G_even (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k) = BitVec.ofNat 32 (condSub (sums (byte s₀ k) % 4 + q - sums (byte s₀ k) / 4 % 4)) := by
  have hv : byte s₀ k < 256 := byte_lt _
  have hq : q = 3329 := rfl
  obtain ⟨e1, e2, -, -, -⟩ := sums_ok _ hv
  have := cbdX_le (byte s₀ k)
  have := cbdY_le (byte s₀ k)
  rw [G, samplePolyCBD2_val _ (show 2 * k < n by rw [n_eq]; omega), e1, e2, condSub_eq (by omega)]
  refine congrArg (BitVec.ofNat 32) (congrArg (· % q) ?_)
  simp only [nibble, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, Nat.pow_zero,
    Nat.div_one]

theorem G_odd (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k + 1) = BitVec.ofNat 32 (condSub (sums (byte s₀ k) / 16 % 4 + q - sums (byte s₀ k) / 64)) := by
  have hv : byte s₀ k < 256 := byte_lt _
  have hq : q = 3329 := rfl
  obtain ⟨-, -, e1, e2, -⟩ := sums_ok _ hv
  have := cbdX_le (byte s₀ k / 16)
  have := cbdY_le (byte s₀ k / 16)
  rw [G, samplePolyCBD2_val _ (show 2 * k + 1 < n by rw [n_eq]; omega), e1, e2, condSub_eq (by omega)]
  refine congrArg (BitVec.ofNat 32) (congrArg (· % q) ?_)
  simp only [nibble, show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega, Nat.pow_one]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR s₀).Disjoint (polyRegion (fP s₀))

/-- After `k` bytes. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 k
  x1 : s.gpr .x1 = fP s₀ + BitVec.ofNat 64 (8 * k)
  x12 : (s.gpr .x12).toNat = q
  x14 : (s.gpr .x14).toNat = 85
  x15 : (s.gpr .x15).toNat = 3
  x16 : (s.gpr .x16).toNat = 128 - k
  out : CoeffsUpTo s.mem (fP s₀) (2 * k) (G s₀) fun i => coeffAt s₀.mem (fP s₀) i
  frame : Frame [polyRegion (fP s₀)] s₀.mem s.mem

theorem Pre.byte_eq {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [polyRegion (fP s₀)] s₀.mem m)
    {j : Nat} (hj : j < 128) : (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte s₀ j := by
  rw [byte_frame (len := 128) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) 128).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : Inv s₀ k s) :
    WP isa (.block cbd2Body) s fun s' =>
      Inv s₀ (k + 1) s' ∧ ((s'.gpr .x16).toNat ≠ 0 ↔ k + 1 ≠ 128) := by
  have hq : q = 3329 := rfl
  have hv : byte s₀ k < 256 := byte_lt _
  obtain ⟨-, -, -, -, hS⟩ := sums_ok _ hv
  have c0 : s.gpr .x1 + BitVec.ofNat 64 0 = coeffAddr (fP s₀) (2 * k) := by
    rw [h.x1, ptr_zero, coeffAddr, show 4 * (2 * k) = 8 * k by omega]
  have c1 : s.gpr .x1 + BitVec.ofNat 64 4 = coeffAddr (fP s₀) (2 * k + 1) := by
    rw [h.x1, ptr_add, coeffAddr, show 8 * k + 4 = 4 * (2 * k + 1) by omega]
  have hout : ∀ i < 256, InRegions s.wr (coeffAddr (fP s₀) i) 4 := fun i hi => by
    rw [h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi))
  refine wp_ldrb (a := bP s₀ + BitVec.ofNat 64 k) (by decide) (by rw [h.x0, ptr_zero]) ?_
    fun s₁ h₁ e₁ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  have v9 : (s₁.gpr .x9).toNat = byte s₀ k := by rw [e₁, toNat_byte, hp.byte_eq h.frame hk]
  refine wp_lsr (by decide) fun s₂ h₂ e₂ => wp_and fun s₃ h₃ e₃ => wp_and fun s₄ h₄ e₄ =>
    wp_add fun s₅ h₅ e₅ => ?_
  have k₅ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep
  have a3 : (s₃.gpr .x9).toNat = byte s₀ k &&& 85 := by
    rw [e₃, BitVec.toNat_and, h₂.get .x9, v9]
    simp (disch := decide) only [h₂.gpr, h₁.gpr]
    rw [h.x14]
  have a4 : (s₄.gpr .x10).toNat = byte s₀ k / 2 &&& 85 := by
    rw [e₄, BitVec.toNat_and, h₃.get .x10, e₂, toNat_lsr, v9]
    simp (disch := decide) only [h₃.gpr, h₂.gpr, h₁.gpr]
    rw [h.x14]
  have x9 : (s₅.gpr .x9).toNat = sums (byte s₀ k) := by
    have b3 := Nat.and_le_right (n := byte s₀ k) (m := 85)
    have b4 := Nat.and_le_right (n := byte s₀ k / 2) (m := 85)
    rw [e₅, toNat_add_n (by rw [h₄.get .x9, a3, a4]; omega), h₄.get .x9, a3, a4]
    rfl
  refine wp_and fun s₆ h₆ e₆ => wp_lsr (by decide) fun s₇ h₇ e₇ => wp_and fun s₈ h₈ e₈ =>
    wp_add fun s₉ h₉ e₉ => wp_sub fun s₁₀ h₁₀ e₁₀ => ?_
  have k₁₀ := ((((k₅.trans h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep
  have x15 : ∀ {t : State}, t.gpr .x15 = s.gpr .x15 → (t.gpr .x15).toNat = 2 ^ 2 - 1 := fun e => by
    rw [e, h.x15]
  have x12 : ∀ {t : State}, t.gpr .x12 = s.gpr .x12 → (t.gpr .x12).toNat = q := fun e => by
    rw [e, h.x12]
  have v6 : (s₆.gpr .x10).toNat = sums (byte s₀ k) % 4 := by
    rw [e₆, toNat_and_mask _ _ (x15 (k₅.get .x15)), x9]
  have v8 : (s₈.gpr .x11).toNat = sums (byte s₀ k) / 4 % 4 := by
    rw [e₈, toNat_and_mask _ _ (x15 ((k₅.trans h₆.keep).trans h₇.keep |>.get .x15)), e₇, toNat_lsr,
      h₆.get .x9, x9]
  have v9' : (s₉.gpr .x10).toNat = sums (byte s₀ k) % 4 + q := by
    rw [e₉, toNat_add_n (by rw [h₈.get .x10, h₇.get .x10, v6, x12 (((k₅.trans h₆.keep).trans
      h₇.keep).trans h₈.keep |>.get .x12)]; omega), h₈.get .x10, h₇.get .x10, v6,
      x12 (((k₅.trans h₆.keep).trans h₇.keep).trans h₈.keep |>.get .x12)]
  have v10 : (s₁₀.gpr .x10).toNat = sums (byte s₀ k) % 4 + q - sums (byte s₀ k) / 4 % 4 := by
    rw [e₁₀, toNat_sub_n (by rw [v9', h₉.get .x11, v8]; omega), v9', h₉.get .x11, v8]
  refine csub_ok (by decide) (by decide) (by decide) (by rw [hq]; omega) v10
    (x12 (k₁₀.get .x12)) fun s₁₁ h₁₁ e₁₁ => ?_
  have k₁₁ := k₁₀.trans h₁₁.keep
  refine wp_strw (a := coeffAddr (fP s₀) (2 * k)) (by decide) (by rw [k₁₁.get .x1]; exact c0)
    (by rw [k₁₁.wr]; exact hout _ (by omega)) fun s₁₂ h₁₂ => ?_
  refine wp_lsr (by decide) fun s₁₃ h₁₃ e₁₃ => wp_and fun s₁₄ h₁₄ e₁₄ =>
    wp_lsr (by decide) fun s₁₅ h₁₅ e₁₅ => wp_add fun s₁₆ h₁₆ e₁₆ => wp_sub fun s₁₇ h₁₇ e₁₇ => ?_
  have k₁₇ := ((((k₁₁.trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep).trans h₁₅.keep).trans
    h₁₆.keep |>.trans h₁₇.keep
  have y9 : (s₁₂.gpr .x9).toNat = sums (byte s₀ k) := by
    rw [h₁₂.gpr, (((((h₆.keep.trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep).trans
      h₁₁.keep).get .x9, x9]
  have v14 : (s₁₄.gpr .x10).toNat = sums (byte s₀ k) / 16 % 4 := by
    rw [e₁₄, toNat_and_mask _ _ (x15 ((k₁₁.trans h₁₂.keep).trans h₁₃.keep |>.get .x15)), e₁₃,
      toNat_lsr, y9]
  have v15 : (s₁₅.gpr .x11).toNat = sums (byte s₀ k) / 64 := by
    rw [e₁₅, toNat_lsr, h₁₄.get .x9, h₁₃.get .x9, y9]
  have v16 : (s₁₆.gpr .x10).toNat = sums (byte s₀ k) / 16 % 4 + q := by
    have e12 := x12 ((((k₁₁.trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep).trans h₁₅.keep |>.get .x12)
    rw [e₁₆, toNat_add_n (by rw [h₁₅.get .x10, v14, e12]; omega), h₁₅.get .x10, v14, e12]
  have v17 : (s₁₇.gpr .x10).toNat = sums (byte s₀ k) / 16 % 4 + q - sums (byte s₀ k) / 64 := by
    rw [e₁₇, toNat_sub_n (by rw [v16, h₁₆.get .x11, v15]; omega), v16, h₁₆.get .x11, v15]
  refine csub_ok (by decide) (by decide) (by decide) (by rw [hq]; omega) v17
    (x12 (k₁₇.get .x12)) fun s₁₈ h₁₈ e₁₈ => ?_
  have k₁₈ := k₁₇.trans h₁₈.keep
  refine wp_strw (a := coeffAddr (fP s₀) (2 * k + 1)) (by decide) (by rw [k₁₈.get .x1]; exact c1)
    (by rw [k₁₈.wr]; exact hout _ (by omega)) fun s₁₉ h₁₉ => ?_
  refine wp_addImm (by decide) fun s₂₀ h₂₀ e₂₀ => wp_addImm (by decide) fun s₂₁ h₂₁ e₂₁ =>
    wp_subImm (by decide) fun s₂₂ h₂₂ e₂₂ => wp_nil ?_
  have k₁₉ := k₁₈.trans h₁₉.keep
  have k₂₁ := (k₁₉.trans h₂₀.keep).trans h₂₁.keep
  have k₂₂ := k₂₁.trans h₂₂.keep
  have m₂₂ : s₂₂.mem = (s.mem.writeW (coeffAddr (fP s₀) (2 * k)) ((s₁₁.gpr .x10).setWidth 32)).writeW
      (coeffAddr (fP s₀) (2 * k + 1)) ((s₁₈.gpr .x10).setWidth 32) := by
    rw [h₂₂.mem, h₂₁.mem, h₂₀.mem, h₁₉.mem, h₁₈.mem, h₁₇.mem, h₁₆.mem, h₁₅.mem, h₁₄.mem, h₁₃.mem,
      h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem,
      h₁.mem]
  have c16 : (s₂₁.gpr .x16).toNat = 128 - k := by rw [k₂₁.get .x16, h.x16]
  have w16 : (s₂₂.gpr .x16).toNat = 128 - (k + 1) := by
    rw [e₂₂, toNat_sub_n (by rw [c16]; simp; omega), c16]
    simp
    omega
  refine ⟨⟨by rw [k₂₂.rd, h.rd], by rw [k₂₂.wr, h.wr], by rw [k₂₂.sp, h.sp], ?_, ?_,
    by rw [k₂₂.get .x12, h.x12], by rw [k₂₂.get .x14, h.x14], by rw [k₂₂.get .x15, h.x15], w16, ?_,
    ?_⟩, by rw [w16]; omega⟩
  · rw [h₂₂.get .x0, h₂₁.get .x0, e₂₀, k₁₉.get .x0, h.x0, ptr_add]
  · rw [h₂₂.get .x1, e₂₁, h₂₀.get .x1, k₁₉.get .x1, h.x1, ptr_next]
  · rw [m₂₂, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    exact (h.out.write (by omega) (by rw [setWidth32_of_toNat e₁₁, G_even _ hk])).write (by omega)
      (by rw [setWidth32_of_toNat e₁₈, G_odd _ hk])
  · rw [m₂₂]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * k < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * k + 1 < 256 by omega))

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa cbd2 s₀ (Inv s₀ 128) := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_)
  refine count_loop (by decide) (Inv s₀) (fun k hk s h => step hp hk h) ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : s₄.mem = s₀.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨k₄.rd, k₄.wr, k₄.sp, by rw [k₄.get .x0, ptr_zero],
    by rw [k₄.get .x1, Nat.mul_zero, ptr_zero], by rw [h₄.get .x12, e₃, toNat_imm]; rfl,
    by rw [h₄.get .x14, h₃.get .x14, h₂.get .x14, e₁, toNat_imm]; rfl,
    by rw [h₄.get .x15, h₃.get .x15, e₂, toNat_imm]; rfl, by rw [e₄, toNat_imm]; rfl, ?_, ?_⟩
  · rw [m₄, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · rw [m₄]; exact Frame.refl _ _

theorem correct (s : State) (hs : cbd2AArch64.pre s) :
    ∃ t s', Exec isa cbd2 s t s' ∧ abiPreserved s s' ∧ cbd2AArch64.post s s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨t, s', he, hI⟩ := loop_ok (s₀ := s) ⟨h1, h2, h3⟩
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he,
    (show CoeffsUpTo s'.mem (fP s) 256 _ _ from hI.out).polyIs fun _ _ => rfl⟩

theorem ct : ConstantTime isa cbd2AArch64.pre cbd2AArch64.pub cbd2 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem cbd2_verified : Verified AArch64.target cbd2 (Spec.MlKem.cbd2Contract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, cbd2AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Cbd2
