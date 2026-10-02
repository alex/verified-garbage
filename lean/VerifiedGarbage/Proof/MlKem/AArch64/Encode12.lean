import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/-!
# ML-KEM on AArch64: `vg_mlkem_encode12`

Three bytes per pair of coefficients (`encode12_byte0`–`encode12_byte2`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against (and verified callers use);
the artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_mlkem_encode12(f = x0, out = x1)`: if the
polynomial at `f` is reduced, writes `ByteEncode₁₂` of it to the 384 bytes
at `out`. The code may read `f` and write `out`, which do not overlap. -/
def encode12AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x1, 384⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 384⟩ ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x1) 384 = encode12 (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Encode12

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev oP : Addr := s₀.gpr .x1
abbrev oR : Region := ⟨oP s₀, 384⟩
abbrev P : Poly := polyAt s₀.mem (fP s₀)
/-- Byte `j` of the output. -/
def L (j : Nat) : Byte := (encode12 (P s₀))[j]!

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (fP s₀)]
  wr : s₀.wr = [oR s₀]
  disj : (polyRegion (fP s₀)).Disjoint (oR s₀)
  red : Reduced s₀.mem (fP s₀)

/-- After `k` pairs of coefficients. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = fP s₀ + BitVec.ofNat 64 (8 * k)
  x1 : s.gpr .x1 = oP s₀ + BitVec.ofNat 64 (3 * k)
  x13 : (s.gpr .x13).toNat = 128 - k
  out : BytesUpTo s.mem (oP s₀) 384 (3 * k) (L s₀) fun j => s₀.mem (oP s₀ + BitVec.ofNat 64 j)
  frame : Frame [oR s₀] s₀.mem s.mem

theorem Pre.coeff {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [oR s₀] s₀.mem m) {i : Nat}
    (hi : i < 256) : (coeffAt m (fP s₀) i).toNat = ((P s₀)[i]!).val := by
  rw [coeffAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hi,
    polyAt_val hp.red (show i < n from hi)]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : Inv s₀ k s) :
    WP isa (.block encode12Body) s fun s' =>
      Inv s₀ (k + 1) s' ∧ ((s'.gpr .x13).toNat ≠ 0 ↔ k + 1 ≠ 128) := by
  have hin : ∀ i < 256, InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) i) 4 := fun i hi => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi)))
  have hout : ∀ j < 384, InRegions s.wr (oP s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
  have a0 : s.gpr .x0 + BitVec.ofNat 64 0 = coeffAddr (fP s₀) (2 * k) := by
    rw [h.x0, ptr_zero, coeffAddr, show 4 * (2 * k) = 8 * k by omega]
  have a1 : s.gpr .x0 + BitVec.ofNat 64 4 = coeffAddr (fP s₀) (2 * k + 1) := by
    rw [h.x0, ptr_add, coeffAddr, show 8 * k + 4 = 4 * (2 * k + 1) by omega]
  have b0 : s.gpr .x1 + BitVec.ofNat 64 0 = oP s₀ + BitVec.ofNat 64 (3 * k) := by
    rw [h.x1, ptr_zero]
  have b1 : s.gpr .x1 + BitVec.ofNat 64 1 = oP s₀ + BitVec.ofNat 64 (3 * k + 1) := by
    rw [h.x1, ptr_add]
  have b2 : s.gpr .x1 + BitVec.ofNat 64 2 = oP s₀ + BitVec.ofNat 64 (3 * k + 2) := by
    rw [h.x1, ptr_add]
  have va : (coeffAt s.mem (fP s₀) (2 * k)).toNat = ((P s₀)[2 * k]!).val :=
    hp.coeff h.frame (by omega)
  have vb : (coeffAt s.mem (fP s₀) (2 * k + 1)).toNat = ((P s₀)[2 * k + 1]!).val :=
    hp.coeff h.frame (by omega)
  have la := val_lt (P s₀)[2 * k]!
  have lb := val_lt (P s₀)[2 * k + 1]!
  refine wp_ldrw (a := coeffAddr (fP s₀) (2 * k)) (by decide) a0 (hin _ (by omega))
    fun s₁ h₁ e₁ => ?_
  refine wp_ldrw (a := coeffAddr (fP s₀) (2 * k + 1)) (by decide) (by rw [h₁.get .x0]; exact a1)
    (by rw [h₁.rd, h₁.wr]; exact hin _ (by omega)) fun s₂ h₂ e₂ => ?_
  have k₂ := h₁.keep.trans h₂.keep
  have v9 : (s₂.gpr .x9).toNat = ((P s₀)[2 * k]!).val := by
    rw [h₂.get .x9, e₁, toNat_readW32, ← coeffAt_eq, va]
  have v10 : (s₂.gpr .x10).toNat = ((P s₀)[2 * k + 1]!).val := by
    rw [e₂, toNat_readW32, h₁.mem, ← coeffAt_eq, vb]
  refine wp_strb (a := oP s₀ + BitVec.ofNat 64 (3 * k)) (by decide) (by rw [k₂.get .x1]; exact b0)
    (by rw [k₂.wr]; exact hout _ (by omega)) fun s₃ h₃ => ?_
  refine wp_lsr (by decide) fun s₄ h₄ e₄ => wp_lsl (by decide) fun s₅ h₅ e₅ =>
    wp_add fun s₆ h₆ e₆ => ?_
  have k₆ := ((k₂.trans h₃.keep).trans (h₄.keep.trans h₅.keep)).trans h₆.keep
  have v11 : (s₆.gpr .x11).toNat = ((P s₀)[2 * k]!).val / 256 + ((P s₀)[2 * k + 1]!).val * 16 := by
    have c9 : (s₃.gpr .x9).toNat = ((P s₀)[2 * k]!).val := by rw [h₃.gpr, v9]
    have c10 : (s₄.gpr .x10).toNat = ((P s₀)[2 * k + 1]!).val := by
      rw [h₄.get .x10, h₃.gpr, v10]
    have d11 : (s₅.gpr .x11).toNat = ((P s₀)[2 * k]!).val / 256 := by
      rw [h₅.get .x11, e₄, toNat_lsr, c9]
    have d12 : (s₅.gpr .x12).toNat = ((P s₀)[2 * k + 1]!).val * 16 := by
      rw [e₅, toNat_lsl_n (by rw [c10]; omega), c10]
    rw [e₆, toNat_add_n (by rw [d11, d12]; omega), d11, d12]
  refine wp_strb (a := oP s₀ + BitVec.ofNat 64 (3 * k + 1)) (by decide) (by rw [k₆.get .x1]; exact b1)
    (by rw [k₆.wr]; exact hout _ (by omega)) fun s₇ h₇ => ?_
  refine wp_lsr (by decide) fun s₈ h₈ e₈ => ?_
  have k₈ := (k₆.trans h₇.keep).trans h₈.keep
  refine wp_strb (a := oP s₀ + BitVec.ofNat 64 (3 * k + 2)) (by decide) (by rw [k₈.get .x1]; exact b2)
    (by rw [k₈.wr]; exact hout _ (by omega)) fun s₉ h₉ => ?_
  refine wp_addImm (by decide) fun s₁₀ h₁₀ e₁₀ => wp_addImm (by decide) fun s₁₁ h₁₁ e₁₁ =>
    wp_subImm (by decide) fun s₁₂ h₁₂ e₁₂ => wp_nil ?_
  have k₁₂ := (((k₈.trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep).trans h₁₂.keep
  -- The three bytes.
  have y0 : (s₂.gpr .x9).setWidth 8 = L s₀ (3 * k) := by
    rw [setWidth8_of_toNat v9, L, encode12_byte0 _ hk, ofNat8_mod]
  have y1 : (s₆.gpr .x11).setWidth 8 = L s₀ (3 * k + 1) := by
    rw [setWidth8_of_toNat v11, L, encode12_byte1 _ hk]
    exact ofNat8_eq (by omega)
  have y2 : (s₈.gpr .x12).setWidth 8 = L s₀ (3 * k + 2) := by
    have c10 : (s₇.gpr .x10).toNat = ((P s₀)[2 * k + 1]!).val := by
      rw [h₇.gpr, h₆.get .x10, h₅.get .x10, h₄.get .x10, h₃.gpr, v10]
    rw [setWidth8_of_toNat (x := s₈.gpr .x12) (n := ((P s₀)[2 * k + 1]!).val / 16)
      (by rw [e₈, toNat_lsr, c10]), L, encode12_byte2 _ hk]
  have m₁₂ : s₁₂.mem = ((s.mem.writeW (oP s₀ + BitVec.ofNat 64 (3 * k)) ((s₂.gpr .x9).setWidth 8)).writeW
      (oP s₀ + BitVec.ofNat 64 (3 * k + 1)) ((s₆.gpr .x11).setWidth 8)).writeW
      (oP s₀ + BitVec.ofNat 64 (3 * k + 2)) ((s₈.gpr .x12).setWidth 8) := by
    rw [h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem,
      h₁.mem]
  have k₉ := k₈.trans h₉.keep
  have k₁₁ := (k₉.trans h₁₀.keep).trans h₁₁.keep
  have c13 : (s₁₁.gpr .x13).toNat = 128 - k := by rw [k₁₁.get .x13, h.x13]
  have v13 : (s₁₂.gpr .x13).toNat = 128 - (k + 1) := by
    rw [e₁₂, toNat_sub_n (by rw [c13]; simp; omega), c13]
    simp
    omega
  have ct : ∀ j < 384, (oR s₀).Contains (oP s₀ + BitVec.ofNat 64 j) (8 / 8) := fun j hj =>
    contains_off (by omega) (by decide)
  refine ⟨⟨by rw [k₁₂.rd, h.rd], by rw [k₁₂.wr, h.wr], by rw [k₁₂.sp, h.sp], ?_, ?_, v13, ?_, ?_⟩,
    by rw [v13]; omega⟩
  · rw [h₁₂.get .x0, h₁₁.get .x0, e₁₀, k₉.get .x0, h.x0, ptr_next]
  · rw [h₁₂.get .x1, e₁₁, h₁₀.get .x1, k₉.get .x1, h.x1, ptr_next]
  · rw [m₁₂, show 3 * (k + 1) = 3 * k + 2 + 1 by omega]
    exact ((h.out.write (by decide) (by omega) y0).write (by decide) (by omega) y1).write (by decide)
      (by omega) y2
  · rw [m₁₂]
    exact ((h.frame.writeW (List.mem_singleton_self _) _ (ct _ (by omega))).writeW
      (List.mem_singleton_self _) _ (ct _ (by omega))).writeW (List.mem_singleton_self _) _
      (ct _ (by omega))

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa encode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_nil ?_)
  refine count_loop (by decide) (Inv s₀) (fun k hk s h => step hp hk h) ?_
  refine ⟨h₁.rd, h₁.wr, h₁.sp, by rw [h₁.get .x0, Nat.mul_zero, ptr_zero],
    by rw [h₁.get .x1, Nat.mul_zero, ptr_zero], by rw [e₁, toNat_imm]; rfl, ?_, ?_⟩
  · rw [h₁.mem, Nat.mul_zero]; exact BytesUpTo.zero _
  · rw [h₁.mem]; exact Frame.refl _ _

theorem correct (s : State) (hs : encode12AArch64.pre s) :
    ∃ t s', Exec isa encode12 s t s' ∧ abiPreserved s s' ∧ encode12AArch64.post s s' := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  obtain ⟨t, s', he, hI⟩ := loop_ok (s₀ := s) ⟨h1, h2, h3, h4⟩
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he,
    (show BytesUpTo s'.mem (oP s) 384 384 _ _ from hI.out).eq (encode12_length _) fun _ _ => rfl⟩

theorem ct : ConstantTime isa encode12AArch64.pre encode12AArch64.pub encode12 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 384⟩]

theorem encode12_verified :
    Verified AArch64.target encode12 (Spec.MlKem.encode12Contract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.encode12Contract, Spec.MlKem.encode12Sig, encode12AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Encode12
