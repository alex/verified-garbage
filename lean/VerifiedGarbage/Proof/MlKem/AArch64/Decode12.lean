import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/-!
# ML-KEM on AArch64: `vg_mlkem_decode12`

Untrusted: everything here is checked by Lean. Two coefficients per three
bytes (`decode12_even`, `decode12_odd`), each less than `2¹² < 2q` and
reduced with one conditional subtraction.
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against (and verified callers use);
the artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_mlkem_decode12(b = x0, f = x1)`: writes
`ByteDecode₁₂` of the 384 bytes at `b` to `f`, reduced. The code may read
`b` and write `f`, which do not overlap. -/
def decode12AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 384⟩] ∧ s.wr = [⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 384⟩ ⟨s.gpr .x1, 1024⟩
  post s s' := PolyIs s'.mem (s.gpr .x1) (decode12 (bytesAt s.mem (s.gpr .x0) 384))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Decode12

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev bR : Region := ⟨bP s₀, 384⟩
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) 384
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decode12 (B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fP s₀)]
  disj : (bR s₀).Disjoint (polyRegion (fP s₀))

/-- After `k` groups of three bytes. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (3 * k)
  x1 : s.gpr .x1 = fP s₀ + BitVec.ofNat 64 (8 * k)
  x14 : (s.gpr .x14).toNat = 15
  x15 : (s.gpr .x15).toNat = q
  x16 : (s.gpr .x16).toNat = 128 - k
  out : CoeffsUpTo s.mem (fP s₀) (2 * k) (G s₀) fun i => coeffAt s₀.mem (fP s₀) i
  frame : Frame [polyRegion (fP s₀)] s₀.mem s.mem

theorem Pre.byte_eq {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [polyRegion (fP s₀)] s₀.mem m)
    {j : Nat} (hj : j < 384) : (m (bP s₀ + BitVec.ofNat 64 j)).toNat = byte s₀ j := by
  rw [byte_frame (len := 384) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (bP s₀) 384).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

theorem G_even (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k) = BitVec.ofNat 32 (condSub (byte s₀ (3 * k) + (byte s₀ (3 * k + 1) % 16) * 256)) := by
  have : byte s₀ (3 * k) < 256 := byte_lt _
  have : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have : ((B s₀).getD (3 * k) 0).toNat < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 1) 0).toNat < 256 := byte_lt _
  have hq : q = 3329 := rfl
  rw [G, decode12_even _ (bytesAt_length _ _ _) hk, val_ofNat, condSub_eq (by omega), Nat.mul_comm 256]

theorem G_odd (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k + 1) = BitVec.ofNat 32 (condSub (byte s₀ (3 * k + 1) / 16 + byte s₀ (3 * k + 2) * 16)) := by
  have : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have : byte s₀ (3 * k + 2) < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 1) 0).toNat < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 2) 0).toNat < 256 := byte_lt _
  have hq : q = 3329 := rfl
  rw [G, decode12_odd _ (bytesAt_length _ _ _) hk, val_ofNat, condSub_eq (by omega), Nat.mul_comm 16]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : Inv s₀ k s) :
    WP isa (.block decode12Body) s fun s' =>
      Inv s₀ (k + 1) s' ∧ ((s'.gpr .x16).toNat ≠ 0 ↔ k + 1 ≠ 128) := by
  have hq : q = 3329 := rfl
  have hin : ∀ j < 384, InRegions (s.rd ++ s.wr) (bP s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  have hout : ∀ i < 256, InRegions s.wr (coeffAddr (fP s₀) i) 4 := fun i hi => by
    rw [h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi))
  have a : ∀ r, s.gpr .x0 + BitVec.ofNat 64 r = bP s₀ + BitVec.ofNat 64 (3 * k + r) := fun r => by
    rw [h.x0, ptr_add]
  have c0 : s.gpr .x1 + BitVec.ofNat 64 0 = coeffAddr (fP s₀) (2 * k) := by
    rw [h.x1, ptr_zero, coeffAddr, show 4 * (2 * k) = 8 * k by omega]
  have c1 : s.gpr .x1 + BitVec.ofNat 64 4 = coeffAddr (fP s₀) (2 * k + 1) := by
    rw [h.x1, ptr_add, coeffAddr, show 8 * k + 4 = 4 * (2 * k + 1) by omega]
  have y0 := hp.byte_eq h.frame (j := 3 * k) (by omega)
  have y1 := hp.byte_eq h.frame (j := 3 * k + 1) (by omega)
  have y2 := hp.byte_eq h.frame (j := 3 * k + 2) (by omega)
  have l0 := byte_lt ((B s₀).getD (3 * k) 0)
  have l1 := byte_lt ((B s₀).getD (3 * k + 1) 0)
  have l2 := byte_lt ((B s₀).getD (3 * k + 2) 0)
  refine wp_ldrb (a := bP s₀ + BitVec.ofNat 64 (3 * k + 0)) (by decide) (a 0)
    (hin _ (by omega)) fun s₁ h₁ e₁ => ?_
  refine wp_ldrb (a := bP s₀ + BitVec.ofNat 64 (3 * k + 1)) (by decide) (by rw [h₁.get .x0, a])
    (by rw [h₁.rd, h₁.wr]; exact hin _ (by omega)) fun s₂ h₂ e₂ => ?_
  refine wp_ldrb (a := bP s₀ + BitVec.ofNat 64 (3 * k + 2)) (by decide)
    (by rw [h₂.get .x0, h₁.get .x0, a]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hin _ (by omega))
    fun s₃ h₃ e₃ => ?_
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have v9 : (s₃.gpr .x9).toNat = byte s₀ (3 * k) := by
    rw [h₃.get .x9, h₂.get .x9, e₁, toNat_byte, Nat.add_zero, y0]
  have v10 : (s₃.gpr .x10).toNat = byte s₀ (3 * k + 1) := by
    rw [h₃.get .x10, e₂, toNat_byte, h₁.mem, y1]
  have v11 : (s₃.gpr .x11).toNat = byte s₀ (3 * k + 2) := by
    rw [e₃, toNat_byte, h₂.mem, h₁.mem, y2]
  refine wp_and fun s₄ h₄ e₄ => wp_lsl (by decide) fun s₅ h₅ e₅ => wp_add fun s₆ h₆ e₆ => ?_
  have v12 : (s₆.gpr .x12).toNat = byte s₀ (3 * k) + (byte s₀ (3 * k + 1) % 16) * 256 := by
    have d₄ : (s₄.gpr .x12).toNat = byte s₀ (3 * k + 1) % 16 := by
      rw [e₄, toNat_and_mask _ _ (k := 4) (by rw [k₃.get .x14, h.x14]), v10]
    have d₅ : (s₅.gpr .x12).toNat = (byte s₀ (3 * k + 1) % 16) * 256 := by
      rw [e₅, toNat_lsl_n (by rw [d₄]; omega), d₄]
    rw [e₆, toNat_add_n (by rw [d₅, h₅.get .x9, h₄.get .x9, v9]; omega), d₅, h₅.get .x9,
      h₄.get .x9, v9, Nat.add_comm]
  have k₆ := ((k₃.trans h₄.keep).trans h₅.keep).trans h₆.keep
  refine csub_ok (by decide) (by decide) (by decide) (by rw [hq]; omega) v12
    (by rw [k₆.get .x15, h.x15]) fun s₇ h₇ e₇ => ?_
  have k₇ := k₆.trans h₇.keep
  refine wp_strw (a := coeffAddr (fP s₀) (2 * k)) (by decide) (by rw [k₇.get .x1]; exact c0)
    (by rw [k₇.wr]; exact hout _ (by omega)) fun s₈ h₈ => ?_
  refine wp_lsr (by decide) fun s₉ h₉ e₉ => wp_lsl (by decide) fun s₁₀ h₁₀ e₁₀ =>
    wp_add fun s₁₁ h₁₁ e₁₁ => ?_
  have k₁₁ := (((k₇.trans h₈.keep).trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep
  have v12' : (s₁₁.gpr .x12).toNat = byte s₀ (3 * k + 1) / 16 + byte s₀ (3 * k + 2) * 16 := by
    have d₉ : (s₉.gpr .x12).toNat = byte s₀ (3 * k + 1) / 16 := by
      rw [e₉, toNat_lsr]
      simp (disch := decide) only [h₈.gpr, h₇.gpr, h₆.gpr, h₅.gpr, h₄.gpr]
      rw [v10]
    have d₁₀ : (s₁₀.gpr .x13).toNat = byte s₀ (3 * k + 2) * 16 := by
      rw [e₁₀]
      simp (disch := decide) only [h₉.gpr, h₈.gpr, h₇.gpr, h₆.gpr, h₅.gpr, h₄.gpr]
      rw [toNat_lsl_n (by rw [v11]; omega), v11]
    rw [e₁₁, h₁₀.get .x12, toNat_add_n (by rw [d₉, d₁₀]; omega), d₉, d₁₀]
  refine csub_ok (by decide) (by decide) (by decide) (by rw [hq]; omega) v12'
    (by rw [k₁₁.get .x15, h.x15]) fun s₁₂ h₁₂ e₁₂ => ?_
  have k₁₂ := k₁₁.trans h₁₂.keep
  refine wp_strw (a := coeffAddr (fP s₀) (2 * k + 1)) (by decide) (by rw [k₁₂.get .x1]; exact c1)
    (by rw [k₁₂.wr]; exact hout _ (by omega)) fun s₁₃ h₁₃ => ?_
  refine wp_addImm (by decide) fun s₁₄ h₁₄ e₁₄ => wp_addImm (by decide) fun s₁₅ h₁₅ e₁₅ =>
    wp_subImm (by decide) fun s₁₆ h₁₆ e₁₆ => wp_nil ?_
  have k₁₃ := k₁₂.trans h₁₃.keep
  have k₁₅ := (k₁₃.trans h₁₄.keep).trans h₁₅.keep
  have k₁₆ := k₁₅.trans h₁₆.keep
  have m₁₆ : s₁₆.mem = (s.mem.writeW (coeffAddr (fP s₀) (2 * k)) ((s₇.gpr .x12).setWidth 32)).writeW
      (coeffAddr (fP s₀) (2 * k + 1)) ((s₁₂.gpr .x12).setWidth 32) := by
    rw [h₁₆.mem, h₁₅.mem, h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem,
      h₆.mem, h₅.mem, h₄.mem, m₃]
  have c16 : (s₁₅.gpr .x16).toNat = 128 - k := by rw [k₁₅.get .x16, h.x16]
  have v16 : (s₁₆.gpr .x16).toNat = 128 - (k + 1) := by
    rw [e₁₆, toNat_sub_n (by rw [c16]; simp; omega), c16]
    simp
    omega
  refine ⟨⟨by rw [k₁₆.rd, h.rd], by rw [k₁₆.wr, h.wr], by rw [k₁₆.sp, h.sp], ?_, ?_,
    by rw [k₁₆.get .x14, h.x14], by rw [k₁₆.get .x15, h.x15], v16, ?_, ?_⟩, by rw [v16]; omega⟩
  · rw [h₁₆.get .x0, h₁₅.get .x0, e₁₄, k₁₃.get .x0, h.x0, ptr_next]
  · rw [h₁₆.get .x1, e₁₅, h₁₄.get .x1, k₁₃.get .x1, h.x1, ptr_next]
  · rw [m₁₆, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    exact (h.out.write (by omega) (by rw [setWidth32_of_toNat e₇, G_even _ hk])).write (by omega)
      (by rw [setWidth32_of_toNat e₁₂, G_odd _ hk])
  · rw [m₁₆]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * k < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * k + 1 < 256 by omega))

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa decode12 s₀ (Inv s₀ 128) := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_nil ?_)
  refine count_loop (by decide) (Inv s₀) (fun k hk s h => step hp hk h) ?_
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s₀.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, Nat.mul_zero, ptr_zero],
    by rw [k₃.get .x1, Nat.mul_zero, ptr_zero], by rw [h₃.get .x14, h₂.get .x14, e₁, toNat_imm]; rfl,
    by rw [h₃.get .x15, e₂, toNat_imm]; rfl, by rw [e₃, toNat_imm]; rfl, ?_, ?_⟩
  · rw [m₃, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · rw [m₃]; exact Frame.refl _ _

theorem correct (s : State) (hs : decode12AArch64.pre s) :
    ∃ t s', Exec isa decode12 s t s' ∧ abiPreserved s s' ∧ decode12AArch64.post s s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨t, s', he, hI⟩ := loop_ok (s₀ := s) ⟨h1, h2, h3⟩
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he,
    (show CoeffsUpTo s'.mem (fP s) 256 _ _ from hI.out).polyIs fun _ _ => rfl⟩

theorem ct : ConstantTime isa decode12AArch64.pre decode12AArch64.pub decode12 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 1024⟩]

theorem decode12_verified :
    Verified AArch64.target decode12 (Spec.MlKem.decode12Contract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.decode12Contract, Spec.MlKem.decode12Sig, decode12AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Decode12
