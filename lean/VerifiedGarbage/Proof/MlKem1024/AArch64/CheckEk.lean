import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
import VerifiedGarbage.Proof.MlKem.EkCheck1024
import VerifiedGarbage.Impl.MlKem1024.AArch64.CheckEk
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_check_ek`

The modulus check holds exactly when no 12-bit field of `ek[0 : 1536]` is at
least `q` (`ekCheck1024`); the code counts those fields (`cnt`, of
ML-KEM-768's proof) without branching.
-/

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against; the artifact's is the
shared contract of `Spec/`, which implies it. AArch64 contract for
`vg_mlkem1024_check_ek(ek = x0) -> w0`: returns 1 if the 1568 bytes at `ek`
pass the encapsulation key check of ML-KEM-1024, and 0 otherwise. The code
may read `ek`. -/
def checkEk1024AArch64 : Contract AArch64.isa where
  pre s := s.rd = [⟨s.gpr .x0, 1568⟩] ∧ s.wr = []
  post s s' := (s'.gpr .x0).setWidth 32 =
    if ekCheck mlKem1024 (bytesAt s.mem (s.gpr .x0) 1568) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.CheckEk

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64 (checkEkBody)
open VG.Proof.MlKem.AArch64.CheckEk (cnt cnt_le cnt_zero bad_arith)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev eP : Addr := s₀.gpr .x0
abbrev B : List Byte := bytesAt s₀.mem (eP s₀) 1568
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨eP s₀, 1568⟩]
  wr : s₀.wr = []

/-- After `k` groups. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = s₀.mem
  x0 : s.gpr .x0 = eP s₀ + BitVec.ofNat 64 (3 * k)
  x9 : (s.gpr .x9).toNat = 3328
  x10 : (s.gpr .x10).toNat = cnt (B s₀) k
  x11 : (s.gpr .x11).toNat = 512 - k
  x14 : (s.gpr .x14).toNat = 15

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 512) {s : State} (h : Inv s₀ k s) :
    WP isa (.block checkEkBody) s fun s' =>
      Inv s₀ (k + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 512) := by
  have hin : ∀ j < 1568, InRegions (s.rd ++ s.wr) (eP s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  have hb : ∀ j < 1568, (s.mem (eP s₀ + BitVec.ofNat 64 j)).toNat = byte s₀ j := fun j hj => by
    rw [h.mem]
    show _ = ((bytesAt s₀.mem (eP s₀) 1568).getD j 0).toNat
    rw [bytesAt_getD _ _ hj]
  have a : ∀ r, s.gpr .x0 + BitVec.ofNat 64 r = eP s₀ + BitVec.ofNat 64 (3 * k + r) := fun r => by
    rw [h.x0, ptr_add]
  have l0 : byte s₀ (3 * k) < 256 := byte_lt _
  have l1 : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have l2 : byte s₀ (3 * k + 2) < 256 := byte_lt _
  refine wp_ldrb (a := eP s₀ + BitVec.ofNat 64 (3 * k + 0)) (by decide) (a 0) (hin _ (by omega))
    fun s₁ h₁ e₁ => ?_
  refine wp_ldrb (a := eP s₀ + BitVec.ofNat 64 (3 * k + 1)) (by decide) (by rw [h₁.get .x0, a])
    (by rw [h₁.rd, h₁.wr]; exact hin _ (by omega)) fun s₂ h₂ e₂ => ?_
  refine wp_and fun s₃ h₃ e₃ => wp_lsl (by decide) fun s₄ h₄ e₄ => wp_add fun s₅ h₅ e₅ =>
    wp_sub fun s₆ h₆ e₆ => wp_lsr (by decide) fun s₇ h₇ e₇ => wp_add fun s₈ h₈ e₈ => ?_
  have v12 : (s₂.gpr .x12).toNat = byte s₀ (3 * k) := by
    rw [h₂.get .x12, e₁, toNat_byte, Nat.add_zero, hb _ (by omega)]
  have v13 : (s₂.gpr .x13).toNat = byte s₀ (3 * k + 1) := by
    rw [e₂, toNat_byte, h₁.mem, hb _ (by omega)]
  have f0 : (s₅.gpr .x15).toNat = field0 (B s₀) k := by
    have c3 : (s₃.gpr .x15).toNat = byte s₀ (3 * k + 1) % 16 := by
      rw [e₃, toNat_and_mask _ _ (k := 4) (by rw [h₂.get .x14, h₁.get .x14, h.x14]), v13]
    have c4 : (s₄.gpr .x15).toNat = byte s₀ (3 * k + 1) % 16 * 256 := by
      rw [e₄, toNat_lsl_n (by rw [c3]; omega), c3]
    rw [e₅, toNat_add_n (by rw [c4, h₄.get .x12, h₃.get .x12, v12]; omega), c4, h₄.get .x12,
      h₃.get .x12, v12]
    simp only [field0, byte]
    omega
  have ff0 : field0 (B s₀) k < 2 ^ 12 := by unfold field0; omega
  have k₈ := (((((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).trans h₇.keep).trans h₈.keep)
  have v10 : (s₈.gpr .x10).toNat = cnt (B s₀) k + (if field0 (B s₀) k < q then 0 else 1) := by
    have e9 : s₅.gpr .x9 = BitVec.ofNat 64 3328 := by
      rw [h₅.get .x9, h₄.get .x9, h₃.get .x9, h₂.get .x9, h₁.get .x9]
      exact BitVec.eq_of_toNat_eq (by rw [h.x9]; rfl)
    have e15 : s₅.gpr .x15 = BitVec.ofNat 64 (field0 (B s₀) k) := by
      exact BitVec.eq_of_toNat_eq (by rw [f0, toNat_ofNat_lt (by omega)])
    have hbad := bad_arith ff0
    rw [← e9, ← e15, ← e₆] at hbad
    have c7 : (s₇.gpr .x15).toNat = if field0 (B s₀) k < q then 0 else 1 := by rw [e₇]; exact hbad
    have c10 : (s₇.gpr .x10).toNat = cnt (B s₀) k := by
      rw [h₇.get .x10, h₆.get .x10, h₅.get .x10, h₄.get .x10, h₃.get .x10, h₂.get .x10,
        h₁.get .x10, h.x10]
    have := cnt_le (B s₀) k
    rw [e₈, toNat_add_n (by rw [c10, c7]; split <;> omega), c10, c7]
  refine wp_ldrb (a := eP s₀ + BitVec.ofNat 64 (3 * k + 2)) (by decide)
    (by rw [k₈.get .x0, a]) (by rw [k₈.rd, k₈.wr]; exact hin _ (by omega)) fun s₉ h₉ e₉ => ?_
  refine wp_lsr (by decide) fun s₁₀ h₁₀ e₁₀ => wp_lsl (by decide) fun s₁₁ h₁₁ e₁₁ =>
    wp_add fun s₁₂ h₁₂ e₁₂ => wp_sub fun s₁₃ h₁₃ e₁₃ => wp_lsr (by decide) fun s₁₄ h₁₄ e₁₄ =>
    wp_add fun s₁₅ h₁₅ e₁₅ => ?_
  have m₈ : s₈.mem = s.mem := by
    rw [h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have m₉ : s₉.mem = s.mem := by rw [h₉.mem, m₈]
  have f1 : (s₁₂.gpr .x13).toNat = field1 (B s₀) k := by
    have c10 : (s₁₀.gpr .x13).toNat = byte s₀ (3 * k + 1) / 16 := by
      rw [e₁₀, toNat_lsr, h₉.get .x13, h₈.get .x13, h₇.get .x13, h₆.get .x13, h₅.get .x13,
        h₄.get .x13, h₃.get .x13, v13]
    have c11 : (s₁₁.gpr .x12).toNat = byte s₀ (3 * k + 2) * 16 := by
      rw [e₁₁, h₁₀.get .x12, e₉, toNat_lsl_n (by rw [toNat_byte, m₈, hb _ (by omega)]; omega),
        toNat_byte, m₈, hb _ (by omega)]
    rw [e₁₂, toNat_add_n (by rw [h₁₁.get .x13, c10, c11]; omega), h₁₁.get .x13, c10, c11]
    simp only [field1, byte]
    omega
  have ff1 : field1 (B s₀) k < 2 ^ 12 := by unfold field1; omega
  have k₁₂ := ((((k₈.trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep).trans h₁₂.keep)
  have v10' : (s₁₅.gpr .x10).toNat = cnt (B s₀) (k + 1) := by
    have e9 : s₁₂.gpr .x9 = BitVec.ofNat 64 3328 := by
      rw [k₁₂.get .x9]
      exact BitVec.eq_of_toNat_eq (by rw [h.x9]; rfl)
    have e13 : s₁₂.gpr .x13 = BitVec.ofNat 64 (field1 (B s₀) k) := by
      exact BitVec.eq_of_toNat_eq (by rw [f1, toNat_ofNat_lt (by omega)])
    have hbad := bad_arith ff1
    rw [← e9, ← e13, ← e₁₃] at hbad
    have c14 : (s₁₄.gpr .x13).toNat = if field1 (B s₀) k < q then 0 else 1 := by rw [e₁₄]; exact hbad
    have c10 : (s₁₄.gpr .x10).toNat = cnt (B s₀) k + (if field0 (B s₀) k < q then 0 else 1) := by
      rw [h₁₄.get .x10, h₁₃.get .x10, h₁₂.get .x10, h₁₁.get .x10, h₁₀.get .x10, h₉.get .x10, v10]
    have := cnt_le (B s₀) k
    rw [e₁₅, toNat_add_n (by rw [c10, c14]; split <;> split <;> omega), c10, c14]
    rfl
  refine wp_addImm (by decide) fun s₁₆ h₁₆ e₁₆ => wp_subImm (by decide) fun s₁₇ h₁₇ e₁₇ => wp_nil ?_
  have k₁₆ := ((((k₁₂.trans h₁₃.keep).trans h₁₄.keep).trans h₁₅.keep).trans h₁₆.keep)
  have c11 : (s₁₆.gpr .x11).toNat = 512 - k := by rw [k₁₆.get .x11, h.x11]
  have v11 : (s₁₇.gpr .x11).toNat = 512 - (k + 1) := by
    rw [e₁₇, toNat_sub_n (by rw [c11]; simp; omega), c11]
    simp
    omega
  have k₁₇ := k₁₆.trans h₁₇.keep
  refine ⟨⟨by rw [k₁₇.rd, h.rd], by rw [k₁₇.wr, h.wr], by rw [k₁₇.sp, h.sp], ?_, ?_,
    by rw [k₁₇.get .x9, h.x9], by rw [h₁₇.get .x10, h₁₆.get .x10, v10'], v11,
    by rw [k₁₇.get .x14, h.x14]⟩, by rw [v11]; omega⟩
  · rw [h₁₇.mem, h₁₆.mem, h₁₅.mem, h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, m₉, h.mem]
  · rw [h₁₇.get .x0, e₁₆, h₁₅.get .x0, h₁₄.get .x0, h₁₃.get .x0, h₁₂.get .x0, h₁₁.get .x0,
      h₁₀.get .x0, h₉.get .x0, k₈.get .x0, h.x0, ptr_next]

theorem correct (s₀ : State) (hs : checkEk1024AArch64.pre s₀) :
    ∃ t s', Exec isa checkEk s₀ t s' ∧ abiPreserved s₀ s' ∧ checkEk1024AArch64.post s₀ s' := by
  have hp : Pre s₀ := ⟨hs.1, hs.2⟩
  suffices h : WP isa checkEk s₀ fun s' => s'.sp = s₀.sp ∧ checkEk1024AArch64.post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_)
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have i₀ : Inv s₀ 0 s₄ := ⟨k₄.rd, k₄.wr, k₄.sp, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem],
    by rw [k₄.get .x0, Nat.mul_zero, ptr_zero], by rw [h₄.get .x9, h₃.get .x9, h₂.get .x9, e₁]; rfl,
    by rw [h₄.get .x10, h₃.get .x10, e₂]; rfl, by rw [h₄.get .x11, e₃]; rfl, by rw [e₄]; rfl⟩
  refine WP.seq (WP.mono (count_loop (by decide) (Inv s₀) (fun k hk s h => step hp hk h) i₀)
    fun s h => ?_)
  refine wp_subImm (by decide) fun s₅ h₅ e₅ => wp_lsr (by decide) fun s₆ h₆ e₆ => wp_nil ?_
  refine ⟨by rw [h₆.sp, h₅.sp, h.sp], ?_⟩
  have hc := cnt_le (B s₀) 512
  have v : (s₆.gpr .x0).toNat = if cnt (B s₀) 512 = 0 then 1 else 0 := by
    rw [e₆, toNat_lsr, e₅, BitVec.toNat_sub, h.x10]
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  have hck := ekCheck1024 (B s₀) (bytesAt_length _ _ _)
  show (s₆.gpr .x0).setWidth 32 = if ekCheck mlKem1024 (B s₀) then 1 else 0
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, v]
  by_cases e : cnt (B s₀) 512 = 0
  · rw [ite_eq_left e, ite_eq_left (hck.mpr ((cnt_zero _ _).mp e))]; rfl
  · rw [ite_eq_right e, ite_eq_right (fun h' => e ((cnt_zero _ _).mpr (hck.mp h')))]; rfl

theorem ct : ConstantTime isa checkEk1024AArch64.pre checkEk1024AArch64.pub checkEk :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ ⟨h0, hsp⟩ => agree_of hsp (by simp [h0])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩]
  wr := []

theorem checkEk_verified : Verified AArch64.target checkEk (Spec.MlKem1024.checkEkContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, checkEk1024AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem1024.AArch64.CheckEk
