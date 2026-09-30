import VerifiedGarbage.Impl.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.Ops

/-! Untrusted: constants and copies in the field workspace. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem slot_range (o : Slot) : FieldRange (offset o) := by
  constructor <;> simp only [offset] <;> omega

theorem limbs_nat (x : Nat) (hx : x < 2 ^ 256) :
    val4 (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2 ^ 64))
      (BitVec.ofNat 64 (x / 2 ^ 128)) (BitVec.ofNat 64 (x / 2 ^ 192)) = x := by
  simp only [val4, BitVec.toNat_ofNat]
  omega

theorem constWords_ok (s : State) (v : Spec.X25519.Fe) :
    WP isa (.block (constWords v)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = v.val ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  rw [constWords, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const64_ok s _ _) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ _ _) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ _ _) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (const64_ok s₃ _ _) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps [.x4, .x5, .x6, .x7] s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans
      (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [k4.gpr .x4 (by decide), k3.gpr .x4 (by decide), k2.gpr .x4 (by decide), e1,
    k4.gpr .x5 (by decide), k3.gpr .x5 (by decide), e2, k4.gpr .x6 (by decide), e3, e4]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem constField_op {s : State} {base : Addr} (hs : Scr s base) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v := by
  rw [constField, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (slot_range o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (slot_range o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [F, fe_st4 _ _ (by have := (slot_range o).2; omega), hv, toFe_self]

theorem loadsField_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (loads (offset a) .x4 .x5 .x6 .x7)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base (offset a) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  refine WP.mono (loads_ok hs (slot_range a) (by decide)) fun t ⟨e1, e2, e3, e4, k⟩ => ?_
  exact ⟨by rw [e1, e2, e3, e4], k⟩

theorem copyField_op {s : State} {base : Addr} (hs : Scr s base) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = F s.mem base (offset a) := by
  rw [copyField, WP.block_append_iff]
  refine WP.mono (loadsField_ok hs a) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (slot_range o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (slot_range o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [F, fe_st4 _ _ (by have := (slot_range o).2; omega), hv]

theorem Outside_F {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 32 < 2 ^ 64)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : F m' base d = F m base d :=
  congrArg toFe (h.fe hsep hd)

end VG.Proof.Ed25519.AArch64
