import VerifiedGarbage.Proof.Curve448.AArch64.Stage
import VerifiedGarbage.Proof.Curve448.AArch64.Copy
import VerifiedGarbage.Proof.X448.Wide.Pack
import VerifiedGarbage.Proof.X448.Wide.TailNormalize
import VerifiedGarbage.Proof.X448.Wide.Encoded
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ld st TMP ACC)
open VG.Impl.X448.AArch64.Wide (PACKA)
open VG.Proof.X448.AArch64

theorem fromLegacy_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (hb : VG.Proof.X448.AArch64.Bounded s.mem base o) :
    WP isa (.block (Impl.Curve448.AArch64.fromLegacy o)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = VG.Proof.X448.AArch64.F s.mem base o := by
  rw [Impl.Curve448.AArch64.fromLegacy, WP.block_append_iff]
  refine WP.mono (pack_ok hs (o := PACKA) (by decide) (Nat.le_trans ho (by decide))
    (by decide) ho8 (Or.inl (Nat.le_trans ho (by decide))) hb) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (copy_ok (o := o) (a := PACKA) (hs.of_keeps uk (by decide)) (Nat.le_trans ho (by decide))
    (by decide) ho8 (by decide) (Or.inr (Or.inl (Nat.le_trans ho (by decide))))) fun t ⟨tf, tm, tk⟩ => ?_
  have out : ∀ i < 8, limbs t.mem base o i = paired (limbs s.mem base o) i :=
    fun i hi => (tf i hi).trans (uf i hi)
  refine ⟨⟨(uk.mono (by decide)).trans tk,
    (FieldMem.work um (by decide) (by decide)).trans (.output tm)⟩, ?_, ?_⟩
  · intro i hi; rw [out i hi]
    exact Nat.lt_trans (paired_bound hb i hi) (by simp only [weakBound]; omega)
  · apply congrArg VG.Proof.X448.toFe
    rw [show fe t.mem base o = VG.Proof.X448.Wide.valN (paired (limbs s.mem base o)) 8 from
      VG.Proof.X448.Wide.valN_congr out, paired_val]

theorem legacyEval_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (hi : i < 8) :
    WP isa (.block (Impl.Curve448.AArch64.legacyEval o i)) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = limbs s.mem base o i ∧ t.mem = s.mem ∧ Keeps clob s t := by
  have l := hs.read (d := o + 8 * i) (n := 8) (by change o + 128 ≤ 3584 at ho; omega)
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := by change o + 128 ≤ 3584 at ho; omega
  apply WP.of_runBlock
  simp only [Impl.Curve448.AArch64.legacyEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.load, RegUpd.gpr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    oe, and_self, hs.x3, l, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [pair, show (BitVec.setWidth 64 (0 : BitVec 16)).toNat = 0 from rfl,
      Nat.mul_zero, Nat.add_zero]
  · simp only [RegUpd.gpr_write, show r ≠ .x4 from fun h => hr (by subst r; decide),
      show r ≠ .x5 from fun h => hr (by subst r; decide), ite_false]

theorem toLegacy_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (hb : Bounded s.mem base o) :
    WP isa (.block (Impl.Curve448.AArch64.toLegacy o)) s fun t =>
      Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧
      VG.Proof.X448.AArch64.F t.mem base o = F s.mem base o := by
  rw [Impl.Curve448.AArch64.toLegacy, WP.block_append_iff]
  refine WP.mono (stage_ok hs (code := Impl.Curve448.AArch64.legacyEval o)
    (f := limbs s.mem base o) ?_) fun u ⟨uf, um, uk⟩ => ?_
  · intro i hi t ts tm
    refine WP.mono (legacyEval_ok ts ho ho8 hi) fun v ⟨vf, vm, vk⟩ => ⟨?_, vm, vk⟩
    rw [input_limb tm ho hi] at vf; exact vf
  · have cap : ∀ i < 8, limbs s.mem base o i < 2 ^ 118 :=
      fun i hi => Nat.lt_trans (hb i hi) (by decide)
    refine WP.mono (tailNormalize_ok (hs.of_keeps uk (by decide)) ho ho8 uf cap) fun t ⟨tf, tm, tk⟩ => ?_
    have out := encoded_limbs tf
    refine ⟨⟨uk.trans (tk.mono (by decide)), (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
    · intro i hi; rw [out i hi]
      exact unpacked_bound (fun j _ => digit_lt _ j) i hi
    · apply VG.Proof.X448.toFe_congr
      rw [show VG.Proof.X448.AArch64.fe t.mem base o = VG.Proof.X448.valN
        (unpacked (normalized (limbs s.mem base o))) 16 from VG.Proof.X448.valN_congr out,
        unpacked_val, normalized_mod cap]
end VG.Proof.Curve448.AArch64
