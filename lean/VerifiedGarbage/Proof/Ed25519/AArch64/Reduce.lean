import VerifiedGarbage.Proof.Ed25519.AArch64.Ops

/-! Untrusted: reduction of an eight-word field product. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- `reduce`, with its steps spelled out. -/
theorem reduce_eq : reduce =
    ([.movz .w .x3 38 0, .movz .w .x20 0 0] : List Instr) ++ (mulStep .x4 .x20 .x3 .x21 ++
      (mulStep .x5 .x20 .x3 .x22 ++ (mulStep .x6 .x20 .x3 .x23 ++
        (mulStep .x7 .x20 .x3 .x24 ++ fold)))) := by
  simp only [reduce, List.append_assoc]
  rfl

/-- `lo + 38 hi` of the eight words `x4–x7, x21–x24`: into `x4–x7` and the carry word
`x20`. -/
theorem reduceSteps_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (([.movz .w .x3 38 0, .movz .w .x20 0 0] : List Instr) ++ (mulStep .x4 .x20 .x3 .x21 ++
      (mulStep .x5 .x20 .x3 .x22 ++ (mulStep .x6 .x20 .x3 .x23 ++
        mulStep .x7 .x20 .x3 .x24))))) s fun s' =>
      val4 (s'.gpr .x4) (s'.gpr .x5) (s'.gpr .x6) (s'.gpr .x7) + 2 ^ 256 * (s'.gpr .x20).toNat =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
          38 * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24) ∧
      s'.gpr .x3 = 38 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x2, .x3, .x20] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movz .w .x3 38 0, .movz .w .x20 0 0]) s
      (fun s' => s'.gpr .x3 = 38 ∧ s'.gpr .x20 = 0 ∧ Keeps [.x3, .x20] s s') by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self]
      rfl
    · rw [RegUpd.gpr_write_self]
      rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]) fun s₁ ⟨c1, b1, k1⟩ => ?_
  rw [WP.block_append_iff]
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  refine WP.mono (mulStep_ok s₁ hz1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  have hz2 := (k2.gpr .x10 (by decide)).trans hz1
  refine WP.mono (mulStep_ok s₂ hz2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  have hz3 := (k3.gpr .x10 (by decide)).trans hz2
  refine WP.mono (mulStep_ok s₃ hz3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hz4 := (k4.gpr .x10 (by decide)).trans hz3
  refine WP.mono (mulStep_ok s₄ hz4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s₅ ⟨e5, k5⟩ => ?_
  have K : Keeps [.x4, .x5, .x6, .x7, .x8, .x2, .x3, .x20] s s₅ :=
    (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide)) |>.trans (k5.mono (by decide))
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.gpr r h
  refine ⟨?_, ?_, K⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [c1, g k1 .x21 (by decide), b1, g k1 .x4 (by decide)] at e2
    rw [g k2 .x3 (by decide), c1, g k2 .x22 (by decide), g k1 .x22 (by decide),
      g k2 .x5 (by decide), g k1 .x5 (by decide)] at e3
    rw [g k3 .x3 (by decide), g k2 .x3 (by decide), c1, g k3 .x23 (by decide),
      g k2 .x23 (by decide), g k1 .x23 (by decide), g k3 .x6 (by decide), g k2 .x6 (by decide),
      g k1 .x6 (by decide)] at e4
    rw [g k4 .x3 (by decide), g k3 .x3 (by decide), g k2 .x3 (by decide), c1,
      g k4 .x24 (by decide), g k3 .x24 (by decide), g k2 .x24 (by decide), g k1 .x24 (by decide),
      g k4 .x7 (by decide), g k3 .x7 (by decide), g k2 .x7 (by decide),
      g k1 .x7 (by decide)] at e5
    simp only [val4, g k5 .x4 (by decide), g k4 .x4 (by decide), g k3 .x4 (by decide),
      g k5 .x5 (by decide), g k4 .x5 (by decide), g k5 .x6 (by decide)]
    have h38 : (38 : BitVec 64).toNat = 38 := rfl
    rw [h38] at e2 e3 e4 e5
    rw [z] at e2
    omega_using [e2, e3, e4, e5]
  · rw [g k5 .x3 (by decide), g k4 .x3 (by decide), g k3 .x3 (by decide), g k2 .x3 (by decide), c1]

theorem fold_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hb : (s.gpr .x20).toNat < 2 ^ 52) :
    WP isa (.block fold) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 38 * (s.gpr .x20).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mul .x .x8 .x20 .x11]) s fun t =>
      (t.gpr .x8).toNat = 38 * (s.gpr .x20).toNat ∧ Keeps [.x8] s t from by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', h38]
    refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [BitVec.toNat_mul, show (38 : Word).toNat = 38 from rfl, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    · intro r hr
      exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr))
    fun s₁ ⟨e1, k1⟩ => ?_
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  have h381 := (k1.gpr .x11 (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by rw [e1]; omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans k2⟩
  rw [e2, e1, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide)]

end VG.Proof.Ed25519.AArch64
