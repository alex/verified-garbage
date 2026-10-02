import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! The three blocks of a four-word squaring (`sqrCross`,
`sqrDouble`, `sqrDiag`), each run once on its registers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- The products `aᵢ aⱼ` (`i < j`) of four words, at word `i + j - 1`. -/
abbrev cross (a0 a1 a2 a3 : Nat) : Nat :=
  a0 * a1 + 2 ^ 64 * (a0 * a2) + 2 ^ 128 * (a0 * a3 + a1 * a2) + 2 ^ 192 * (a1 * a3) +
    2 ^ 256 * (a2 * a3)

/-- The squares `aᵢ²` of four words, at word `2 i`. -/
abbrev diag (a0 a1 a2 a3 : Nat) : Nat :=
  a0 * a0 + 2 ^ 128 * (a1 * a1) + 2 ^ 256 * (a2 * a2 + 2 ^ 128 * (a3 * a3))

/-- The carry chains of `sqrCross`, on natural numbers. -/
theorem sqrCross_arith {L01 L02 L03 L12 L13 L23 H01 H02 H03 H12 H13 H23
    P01 P02 P03 P12 P13 P23 S6 S7 S21 S7b S21b S22 S21c S22b S22c S23
    K7 K8 K9 K14 K15 K16 K17 K18 K21 K22 : Nat}
    (e7 : S6 + 2 ^ 64 * K7 = L02 + H01 + 0) (e8 : S7 + 2 ^ 64 * K8 = L03 + H02 + K7)
    (e9 : S21 + 2 ^ 64 * K9 = H03 + 0 + K8)
    (e14 : S7b + 2 ^ 64 * K14 = S7 + L12 + 0) (e15 : S21b + 2 ^ 64 * K15 = S21 + L13 + K14)
    (e16 : S22 + 2 ^ 64 * K16 = H13 + 0 + K15)
    (e17 : S21c + 2 ^ 64 * K17 = S21b + H12 + 0) (e18 : S22b + 2 ^ 64 * K18 = S22 + 0 + K17)
    (e21 : S22c + 2 ^ 64 * K21 = S22b + L23 + 0) (e22 : S23 + 2 ^ 64 * K22 = H23 + 0 + K21)
    (m01 : L01 + 2 ^ 64 * H01 = P01) (m02 : L02 + 2 ^ 64 * H02 = P02)
    (m03 : L03 + 2 ^ 64 * H03 = P03) (m12 : L12 + 2 ^ 64 * H12 = P12)
    (m13 : L13 + 2 ^ 64 * H13 = P13) (m23 : L23 + 2 ^ 64 * H23 = P23)
    (p01 : P01 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p02 : P02 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p03 : P03 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p12 : P12 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p13 : P13 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p23 : P23 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L01 + 2 ^ 64 * S6 + 2 ^ 128 * S7b + 2 ^ 192 * S21c + 2 ^ 256 * (S22c + 2 ^ 64 * S23) =
      P01 + 2 ^ 64 * P02 + 2 ^ 128 * (P03 + P12) + 2 ^ 192 * P13 + 2 ^ 256 * P23 := by
  omega

/-- What `sqrCross` computes, word by word. -/
theorem sqrCross_value (a0 a1 a2 a3 : Word) :
    let k7 := carryOut (a0 * a2) (mulHi a0 a1) false
    let s7 := addCarry (a0 * a3) (mulHi a0 a2) k7
    let k8 := carryOut (a0 * a3) (mulHi a0 a2) k7
    let s21 := addCarry (mulHi a0 a3) 0 k8
    let k14 := carryOut s7 (a1 * a2) false
    let s21b := addCarry s21 (a1 * a3) k14
    let k15 := carryOut s21 (a1 * a3) k14
    let s22 := addCarry (mulHi a1 a3) 0 k15
    let k17 := carryOut s21b (mulHi a1 a2) false
    let s22b := addCarry s22 0 k17
    let k21 := carryOut s22b (a2 * a3) false
    val4 (a0 * a1) (addCarry (a0 * a2) (mulHi a0 a1) false) (addCarry s7 (a1 * a2) false)
        (addCarry s21b (mulHi a1 a2) false) +
        2 ^ 256 * ((addCarry s22b (a2 * a3) false).toNat +
          2 ^ 64 * (addCarry (mulHi a2 a3) 0 k21).toNat) =
      cross a0.toNat a1.toNat a2.toNat a3.toNat := by
  intro k7 s7 k8 s21 k14 s21b k15 s22 k17 s22b k21
  simp only [val4, cross]
  exact sqrCross_arith (addCarry_value (a0 * a2) (mulHi a0 a1) false)
    (addCarry_value (a0 * a3) (mulHi a0 a2) k7) (addCarry_value (mulHi a0 a3) 0 k8)
    (addCarry_value s7 (a1 * a2) false) (addCarry_value s21 (a1 * a3) k14)
    (addCarry_value (mulHi a1 a3) 0 k15)
    (addCarry_value s21b (mulHi a1 a2) false) (addCarry_value s22 0 k17)
    (addCarry_value s22b (a2 * a3) false) (addCarry_value (mulHi a2 a3) 0 k21)
    (mul_lo_hi a0 a1) (mul_lo_hi a0 a2) (mul_lo_hi a0 a3) (mul_lo_hi a1 a2)
    (mul_lo_hi a1 a3) (mul_lo_hi a2 a3)
    (mul_le a0 a1) (mul_le a0 a2) (mul_le a0 a3) (mul_le a1 a2) (mul_le a1 a3) (mul_le a2 a3)

theorem sqrCross_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block sqrCross) s fun t =>
      val4 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) +
          2 ^ 256 * ((t.gpr .x22).toNat + 2 ^ 64 * (t.gpr .x23).toNat) =
        cross (s.gpr .x12).toNat (s.gpr .x13).toNat (s.gpr .x14).toNat (s.gpr .x15).toNat ∧
      Keeps [.x2, .x8, .x9, .x16, .x5, .x6, .x7, .x21, .x22, .x23] s t := by
  apply WP.of_runBlock
  simp only [sqrCross, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := sqrCross_value (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- The carry chain of `sqrDouble`, on natural numbers. -/
theorem sqrDouble_arith {W1 W2 W3 W4 W5 W6 R1 R2 R3 R4 R5 R6 R7 K1 K2 K3 K4 K5 K6 K7 : Nat}
    (w1 : W1 < 2 ^ 64) (w2 : W2 < 2 ^ 64) (w3 : W3 < 2 ^ 64) (w4 : W4 < 2 ^ 64)
    (w5 : W5 < 2 ^ 64) (w6 : W6 < 2 ^ 64)
    (e1 : R1 + 2 ^ 64 * K1 = W1 + W1 + 0) (e2 : R2 + 2 ^ 64 * K2 = W2 + W2 + K1)
    (e3 : R3 + 2 ^ 64 * K3 = W3 + W3 + K2) (e4 : R4 + 2 ^ 64 * K4 = W4 + W4 + K3)
    (e5 : R5 + 2 ^ 64 * K5 = W5 + W5 + K4) (e6 : R6 + 2 ^ 64 * K6 = W6 + W6 + K5)
    (e7 : R7 + 2 ^ 64 * K7 = 0 + 0 + K6) :
    R1 + 2 ^ 64 * R2 + 2 ^ 128 * R3 + 2 ^ 192 * R4 + 2 ^ 256 * (R5 + 2 ^ 64 * R6 + 2 ^ 128 * R7) =
      2 * (W1 + 2 ^ 64 * W2 + 2 ^ 128 * W3 + 2 ^ 192 * W4 + 2 ^ 256 * (W5 + 2 ^ 64 * W6)) := by
  omega

/-- What `sqrDouble` computes, word by word. -/
theorem sqrDouble_value (w1 w2 w3 w4 w5 w6 : Word) :
    let k1 := carryOut w1 w1 false
    let k2 := carryOut w2 w2 k1
    let k3 := carryOut w3 w3 k2
    let k4 := carryOut w4 w4 k3
    let k5 := carryOut w5 w5 k4
    let k6 := carryOut w6 w6 k5
    val4 (addCarry w1 w1 false) (addCarry w2 w2 k1) (addCarry w3 w3 k2) (addCarry w4 w4 k3) +
        2 ^ 256 * ((addCarry w5 w5 k4).toNat + 2 ^ 64 * (addCarry w6 w6 k5).toNat +
          2 ^ 128 * (addCarry 0 0 k6).toNat) =
      2 * (val4 w1 w2 w3 w4 + 2 ^ 256 * (w5.toNat + 2 ^ 64 * w6.toNat)) := by
  intro k1 k2 k3 k4 k5 k6
  simp only [val4]
  exact sqrDouble_arith w1.isLt w2.isLt w3.isLt w4.isLt w5.isLt w6.isLt
    (addCarry_value w1 w1 false) (addCarry_value w2 w2 k1)
    (addCarry_value w3 w3 k2) (addCarry_value w4 w4 k3) (addCarry_value w5 w5 k4)
    (addCarry_value w6 w6 k5) (addCarry_value 0 0 k6)

theorem sqrDouble_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block sqrDouble) s fun t =>
      val4 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) +
          2 ^ 256 * ((t.gpr .x22).toNat + 2 ^ 64 * (t.gpr .x23).toNat +
            2 ^ 128 * (t.gpr .x24).toNat) =
        2 * (val4 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) +
          2 ^ 256 * ((s.gpr .x22).toNat + 2 ^ 64 * (s.gpr .x23).toNat)) ∧
      Keeps [.x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [sqrDouble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := sqrDouble_value (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22)
      (s.gpr .x23)
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- The carry chain of `sqrDiag`, on natural numbers. -/
theorem sqrDiag_arith {W1 W2 W3 W4 W5 W6 W7 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    R1 R2 R3 R4 R5 R6 R7 K1 K2 K3 K4 K5 K6 K7 : Nat}
    (e1 : R1 + 2 ^ 64 * K1 = W1 + H0 + 0) (e2 : R2 + 2 ^ 64 * K2 = W2 + L1 + K1)
    (e3 : R3 + 2 ^ 64 * K3 = W3 + H1 + K2) (e4 : R4 + 2 ^ 64 * K4 = W4 + L2 + K3)
    (e5 : R5 + 2 ^ 64 * K5 = W5 + H2 + K4) (e6 : R6 + 2 ^ 64 * K6 = W6 + L3 + K5)
    (e7 : R7 + 2 ^ 64 * K7 = W7 + H3 + K6)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 +
        2 ^ 256 * (R4 + 2 ^ 64 * R5 + 2 ^ 128 * R6 + 2 ^ 192 * R7 + 2 ^ 256 * K7) =
      2 ^ 64 * (W1 + 2 ^ 64 * W2 + 2 ^ 128 * W3 + 2 ^ 192 * W4 +
        2 ^ 256 * (W5 + 2 ^ 64 * W6 + 2 ^ 128 * W7)) +
        (P0 + 2 ^ 128 * P1 + 2 ^ 256 * (P2 + 2 ^ 128 * P3)) := by
  omega

/-- What `sqrDiag` computes, word by word. -/
theorem sqrDiag_value (a0 a1 a2 a3 w1 w2 w3 w4 w5 w6 w7 : Word) :
    let k1 := carryOut w1 (mulHi a0 a0) false
    let k2 := carryOut w2 (a1 * a1) k1
    let k3 := carryOut w3 (mulHi a1 a1) k2
    let k4 := carryOut w4 (a2 * a2) k3
    let k5 := carryOut w5 (mulHi a2 a2) k4
    let k6 := carryOut w6 (a3 * a3) k5
    val4 (a0 * a0) (addCarry w1 (mulHi a0 a0) false) (addCarry w2 (a1 * a1) k1)
        (addCarry w3 (mulHi a1 a1) k2) +
        2 ^ 256 * val4 (addCarry w4 (a2 * a2) k3) (addCarry w5 (mulHi a2 a2) k4)
          (addCarry w6 (a3 * a3) k5) (addCarry w7 (mulHi a3 a3) k6) +
        2 ^ 256 * (2 ^ 256 * (carryOut w7 (mulHi a3 a3) k6).toNat) =
      2 ^ 64 * (val4 w1 w2 w3 w4 + 2 ^ 256 * (w5.toNat + 2 ^ 64 * w6.toNat +
        2 ^ 128 * w7.toNat)) + diag a0.toNat a1.toNat a2.toNat a3.toNat := by
  intro k1 k2 k3 k4 k5 k6
  simp only [val4, diag]
  have h := sqrDiag_arith (addCarry_value w1 (mulHi a0 a0) false)
    (addCarry_value w2 (a1 * a1) k1) (addCarry_value w3 (mulHi a1 a1) k2)
    (addCarry_value w4 (a2 * a2) k3) (addCarry_value w5 (mulHi a2 a2) k4)
    (addCarry_value w6 (a3 * a3) k5) (addCarry_value w7 (mulHi a3 a3) k6)
    (mul_lo_hi a0 a0) (mul_lo_hi a1 a1) (mul_lo_hi a2 a2) (mul_lo_hi a3 a3)
  omega_using [h]

theorem sqrDiag_ok (s : State) :
    WP isa (.block sqrDiag) s fun t => ∃ c : Nat,
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) +
          2 ^ 256 * val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) +
          2 ^ 256 * (2 ^ 256 * c) =
        2 ^ 64 * (val4 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) +
          2 ^ 256 * ((s.gpr .x22).toNat + 2 ^ 64 * (s.gpr .x23).toNat +
            2 ^ 128 * (s.gpr .x24).toNat)) +
          diag (s.gpr .x12).toNat (s.gpr .x13).toNat (s.gpr .x14).toNat (s.gpr .x15).toNat ∧
      Keeps [.x2, .x3, .x8, .x9, .x11, .x16, .x17, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24]
        s t := by
  apply WP.of_runBlock
  simp only [sqrDiag, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have h := sqrDiag_value (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x5)
    (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
  dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
  refine ⟨_, h, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  reg_keeps

end VG.Proof.Ed25519.AArch64
