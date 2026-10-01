import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-! Untrusted: rows of a four-by-four word product with the words of one
operand in registers (`rowFirst`, `rowAcc`), and the instances the field
multiplication and reduction use. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- The high word of a product, as `umulh` computes it. -/
abbrev mulHi (a b : Word) : Word := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)

theorem mul_lo_hi (a b : Word) :
    (a * b).toNat + 2 ^ 64 * (mulHi a b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  have h1 : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have h2 : (mulHi a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
    simp only [mulHi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  omega

theorem mul_le (a b : Word) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)

theorem mul_val4 (a b0 b1 b2 b3 : Nat) :
    a * (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) =
      a * b0 + 2 ^ 64 * (a * b1) + 2 ^ 128 * (a * b2) + 2 ^ 192 * (a * b3) := by
  simp only [Nat.mul_add, Nat.mul_left_comm a]

/-- The carry chains of `rowAcc`, on natural numbers: the low halves `L`
of the products `P` added to `T`, then the high halves `H` one word up. -/
theorem rowAcc_arith {T0 T1 T2 T3 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    S0 S1 S2 S3 U R1 R2 R3 R4 C0 C1 C2 C3 C4 D1 D2 D3 D4 : Nat}
    (e0 : S0 + 2 ^ 64 * C0 = T0 + L0 + 0) (e1 : S1 + 2 ^ 64 * C1 = T1 + L1 + C0)
    (e2 : S2 + 2 ^ 64 * C2 = T2 + L2 + C1) (e3 : S3 + 2 ^ 64 * C3 = T3 + L3 + C2)
    (e4 : U + 2 ^ 64 * C4 = 0 + 0 + C3)
    (f1 : R1 + 2 ^ 64 * D1 = S1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = S2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = S3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = U + H3 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (t0 : T0 < 2 ^ 64) (t1 : T1 < 2 ^ 64) (t2 : T2 < 2 ^ 64) (t3 : T3 < 2 ^ 64) :
    S0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      T0 + 2 ^ 64 * T1 + 2 ^ 128 * T2 + 2 ^ 192 * T3 +
        (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) := by
  omega

/-- What `rowAcc` computes, word by word. -/
theorem rowAcc_value (a b0 b1 b2 b3 t0 t1 t2 t3 : Word) :
    let c0 := carryOut t0 (a * b0) false
    let c1 := carryOut t1 (a * b1) c0
    let c2 := carryOut t2 (a * b2) c1
    let c3 := carryOut t3 (a * b3) c2
    let s1 := addCarry t1 (a * b1) c0
    let s2 := addCarry t2 (a * b2) c1
    let s3 := addCarry t3 (a * b3) c2
    let u := addCarry 0 0 c3
    let d1 := carryOut s1 (mulHi a b0) false
    let d2 := carryOut s2 (mulHi a b1) d1
    let d3 := carryOut s3 (mulHi a b2) d2
    val4 (addCarry t0 (a * b0) false) (addCarry s1 (mulHi a b0) false)
        (addCarry s2 (mulHi a b1) d1) (addCarry s3 (mulHi a b2) d2) +
        2 ^ 256 * (addCarry u (mulHi a b3) d3).toNat =
      val4 t0 t1 t2 t3 + a.toNat * val4 b0 b1 b2 b3 := by
  intro c0 c1 c2 c3 s1 s2 s3 u d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact rowAcc_arith (addCarry_value t0 (a * b0) false) (addCarry_value t1 (a * b1) c0)
    (addCarry_value t2 (a * b2) c1) (addCarry_value t3 (a * b3) c2) (addCarry_value 0 0 c3)
    (addCarry_value s1 (mulHi a b0) false) (addCarry_value s2 (mulHi a b1) d1)
    (addCarry_value s3 (mulHi a b2) d2) (addCarry_value u (mulHi a b3) d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)
    (mul_le a b0) (mul_le a b1) (mul_le a b2) (mul_le a b3) t0.isLt t1.isLt t2.isLt t3.isLt

/-- The carry chain of `rowFirst`, on natural numbers. -/
theorem rowFirst_arith {L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3 R1 R2 R3 R4 D1 D2 D3 D4 : Nat}
    (f1 : R1 + 2 ^ 64 * D1 = L1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = L2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = L3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = H3 + 0 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3 := by
  omega

/-- What `rowFirst` computes, word by word. -/
theorem rowFirst_value (a b0 b1 b2 b3 : Word) :
    let d1 := carryOut (a * b1) (mulHi a b0) false
    let d2 := carryOut (a * b2) (mulHi a b1) d1
    let d3 := carryOut (a * b3) (mulHi a b2) d2
    val4 (a * b0) (addCarry (a * b1) (mulHi a b0) false)
        (addCarry (a * b2) (mulHi a b1) d1) (addCarry (a * b3) (mulHi a b2) d2) +
        2 ^ 256 * (addCarry (mulHi a b3) 0 d3).toNat =
      a.toNat * val4 b0 b1 b2 b3 := by
  intro d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact rowFirst_arith (addCarry_value (a * b1) (mulHi a b0) false)
    (addCarry_value (a * b2) (mulHi a b1) d1) (addCarry_value (a * b3) (mulHi a b2) d2)
    (addCarry_value (mulHi a b3) 0 d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)
    (mul_le a b0) (mul_le a b1) (mul_le a b2) (mul_le a b3)

/-- Run a straight block of register arithmetic, reading registers through
the writes (literal registers decide each `if`). -/
macro "reg_exec" hz:term : tactic => `(tactic| (
  apply WP.of_runBlock
  simp only [rowAcc, rowFirst, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, $hz:term,
    Option.some.injEq, exists_eq_left']))

/-- The registers but those written are kept. -/
macro "reg_keeps" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]))

theorem rowFirst_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowFirst .x3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * (t.gpr .x21).toNat =
        (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x4, .x5, .x6, .x7, .x21] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := rowFirst_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- Row 1 of the product, `a₁ · b`, into x5–x7, x21–x22. -/
theorem rowAcc1_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x3 .x12 .x13 .x14 .x15 .x5 .x6 .x7 .x21 .x22)) s fun t =>
      val4 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) + 2 ^ 256 * (t.gpr .x22).toNat =
        val4 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) +
          (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x5, .x6, .x7, .x21, .x22] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := rowAcc_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- Row 2 of the product, into x6–x7, x21–x23. -/
theorem rowAcc2_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x3 .x12 .x13 .x14 .x15 .x6 .x7 .x21 .x22 .x23)) s fun t =>
      val4 (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) (t.gpr .x22) + 2 ^ 256 * (t.gpr .x23).toNat =
        val4 (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) +
          (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x6, .x7, .x21, .x22, .x23] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := rowAcc_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- Row 3 of the product, into x7, x21–x24. -/
theorem rowAcc3_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x3 .x12 .x13 .x14 .x15 .x7 .x21 .x22 .x23 .x24)) s fun t =>
      val4 (t.gpr .x7) (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) + 2 ^ 256 * (t.gpr .x24).toNat =
        val4 (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) +
          (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x7, .x21, .x22, .x23, .x24] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := rowAcc_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- 38 times the high half of a product added to its low half: x4–x7 and x20. -/
theorem rowAccReduce_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x11 .x21 .x22 .x23 .x24 .x4 .x5 .x6 .x7 .x20)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * (t.gpr .x20).toNat =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
          (s.gpr .x11).toNat * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24) ∧
      Keeps [.x2, .x8, .x9, .x16, .x4, .x5, .x6, .x7, .x20] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := rowAcc_value (s.gpr .x11) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

end VG.Proof.Ed25519.AArch64
