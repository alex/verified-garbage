import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.Arm.CompressS

/-!
# BLAKE2s on ARMv7: instructions and rotations

Untrusted: everything here is checked by Lean. Weakest-precondition rules for
the instructions the compression function uses that `Proof/MdStream/Arm`
lacks, and the facts about rotations its rotated registers need.
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd)

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl (k _ (Upd.setReg _ _ _))

theorem op2_ror {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .ror n).eval s = some ((s.gpr r).rotateRight n) := by
  simp [Op2.eval, h]

end

/-! ## Rotations -/

theorem rotl_rotr (x : BitVec 32) {k : Nat} (hk : k < 32) : (x.rotateRight k).rotateLeft k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega | (congr 1; omega)

theorem rotr_rotl (x : BitVec 32) {k : Nat} (hk : k < 32) : (x.rotateLeft k).rotateRight k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega | (congr 1; omega)

theorem rotr_eq_rotl (x : BitVec 32) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x.rotateRight k = x.rotateLeft (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk',
    Nat.mod_eq_of_lt (show 32 - k < 32 by omega)]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega | (congr 1; omega)

theorem rotl_xor (x y : BitVec 32) (k : Nat) : (x ^^^ y).rotateLeft k = x.rotateLeft k ^^^ y.rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  split <;> simp_all

theorem rotl8_rotr1 (x : BitVec 32) : (x.rotateLeft 8).rotateRight 1 = x.rotateLeft 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, show 8 % 32 = 8 from rfl,
    show 1 % 32 = 1 from rfl, show 7 % 32 = 7 from rfl]
  by_cases h1 : i < 32 - 1
  · by_cases h2 : 1 + i < 8 <;> by_cases h3 : i < 7 <;>
      simp [h1, h2, h3, hi, show 1 + i < 32 by omega] <;> first | omega | (congr 1; omega)
  · by_cases h2 : i - (32 - 1) < 8 <;> by_cases h3 : i < 7 <;> simp [h1, h2, h3, hi] <;>
      first | omega | (congr 1; omega)

/-- `G`'s words for BLAKE2s, in the order the code computes them: with `b` and
`d` given rotated left by 7 and 8, the code's additions and exclusive ors
before their rotations. -/
theorem mix_s (va B' vc D' X Y : BitVec 32) :
    Proof.Blake2.mix Spec.Blake2.s va (B'.rotateRight 7) vc (D'.rotateRight 8) X Y =
      let a1 := va + B'.rotateRight 7 + X
      let e1 := a1 ^^^ D'.rotateRight 8
      let c1 := vc + e1.rotateRight 16
      let f1 := c1 ^^^ B'.rotateRight 7
      let a2 := a1 + Y + f1.rotateRight 12
      let e2 := a2 ^^^ e1.rotateRight 16
      let c2 := c1 + e2.rotateRight 8
      let f2 := c2 ^^^ f1.rotateRight 12
      (a2, f2.rotateRight 7, c2, e2.rotateRight 8) := by
  simp only [Proof.Blake2.mix, show Spec.Blake2.s.R1 = 16 from rfl, show Spec.Blake2.s.R2 = 12 from rfl,
    show Spec.Blake2.s.R3 = 8 from rfl, show Spec.Blake2.s.R4 = 7 from rfl]
  simp only [BitVec.xor_comm (D'.rotateRight 8), BitVec.xor_comm (B'.rotateRight 7), BitVec.add_assoc,
    BitVec.add_comm Y]
  simp only [BitVec.xor_comm _ (_ + _)]

end VG.Proof.Blake2.ArmS
