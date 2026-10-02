import VerifiedGarbage.Proof.Argon2.AArch64.Carry
import VerifiedGarbage.Impl.Argon2.AArch64.Relative
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.AArch64.Mix
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! # The baseline reference-window mapping is fixed time and preserves memory -/

namespace VG.Proof.Argon2.AArch64.Relative

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Relative
open VG.Impl.Argon2.AArch64

def value (random count : Addr) : Addr :=
  let j := random &&& 0xffffffff
  let x := (j * j) >>> 32
  let y := (x * count) >>> 32
  count - 1 - y

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x8 = value (s.gpr .x0) (s.gpr .x1) ∧
    (∀ r, r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold code
  apply WP.of_runBlock
  simp only [List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Instructions.mov, Instructions.mov32, Instructions.mul, Instructions.shr,
    Instructions.subi, Instructions.sub, Instructions.imm, Instructions.mark,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_addWithCarry, RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry,
    BitVec.setWidth_eq, BitVec.or_self, reduceCtorEq, ite_true, ite_false,
    show 0 < 4096 from by decide, show 1 < 65536 from by decide,
    Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (BitVec.ofNat 16 1).setWidth 64 = 1#64 from rfl,
    show 32 < 64 from by decide, BitVec.add_zero, Option.some.injEq,
    exists_eq_left', Bool.toNat_true, sub_value]
  refine ⟨?_, ?_, trivial, trivial, trivial⟩
  · rw [low32]; rfl
  · intro r h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, ite_false]

theorem mul_shift_toNat (x y : Addr) (bound : x.toNat * y.toNat < 2 ^ 64) :
    ((x * y) >>> 32).toNat = x.toNat * y.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
    Nat.mod_eq_of_lt bound]

theorem value_nat (random count : Addr) (lo : 0 < count.toNat)
    (bound : count.toNat < 2 ^ 32) :
    value random count = BitVec.ofNat 64
      (count.toNat - 1 - count.toNat * ((random &&& 0xffffffff).toNat *
        (random &&& 0xffffffff).toNat / 2 ^ 32) / 2 ^ 32) := by
  let j := random &&& 0xffffffff
  have hj : j.toNat < 2 ^ 32 := by
    have h32 := (random.setWidth 32).isLt
    rw [show j = (random.setWidth 32).setWidth 64 from (low32 random).symm,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact h32
  have hx := mul_shift_toNat j j (Proof.Argon2.reference_square_bound _ hj)
  have product : ((j * j) >>> 32).toNat * count.toNat < 2 ^ 64 := by
    rw [hx, Nat.mul_comm]
    exact Proof.Argon2.reference_product_bound _ _ bound hj
  have hy := mul_shift_toNat ((j * j) >>> 32) count product
  rw [hx, Nat.mul_comm] at hy
  have hyBound : count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32 < count.toNat :=
    Proof.Argon2.reference_scale_lt_count _ _ lo hj
  have hyWord : (((j * j) >>> 32) * count) >>> 32 = BitVec.ofNat 64
      (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold value
  change count - 1 - ((((j * j) >>> 32) * count) >>> 32) = _
  rw [hyWord]
  change count - (1 : Addr) - BitVec.ofNat 64
    (count.toNat * (j.toNat * j.toNat / 2 ^ 32) / 2 ^ 32) = _
  have countWord : count = BitVec.ofNat 64 count.toNat := by
    exact (BitVec.ofNat_toNat 64 count).symm
  have countSub : count - 1 = BitVec.ofNat 64 (count.toNat - 1) := by
    calc
      count - 1 = BitVec.ofNat 64 count.toNat - BitVec.ofNat 64 1 :=
        congrArg (fun x : Addr => x - 1) countWord
      _ = _ := Offset.ofNat_sub_ofNat (by omega)
  rw [countSub, Offset.ofNat_sub_ofNat (by omega)]

theorem code_nat_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      t.gpr .x8 = BitVec.ofNat 64
        ((s.gpr .x1).toNat - 1 - (s.gpr .x1).toNat *
          ((s.gpr .x0 &&& 0xffffffff).toNat * (s.gpr .x0 &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧
      (∀ r, r ≠ .x8 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (value_nat _ _ lo bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.Relative
