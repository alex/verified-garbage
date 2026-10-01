import VerifiedGarbage.Impl.Argon2.X86_64.Relative
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.X86_64.Mix
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # The baseline reference-window mapping is fixed time and preserves memory -/

namespace VG.Proof.Argon2.X86_64.Relative

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Relative

def value (random count : Addr) : Addr :=
  let j := random &&& 0xffffffff
  let x := (j * j) >>> 32
  let y := (x * count) >>> 32
  count - 1 - y

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rax = value (s.gpr .rdi) (s.gpr .rsi) ∧
    (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold code
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, readSrc, State.setReg32, execMul, execAlu, execShift,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, and_self, ite_true, ite_false,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl]
  refine ⟨?_, ?_, trivial⟩
  · rw [VG.Proof.Argon2.X86_64.low32]; rfl
  · intro r h1 h2 h3
    simp only [h1, h2, h3, ite_false]

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

theorem code_nat_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      t.gpr .rax = BitVec.ofNat 64
        ((s.gpr .rsi).toNat - 1 - (s.gpr .rsi).toNat *
          ((s.gpr .rdi &&& 0xffffffff).toNat * (s.gpr .rdi &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  (code_ok s).mono (fun _ h => ⟨h.1.trans (value_nat _ _ lo bound), h.2⟩)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Relative
