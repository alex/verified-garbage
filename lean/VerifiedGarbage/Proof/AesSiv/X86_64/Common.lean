import VerifiedGarbage.Proof.AesSiv.X86_64.Call
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Cmac.Block

/-!
# AES-SIV on x86-64: common lemmas

Running a block that is two blocks concatenated (`runBlock_append`), and the
registers the code keeps.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => simp [runBlock]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- The immediates the code adds, sign-extended. -/
theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]

theorem take_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).take a = Spec.Aes.bytesAt m p a := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem drop_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesSiv.X86_64
