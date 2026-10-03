import VerifiedGarbage.Proof.Md5.X86_64.Shared
import VerifiedGarbage.Proof.Md5.AArch64.Shared
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.TCB.Axioms

/-! `Verified.stackScratch` on a real function: MD5's `update` (its streaming
code and its proofs as they are) without its scratch argument, on x86-64 and
AArch64. The scratch-less signature and contract are local to this test. -/

namespace VG.Test.StackScratch

/-- `vg_md5_update` without `scratch`. -/
def updateSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := fun state count data len m m' _ =>
    ∀ msg, Spec.Md5.Repr m state msg → count = BitVec.ofNat 64 msg.length →
      Spec.Md5.Repr m' state (msg ++ Spec.Md5.bytesAt m data len.toNat))
    (writeArgs := true)
    (stack := stack)

-- The contract with the scratch argument is `Sig.scratchContract` of the one
-- without it.
example : Spec.Md5.updateContract X86_64.abi 8 =
    Sig.scratchContract X86_64.abi updateSig "scratch" .u64 14 (Curry.const (fun _ => True) _)
      (fun state count data len m m' _ =>
        ∀ msg, Spec.Md5.Repr m state msg → count = BitVec.ofNat 64 msg.length →
          Spec.Md5.Repr m' state (msg ++ Spec.Md5.bytesAt m data len.toNat)) true 8 := rfl

theorem update_x86_64 : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 128 .r8 Impl.Md5.X86_64.Stream.update)
    (updateContract X86_64.abi (8 + 128)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 8) (bytes := 128)
    Proof.Md5.X86_64.Shared.update (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem update_aarch64 : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Md5.AArch64.Stream.update)
    (updateContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    Proof.Md5.AArch64.Shared.update (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

#guard (Impl.StackScratch.X86_64.withStackScratch 128 .r8 Impl.Md5.X86_64.Stream.update).all
  (fun i => !X86_64.isa.writesSp i)

#assert_standard_axioms update_x86_64
#assert_standard_axioms update_aarch64

end VG.Test.StackScratch
