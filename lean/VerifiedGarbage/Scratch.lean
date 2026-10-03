import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
import VerifiedGarbage.Proof.AesGcm.X86_64.Verified
open VG VG.X86_64
namespace VG.Proof.AesGcm.X86_64
def blkSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 0⟩, ⟨0, 2560⟩]
example (c : Prog isa) (h1 : ∀ s, Proof.AesGcm.encryptBlocksX86_64.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.encryptBlocksX86_64.post s s')
  (h2 : ConstantTime isa Proof.AesGcm.encryptBlocksX86_64.pre Proof.AesGcm.encryptBlocksX86_64.pub c) :
    Verified X86_64.target c (Spec.Gcm.encryptBlocksContract X86_64.abi 8) :=
  Verified.of_correct h1 h2 (by
    exact
      { pre := by sig_implies_pre [Spec.Gcm.encryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.encryptBlocksX86_64, Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        post := by sig_implies_post [Spec.Gcm.encryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.encryptBlocksX86_64, Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        pub := by sig_implies_pub [Spec.Gcm.encryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.encryptBlocksX86_64, Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sat := by sig_implies_sat [Spec.Gcm.encryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.encryptBlocksX86_64, Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [blkSat] using blkSat })
end VG.Proof.AesGcm.X86_64
