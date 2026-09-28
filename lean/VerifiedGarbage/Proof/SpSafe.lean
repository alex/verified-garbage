import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.ChaCha20.X86
import VerifiedGarbage.Impl.ChaCha20.X86_64
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Impl.Hmac.X86_64
import VerifiedGarbage.Impl.Pbkdf2.X86_64
import VerifiedGarbage.Impl.Md5.X86_64
import VerifiedGarbage.Impl.Md5.X86_64.Stream
import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Impl.Sha3.X86_64
import VerifiedGarbage.Impl.Sha3.X86_64.Stream
import VerifiedGarbage.Impl.Sha1.X86_64
import VerifiedGarbage.Impl.Sha1.X86_64.Stream
import VerifiedGarbage.Impl.Sha256.X86
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Impl.Sha256.X86_64
import VerifiedGarbage.Impl.Sha256.X86_64.Stream
import VerifiedGarbage.Impl.Sha256.X86_64.ShaNi
import VerifiedGarbage.Impl.Sha512.X86_64
import VerifiedGarbage.Impl.Sha512.X86_64.Stream
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor

/-!
# The stack discipline of the x86 and x86-64 artifacts

Untrusted: everything here is checked by Lean.

`Artifact.spSafe`: no instruction of an artifact's code, or of the code it
calls, writes the stack pointer. On x86 and x86-64 the kernel checks it by
evaluating the code, which takes a fraction of a second per artifact; these
theorems do that here, in a module that depends only on the code and builds
in parallel with the proofs, rather than in `Artifacts.lean`, which every
proof has to finish before. (On ARMv7 and AArch64 no instruction writes the
stack pointer: `Code.all_of_forall`.)
-/

namespace VG.Proof.SpSafe

theorem selftest_x86_64_add :
    Impl.Selftest.X86_64.add.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_compress :
    Impl.Sha256.X86_64.compress.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_init :
    Impl.Sha256.X86_64.Stream.init.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_update :
    (Impl.Sha256.X86_64.Stream.update .scalar).all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_finalize :
    (Impl.Sha256.X86_64.Stream.finalize .scalar).all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_compress_shani :
    Impl.Sha256.X86_64.ShaNi.compress.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_update_shani :
    (Impl.Sha256.X86_64.Stream.update .shani).all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_64_finalize_shani :
    (Impl.Sha256.X86_64.Stream.finalize .shani).all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem md5_x86_64_compress :
    Impl.Md5.X86_64.compress.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem md5_x86_64_init :
    Impl.Md5.X86_64.Stream.init.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem md5_x86_64_update :
    Impl.Md5.X86_64.Stream.update.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem md5_x86_64_finalize :
    Impl.Md5.X86_64.Stream.finalize.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha3_x86_64_permute :
    Impl.Sha3.X86_64.permute.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha3_x86_64_absorb :
    Impl.Sha3.X86_64.Stream.absorb.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha3_x86_64_pad :
    Impl.Sha3.X86_64.Stream.pad.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha3_x86_64_squeeze :
    Impl.Sha3.X86_64.Stream.squeeze.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha1_x86_64_compress :
    Impl.Sha1.X86_64.compress.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha1_x86_64_init :
    Impl.Sha1.X86_64.Stream.init.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha1_x86_64_update :
    Impl.Sha1.X86_64.Stream.update.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha1_x86_64_finalize :
    Impl.Sha1.X86_64.Stream.finalize.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_compress :
    Impl.Sha512.X86_64.compress.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_init_h0_384 :
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384).all
      (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_init_h0_512 :
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all
      (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_init_h0_512_224 :
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224).all
      (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_init_h0_512_256 :
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256).all
      (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_update :
    Impl.Sha512.X86_64.Stream.update.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha512_x86_64_finalize :
    Impl.Sha512.X86_64.Stream.finalize.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem hmac_x86_64_init :
    Impl.Hmac.X86_64.init.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem hmac_x86_64_finalize :
    Impl.Hmac.X86_64.finalize.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem pbkdf2_x86_64_iterate :
    Impl.Pbkdf2.X86_64.iterate.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem chacha20_x86_64_block :
    Impl.ChaCha20.X86_64.block.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem scrypt_x86_64_salsa :
    Impl.Scrypt.X86_64.salsa.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem scrypt_x86_64_blockmix :
    Impl.Scrypt.X86_64.blockMix.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem scrypt_x86_64_romix :
    Impl.Scrypt.X86_64.roMix.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_compress :
    Impl.Sha256.X86.compress.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_init :
    Impl.Sha256.X86.Stream.init.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_update :
    Impl.Sha256.X86.Stream.update.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem sha256_x86_finalize :
    Impl.Sha256.X86.Stream.finalize.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem hmac_x86_init :
    Impl.Hmac.X86.init.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem hmac_x86_finalize :
    Impl.Hmac.X86.finalize.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem chacha20_x86_block :
    Impl.ChaCha20.X86.block.all (fun i => !X86.target.isa.writesSp i) = true := by
  decide +kernel

theorem chacha20_x86_64_xor :
    Impl.ChaCha20.X86_64.Xor.xor.all (fun i => !X86_64.target.isa.writesSp i) = true := by
  decide +kernel

end VG.Proof.SpSafe
