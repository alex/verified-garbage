import VerifiedGarbage.Proof.Rc2.X86_64.Stream.InitCT

/-! # Streaming RC2-CBC on x86-64: verified against the shared contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem init_verified : Verified target init (Spec.Rc2.cbcInitContract abi 8) :=
  Verified.of_correct init_correct init_constantTime init_implies

theorem encryptUpdate_verified :
    Verified target encryptUpdate (Spec.Rc2.cbcEncryptUpdateContract abi 16) :=
  Verified.of_correct (update_correct .encrypt) (update_constantTime .encrypt) (update_implies .encrypt)

theorem decryptUpdate_verified :
    Verified target decryptUpdate (Spec.Rc2.cbcDecryptUpdateContract abi 16) :=
  Verified.of_correct (update_correct .decrypt) (update_constantTime .decrypt) (update_implies .decrypt)

end VG.Proof.Rc2.X86_64.Stream
