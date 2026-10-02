import VerifiedGarbage.Proof.Rc2.Arm.Stream.InitCT

/-! # Verified streaming RC2-CBC on ARMv7 -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

theorem init_verified : Verified target Impl.Rc2.Arm.Stream.init (Spec.Rc2.cbcInitContract abi 8) :=
  Verified.of_correct init_correct init_constantTime init_implies

theorem encryptUpdate_verified :
    Verified target Impl.Rc2.Arm.Stream.encryptUpdate (Spec.Rc2.cbcEncryptUpdateContract abi 8) :=
  Verified.of_correct (update_correct .encrypt) (update_constantTime .encrypt) (update_implies .encrypt)

theorem decryptUpdate_verified :
    Verified target Impl.Rc2.Arm.Stream.decryptUpdate (Spec.Rc2.cbcDecryptUpdateContract abi 8) :=
  Verified.of_correct (update_correct .decrypt) (update_constantTime .decrypt) (update_implies .decrypt)

end VG.Proof.Rc2.Arm.Stream
