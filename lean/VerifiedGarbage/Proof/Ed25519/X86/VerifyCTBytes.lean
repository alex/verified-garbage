import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verify_sig_offset {s : State} (h : verifyLocal.pre s) :
    (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, sf, _, _, _⟩ := h
  exact addr_eq (by omega_using [sf])

theorem VerifyCTFacts.pkBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 0 + BitVec.ofNat 32 0).setWidth 64) 32 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 0 + BitVec.ofNat 32 0).setWidth 64) 32 := by
  simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using h.pub.2.2.2.2.2.1

theorem VerifyCTFacts.rBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 0).setWidth 64) 32 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 1 + BitVec.ofNat 32 0).setWidth 64) 32 := by
  have hh := congrArg (List.take 32) h.pub.2.2.2.2.2.2.1
  rw [signatureBytes_take, signatureBytes_take] at hh
  simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using hh

theorem VerifyCTFacts.scalarBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 1 + BitVec.ofNat 32 32).setWidth 64) 32 := by
  rw [verify_sig_offset h.left, verify_sig_offset h.right]
  have hh := congrArg (List.drop 32) h.pub.2.2.2.2.2.2.1
  rw [signatureBytes_drop, signatureBytes_drop] at hh
  exact hh

theorem VerifyCTFacts.challengeBytes {s t : State} (h : VerifyCTFacts s t) :
    VG.Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64 =
      VG.Spec.Ed25519.bytesAt t.mem ((arg t 2 + BitVec.ofNat 32 0).setWidth 64) 64 := by
  simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using h.pub.2.2.2.2.2.2.2

theorem fe_decode_input {s : State} {p : BitVec 32} (h : p.toNat + 32 ≤ 2 ^ 32) :
    fe s.mem p 0 = VG.Spec.Ed25519.decodeLE (VG.Spec.Ed25519.bytesAt s.mem (p.setWidth 64) 32) := by
  have hh := decode_words (x := p) (o := 0) s.mem 8 (by omega_using [h])
  rw [addr_zero] at hh
  exact hh.symm

theorem VerifyCTFacts.scalarFe {s t : State} (h : VerifyCTFacts s t) :
    fe s.mem (arg s 1 + 32) 0 = fe t.mem (arg t 1 + 32) 0 := by
  change fe s.mem (arg s 1 + BitVec.ofNat 32 32) 0 = fe t.mem (arg t 1 + BitVec.ofNat 32 32) 0
  rw [fe_decode_input (s := s) (verify_pre h.left).scalar.fit, fe_decode_input (s := t) (verify_pre h.right).scalar.fit]
  exact congrArg VG.Spec.Ed25519.decodeLE h.scalarBytes

end VG.Proof.Ed25519.X86
