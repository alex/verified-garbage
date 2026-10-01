import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-! The complete verifier satisfies the reviewed message-level contract. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce verifyEquation callWith)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Sha512.X86_64 (Compress)

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0 | .rcx => 0x3000
    | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem implies : verifyMessageLocal.Implies (Spec.Ed25519.verifyContract X86_64.abi 184) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, verifyMessageLocal]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs]
    change t.gpr .rax = if _ then 1 else 0 at h
    rw [h]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, scr⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb
      (by simp only [PublicKey.bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [PublicKey.bytesAt_length, len])
    exact ⟨sp, pk, msg, len, sig, scr, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs] [satState] using satState

theorem verified (v : Compress) :
    Verified X86_64.target (code fld fs v.callee v.suffix) (Spec.Ed25519.verifyContract X86_64.abi 184) :=
  Verified.of_correct (fun _ h => verifyMessage_ok v h) (verifyMessage_ct v) implies

theorem spSafe (v : Compress) :
    (code fld fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hr : scalarReduce.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have he : (verifyEquation fld).all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by fld_lit_decide)
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [code, body, Impl.Ed25519.X86_64.VerifyMessage.hash, callWith, Code.all, hu, hf, hr, he, hi, Bool.and_true]
  decide

end VG.Proof.Ed25519.X86_64.VerifyMessage
