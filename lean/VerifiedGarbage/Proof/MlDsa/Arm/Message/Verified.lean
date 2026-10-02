import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: verified

Untrusted: everything here is checked by Lean. `signMessage n c p` and
`verifyMessage n c p`, for any functions on `μ` `c` they can call
(`SignFn`, `VerifyFn`), are verified against `signMessageContract p Arm.abi
36` and `verifyMessageContract p Arm.abi 36`; `vg_mldsa*_sign` and
`vg_mldsa*_verify` are such functions (`sign44Fn`, …).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition of signing: `ctx_len = 0`, `rnd`,
`sig` and `scratch` on the stack. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80005 then 0x32 else if a = 0x80009 then 0x40 else if a = 0x8000E then 1 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩, ⟨0x80000, 16⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩]

theorem signMessage_sat {p : Params} (hp : p ∈ params) : ∃ s, (signMessageContract p Arm.abi 36).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      [signSat] using signSat mlDsa87

theorem signMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    Verified Arm.target (signMessage n c p) (signMessageContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := signMessage_wp hS hp h; ⟨t, s', he, ha, hq⟩,
    signMessage_ct hS hp, signMessage_sat hp⟩

/-- A state satisfying the precondition of verification: `ctx_len = 0`, `sig`
and `scratch` on the stack. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r3 => 0x3100
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80005 then 0x32 else if a = 0x8000A then 1 else 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x80000, 12⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) : ∃ s, (verifyMessageContract p Arm.abi 36).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] [verifySat] using verifySat mlDsa87

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    Verified Arm.target (verifyMessage n c p) (verifyMessageContract p Arm.abi 36) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessage_ct hV hp, verifyMessage_sat hp⟩

/-! ## The functions on `μ` -/

theorem sign44Fn : SignFn mlDsa44 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa44) :=
  ⟨Sign.sign44_verified', by decide +kernel⟩
theorem sign65Fn : SignFn mlDsa65 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa65) :=
  ⟨Sign.sign65_verified', by decide +kernel⟩
theorem sign87Fn : SignFn mlDsa87 (Impl.MlDsa.Arm.Sign.sign Sign.prims mlDsa87) :=
  ⟨Sign.sign87_verified', by decide +kernel⟩

theorem verify44Fn : VerifyFn mlDsa44 Impl.MlDsa.Arm.Verify.verify44 :=
  ⟨Verify.verify44_verified, by decide +kernel⟩
theorem verify65Fn : VerifyFn mlDsa65 Impl.MlDsa.Arm.Verify.verify65 :=
  ⟨Verify.verify65_verified, by decide +kernel⟩
theorem verify87Fn : VerifyFn mlDsa87 Impl.MlDsa.Arm.Verify.verify87 :=
  ⟨Verify.verify87_verified, by decide +kernel⟩

end VG.Proof.MlDsa.Arm.Message
