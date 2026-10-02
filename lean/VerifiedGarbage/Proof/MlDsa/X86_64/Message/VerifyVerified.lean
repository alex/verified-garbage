import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCT

/-!
# ML-DSA on x86-64, `verify_message`: verified

Untrusted: everything here is checked by Lean. `verifyMessage n c p`, for
any verification function on `μ` `c` that `verify_message` can call
(`VerifyFn`), is verified against `verifyMessageContract p X86_64.abi 112`.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8000A then 0x01 else 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x80008, 8⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageContract p X86_64.abi 112).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySat mlDsa44
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySat mlDsa65
  · sig_implies_sat [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifySat mlDsa87

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    Verified X86_64.target (verifyMessage n c p) (verifyMessageContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp hV hp h; ⟨t, s', he, ha, hq⟩,
    verifyMessage_ct hV hp, verifyMessage_sat hp⟩

end VG.Proof.MlDsa.X86_64.Message
