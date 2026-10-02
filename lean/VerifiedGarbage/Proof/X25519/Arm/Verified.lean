import VerifiedGarbage.Proof.X25519.Arm.Main
import VerifiedGarbage.Proof.X25519.Arm.CT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.X25519.Contract

/-!
# X25519 on 32-bit ARM: verified

`vg_x25519` meets the shared contract of `Spec/X25519/Contract.lean`: the
proof against `x25519Arm`, which it implies, and a state satisfying it.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm

theorem x25519_ok (s : State) (hs : x25519Arm.pre s) :
    ∃ t s', Exec isa Impl.X25519.Arm.x25519 s t s' ∧ abiPreserved s s' ∧ x25519Arm.post s s' :=
  x25519_correct (XPre.of hs)

theorem x25519_ct' : ConstantTime isa x25519Arm.pre x25519Arm.pub Impl.X25519.Arm.x25519 :=
  x25519_ct fun _ _ _ _ ⟨_, h0, h1, h2, h3⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified Arm.target Impl.X25519.Arm.x25519 (Spec.X25519.x25519Contract Arm.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.Arm.x25519Arm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.X25519.Arm.x25519Sat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X25519.Arm.x25519Sat)

end VG.Proof.X25519.Arm
