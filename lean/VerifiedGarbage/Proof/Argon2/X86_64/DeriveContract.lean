import VerifiedGarbage.Proof.Argon2.X86_64.DeriveAbi

/-! A concrete caller establishes satisfiability of the shared derivation contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def satArgs : List Nat := [8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

def satMem (a : Addr) : Byte :=
  let d := a.toNat - 0x40008
  if 0x40008 ≤ a.toNat ∧ a.toNat < 0x40068 then
    ((BitVec.ofNat 64 (satArgs[d / 8]?.getD 0)) >>> (8 * (d % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .rsp => 0x40000 | .r9 => 1 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40008, 96⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem contract_sat : ∃ s, (Spec.Argon2.deriveContract X86_64.abi 344).pre s := by
  refine ⟨satState, ?_⟩
  sig_sat_check [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop,
    satState, satMem, satArgs, Spec.Argon2.params, Spec.Argon2.valid,
    Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]

end VG.Proof.Argon2.X86_64.Derive
