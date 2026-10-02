import VerifiedGarbage.Proof.Argon2.AArch64.DeriveAbi

/-! A concrete caller establishes satisfiability of the shared derivation contract. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

def satArgs : List Nat := [1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

def satMem (a : Addr) : Byte :=
  let d := a.toNat - 0x40000
  if 0x40000 ≤ a.toNat ∧ a.toNat < 0x40050 then
    ((BitVec.ofNat 64 (satArgs[d / 8]?.getD 0)) >>> (8 * (d % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .x5 => 1 | .x6 => 8 | .x7 => 1 | _ => 0
  sp := 0x40000
  c := false
  v _ := 0
  unknowns _ := 0
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 80⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem contract_sat : ∃ s, (Spec.Argon2.deriveContract AArch64.abi 400).pre s := by
  refine ⟨satState, ?_⟩
  sig_sat_check [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, AArch64.abi,
    AArch64.argRegs, AArch64.firstNarrowStack, AArch64.stackArg, AArch64.stackArgAddr,
    List.range, List.range.loop, satState, satMem, satArgs, Spec.Argon2.params, Spec.Argon2.valid,
    Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]
end VG.Proof.Argon2.AArch64.Derive
