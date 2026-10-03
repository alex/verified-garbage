import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA over P-256 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.P256.inst.signContract` for x86-64, by name:
`vg_ecdsa_p256_sign(out = rdi, d = rsi, digest = rdx, k = rcx, scratch = r8)`,
the result in `eax`.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P256.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.P256.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 64⟩
    let d : Region := ⟨s.gpr .rsi, 32⟩
    let digest : Region := ⟨s.gpr .rdx, 32⟩
    let k : Region := ⟨s.gpr .rcx, 32⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem implies : signX86_64.Implies (Spec.Ecdsa.P256.inst.signContract X86_64.abi) := by
  sig_implies [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, signX86_64, sig]
    [satState] using satState

end VG.Proof.Ecdsa.X86_64
