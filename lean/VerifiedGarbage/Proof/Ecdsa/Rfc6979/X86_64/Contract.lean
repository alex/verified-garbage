import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA over P-256 with HMAC-SHA-256 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract` for x86-64
and 160 bytes of stack, by name:
`vg_ecdsa_p256_sha256_sign(out = rdi, d = rsi, digest = rdx, scratch = rcx)`,
the result in `eax`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  Spec.Ecdsa.Rfc6979.P256Sha256.inst.result m d digest

def rfcX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 64⟩
    let d : Region := ⟨s.gpr .rsi, 32⟩
    let digest : Region := ⟨s.gpr .rdx, 32⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 160, 160⟩
    160 ≤ (s.gpr .rsp).toNat ∧ s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint d ∧ ret.Disjoint digest ∧ ret.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match (result s.mem (s.gpr .rsi) (s.gpr .rdx)).1 with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    (result s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)).2

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem implies : rfcX86_64.Implies (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86_64.abi 160) := by
  exact
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      post := by
        sig_implies_post [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64]
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, rfcX86_64] at h
        obtain ⟨h0, hl, h1, h2, h3, h4⟩ := h
        exact ⟨h0, h1, h2, h3, h4, (List.cons.inj hl).1⟩
      sat := by
        sig_implies_sat [Spec.Ecdsa.Rfc6979.P256Sha256.inst, Spec.Ecdsa.Rfc6979.Instance.signContract,
          Spec.Ecdsa.Rfc6979.Instance.signSig, Spec.Ecdsa.P256.inst, Spec.P256.curve, Spec.Ecdsa.scratchWords,
          X86_64.abi, X86_64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdsa.Rfc6979.X86_64
