import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.X86_64.Target

/-!
# Poly1305: the x86-64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`).
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open X86_64 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let key : Region := ⟨s.gpr .rsi, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧ ret.Disjoint state
  post s s' := Repr s'.mem (s.gpr .rdi) (bytesAt s.mem (s.gpr .rsi) 32) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open X86_64 in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .rdi) key msg →
    Repr s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rsi) (16 * (s.gpr .rdx).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

open X86_64 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], tail: *const u8, len: usize, out: *mut [u8; 16])`. -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let tail : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let out : Region := ⟨s.gpr .rcx, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [tail] ∧ s.wr = [state, out] ∧ state.Disjoint tail ∧ state.Disjoint out ∧
      tail.Disjoint out ∧ ret.Disjoint state ∧ ret.Disjoint out ∧ (s.gpr .rdx).toNat < 16
  post s s' := ∀ key msg, Repr s.mem (s.gpr .rdi) key msg →
    bytesAt s'.mem (s.gpr .rcx) 16 = mac key (msg ++ bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.Poly1305
