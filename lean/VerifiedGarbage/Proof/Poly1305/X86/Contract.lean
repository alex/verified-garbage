import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.X86.Target

/-!
# Poly1305: the x86 (32-bit) contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). Every argument is on the stack (cdecl), above the
return address; the code may read the arguments but not write them.
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open X86 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let key : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [state] ∧ state.Disjoint key ∧ args.Disjoint state ∧
      ret.Disjoint state ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' := Repr s'.mem ((arg s 0).setWidth 64) (bytesAt s.mem ((arg s 1).setWidth 64) 32) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open X86 in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ args.Disjoint state ∧
      ret.Disjoint state ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := ∀ key msg, Repr s.mem ((arg s 0).setWidth 64) key msg →
    Repr s'.mem ((arg s 0).setWidth 64) key
      (msg ++ bytesAt s.mem ((arg s 1).setWidth 64) (16 * (arg s 2).toNat))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

open X86 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], tail: *const u8, len: usize, out: *mut [u8; 16])`. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let tail : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 16⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [tail, args] ∧ s.wr = [state, out] ∧ state.Disjoint tail ∧ state.Disjoint out ∧
      tail.Disjoint out ∧ args.Disjoint state ∧ args.Disjoint out ∧ ret.Disjoint state ∧
      ret.Disjoint out ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ (arg s 2).toNat < 16
  post s s' := ∀ key msg, Repr s.mem ((arg s 0).setWidth 64) key msg →
    bytesAt s'.mem ((arg s 3).setWidth 64) 16 =
      mac key (msg ++ bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.Poly1305
