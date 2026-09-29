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

/-- The message's length so far, `count`, from the arguments 1 and 2 (cdecl:
the low word first). -/
def countX86 (s : X86.State) : BitVec 64 := X86.arg s 2 ++ X86.arg s 1

open X86 in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 16])`:
the arguments `state`, the low and high words of `count`, `data`, `len` and
`scratch`. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧ state.Disjoint data ∧ state.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem ((arg s 0).setWidth 64) key msg →
    countX86 s = BitVec.ofNat 64 msg.length →
    Buffered s'.mem ((arg s 0).setWidth 64) key (msg ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 16])`:
the arguments `state`, the low and high words of `count`, `out` and
`scratch`. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 16⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧ state.Disjoint out ∧ state.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem ((arg s 0).setWidth 64) key msg →
    countX86 s = BitVec.ofNat 64 msg.length → bytesAt s'.mem ((arg s 3).setWidth 64) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Poly1305
