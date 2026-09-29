import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.Arm.Target

/-!
# Poly1305: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`).
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open Arm in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let key : Region := ⟨State.addr (s.gpr .r1), 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) (bytesAt s.mem (State.addr (s.gpr .r1)) 32) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open Arm in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 16 * (s.gpr .r2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 * (s.gpr .r2).toNat ≤ 2 ^ 32
  post s s' := ∀ key msg, Repr s.mem (State.addr (s.gpr .r0)) key msg →
    Repr s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (s.gpr .r1)) (16 * (s.gpr .r2).toNat))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

open Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open Arm in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 16])`:
`state` in `r0`, `count` in `r2:r3`, and `data`, `len` and `scratch` the stack
arguments 0, 1 and 2. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem (State.addr (s.gpr .r0)) key msg →
    countArm s = BitVec.ofNat 64 msg.length →
    Buffered s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open Arm in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 16])`:
`state` in `r0`, `count` in `r2:r3`, and `out` and `scratch` the stack
arguments 0 and 1. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let out : Region := ⟨State.addr (stackArg s 0), 16⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem (State.addr (s.gpr .r0)) key msg →
    countArm s = BitVec.ofNat 64 msg.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 16 = mac key msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Poly1305
