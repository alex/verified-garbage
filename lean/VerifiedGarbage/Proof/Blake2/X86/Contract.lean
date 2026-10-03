import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.TCB.X86.Target

/-!
# BLAKE2 on x86 (32-bit): the contracts

The contracts the proofs of the x86 (32-bit) implementations are written
against, for BLAKE2b and BLAKE2s at once (words of `w` bits, the parameters
`P`), with the arguments on the stack (cdecl); the artifacts' contracts are
the shared ones of `Spec/Blake2/Contract.lean`, which imply these. The
streaming functions call the compression function (BLAKE2b's or BLAKE2s's)
through `compressX86`, using the 32 bytes of stack below the return address
(its seven arguments and the return address).
-/

namespace VG.Proof.Blake2

open VG.X86 VG.Spec.Blake2

section
variable {w : Nat} (P : Params w)

/-- x86 (32-bit) contract for
`compress(state, blocks, n, t: u64, last: u32, scratch: *mut [u64; 64])`:
updates the state at `state` with the `n` blocks at `blocks`, block `i` with
the counter `t + bb · i` and the final block flag if `last ≠ 0`.

The code may read the arguments (28 bytes above the return address) and the
blocks, and read and write the state and 512 bytes of scratch space. The
writable buffers may not overlap each other, the blocks, the arguments or the
return address, and nothing may wrap around the end of the (32-bit) address
space. `esp` and the arguments are public. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 8 * (w / 8)⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, blockBytes w * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 6).setWidth 64, 512⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 8 * (w / 8) ≤ 2 ^ 32 ∧ (arg s 1).toNat + blockBytes w * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s s' :=
    stateAt w s'.mem ((arg s 0).setWidth 64) =
      compressBlocks P (stateAt w s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64)
        (arg s 2).toNat (arg s 4 ++ arg s 3).toNat (arg s 5 != 0)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- The 64-bit `count` argument of `update`/`finalize`, in argument slots 1
and 2 (cdecl: the low word first). -/
def countX86 (s : X86.State) : BitVec 64 := arg s 2 ++ arg s 1

/-- x86 (32-bit) contract for `init(state, outlen, key, keylen)`. The code may
read the arguments (16 bytes above the return address) and the key, and
write the state. -/
def initX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, bufOff w + blockBytes w⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [state] ∧ key.Disjoint state ∧ args.Disjoint state ∧
    ret.Disjoint state ∧ (arg s 0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ P.maxBytes ∧ (arg s 3).toNat ≤ P.maxBytes
  post s s' := Repr P (init P (arg s 1).toNat (arg s 3).toNat) s'.mem ((arg s 0).setWidth 64)
    (keyBlock w (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- x86 (32-bit) contract for `update(state, count, data, len, scratch)`. The
code may read the arguments (24 bytes above the return address) and the data,
and read and write the state and 576 bytes of scratch space; it uses the 32
bytes of stack below the return address. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, bufOff w + blockBytes w⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 576⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 576 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ h0 d, Repr P h0 s.mem ((arg s 0).setWidth 64) d → countX86 s = BitVec.ofNat 64 d.length →
    d.length + (arg s 4).toNat < 2 ^ 64 →
    Repr P h0 s'.mem ((arg s 0).setWidth 64) (d ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- x86 (32-bit) contract for `finalize(state, count, out, scratch)`. The code
may read the arguments (20 bytes above the return address), and read and write
the state, the output (`8 · w/8` bytes) and 576 bytes of scratch space; it
uses the 32 bytes of stack below the return address. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, bufOff w + blockBytes w⟩
    let out : Region := ⟨(arg s 3).setWidth 64, bufOff w⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 576⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧ (arg s 3).toNat + bufOff w ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 576 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ h0 d, Repr P h0 s.mem ((arg s 0).setWidth 64) d → d.length < 2 ^ 64 →
    countX86 s = BitVec.ofNat 64 d.length →
    bytesAt s'.mem ((arg s 3).setWidth 64) (bufOff w) = finalHash P h0 d
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end

end VG.Proof.Blake2
