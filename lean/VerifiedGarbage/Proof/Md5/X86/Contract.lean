import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.X86.Target

/-!
# MD5: the x86 (32-bit) contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the x86 (32-bit) implementations of the compression function and of
streaming MD5 (`init`/`update`/`finalize`, on the representation `Repr`), in
terms of `Spec/Md5.lean`.

The shared contracts let the streaming functions write their own argument
area (cdecl passes the arguments in the caller's frame, just above the
return address, and the callee owns them). `update` only reads it, and its
contract here says so; `finalize`'s lets it write them. `update` and
`finalize` call the compression function, using the 20 bytes of stack below
the return address.
-/

namespace VG.Proof.Md5

open Spec.Md5

open X86 in
/-- x86 (32-bit) contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`,
whose arguments are on the stack (cdecl): updates the MD buffer at `state`
with the `n` 64-byte blocks at `blocks`.

The code may read the arguments (16 bytes above the return address) and
`blocks` (`64 * n` bytes), and read and write `state` (16 bytes) and
`scratch` (64 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the blocks, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers and `n`) are public; the MD buffer and
the blocks are secret. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 64 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) =
      compressBlocks (stateAt s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64)
        (arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

open X86 in
/-- The 64-bit `count` argument of `update`/`finalize`, in argument slots 1
and 2 (cdecl: the low word first). -/
def countX86 (s : X86.State) : BitVec 64 := arg s 2 ++ arg s 1

open X86 in
/-- x86 (32-bit) contract for `vg_md5_init(state: *mut [u8; 80])`, whose
argument is on the stack (cdecl): makes the streaming state at `state`
represent the empty message.

The code may read the argument (4 bytes above the return address) and write
`state` (80 bytes), which may not overlap the argument or the return address;
nothing may wrap around the end of the (32-bit) address space. `esp` and the
pointer are public. -/
def initX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
    let args : Region := ⟨argAddr s 0, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  post s s' := Repr s'.mem ((arg s 0).setWidth 64) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

open X86 in
/-- x86 (32-bit) contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `data`, `len`, `scratch`): if the streaming state at `state`
represents a message `m` of `count` bytes (modulo 2⁶⁴), then afterwards it
represents `m` followed by the `len` bytes at `data`.

The code may read the arguments (24 bytes above the return address) and
`data` (`len` bytes), and read and write `state` (80 bytes) and `scratch`
(112 bytes, whose contents on exit are unspecified). The writable buffers may not
overlap each other, the data or the arguments; none of them may overlap the
return address or the 20 bytes of stack below it; and nothing may wrap
around the end of the (32-bit) address space. `esp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 112⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 112 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem ((arg s 0).setWidth 64) m → countX86 s = BitVec.ofNat 64 m.length →
    Repr s'.mem ((arg s 0).setWidth 64) (m ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `out`, `scratch`): if the streaming state at `state` represents a
message `m` of `count` bytes (modulo 2⁶⁴), writes the MD5 digest of `m` to
`out`.

The code may read and write the arguments (20 bytes above the return
address, whose contents on exit are unspecified), `state` (80 bytes, whose
contents on exit are unspecified), `out` (16 bytes) and `scratch` (112
bytes, whose contents on exit are unspecified). These may not overlap each
other or the return address; none of the buffers may overlap the 20 bytes
of stack below the return address; and nothing may wrap around the end of
the (32-bit) address space. `esp`, the pointers and `count` are public; the
state is secret. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 16⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 112⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 112 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem ((arg s 0).setWidth 64) m → countX86 s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem ((arg s 3).setWidth 64) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Md5
