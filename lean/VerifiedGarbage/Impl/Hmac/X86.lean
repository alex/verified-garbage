import VerifiedGarbage.Impl.Sha256.X86.Stream

/-!
# HMAC-SHA-256: x86 (32-bit) implementation

Two SHA-256 streaming states (`inner`, `outer`; see `VG.Spec.Hmac`). Every
argument is on the stack (cdecl).

* `init(inner, outer, key, key_len, scratch)` stores `H⁽⁰⁾` in both states,
  the block `K₀ ⊕ ipad` in the inner buffer and `K₀ ⊕ opad` (computed from it
  a word at a time, as `(K₀ ⊕ ipad) ⊕ (ipad ⊕ opad)`) in the outer one, and
  compresses both, with the inlined compression function
  (`Impl.Sha256.X86.compress`), whose arguments it writes over its own.
* `finalize(inner, outer, count, out, scratch)` computes the inner hash
  value with the code of `vg_sha256_finalize` up to writing the digest, then
  the outer hash, of `(K₀ ⊕ opad) ‖ digest`, as one compression of a block
  laid out at known offsets, and writes it to `out`.

The inlined compression function saves and restores `ebx`, `esi`, `edi`,
`ebp` itself, so our variables live there; our caller's are saved in
`scratch[112..128)`, as in the streaming functions.

The constant-time analysis follows pointers through memory only while they
are the base address of a writable region, and forgets which words of memory
are public after a store of a secret at an unknown address. So every store
of a key byte goes through a register that is not needed afterwards, and
every pointer needed afterwards is kept in a register.
-/

namespace VG.Impl.Hmac.X86

open VG.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (compressAt save restore)

/-! ## `init`

Registers: `ebx` = `inner`, `esi` = `outer`, `ebp` = `scratch`; in the
loops, `edi` = the next key byte, `edx` = where it goes in the inner buffer,
`ecx` = the key bytes left (then `ipad`), `eax` = the byte (then the end of
the inner buffer). -/

/-- `H⁽⁰⁾` into the state at `b`. -/
def h0 (b : Reg) : List Instr :=
  (List.range 8).flatMap fun k => [.mov .ecx (.imm Spec.Sha256.H0[k]!), .store (at_ b (4 * k)) .ecx]

/-- The key bytes, XORed with `ipad`, into the inner buffer. -/
def keyLoop : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .edi 0), .alu .xor .eax (.imm 0x36), .store8 (at_ .edx 0) .al,
    .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne

/-- `ipad` up to the end of the inner buffer. -/
def padLoop : Prog isa :=
  .loop (.block [.store8 (at_ .edx 0) .cl, .alu .add .edx (.imm 1), .alu .cmp .edx (.reg .eax)]) .ne

/-- Word `k` of the outer buffer, from word `k` of the inner one. -/
def opadWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebx (32 + 4 * k))), .alu .xor .eax (.imm 0x6a6a6a6a),
   .store (at_ .esi (32 + 4 * k)) .eax]

/-- Compress the buffer of the state at `b` into its hash value. -/
def compressBuf (b : Reg) : Prog isa :=
  .seq (.block [.store (at_ .esp 4) b, .store (at_ .esp 16) .ebp, .mov .eax (.reg b),
    .alu .add .eax (.imm 32)]) compressAt

def init : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++ save .eax ++
      [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8))] ++
      h0 .ebx ++ h0 .esi ++
      [.mov .edi (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16)), .mov .edx (.reg .ebx),
       .alu .add .edx (.imm 32), .alu .test .ecx (.reg .ecx)]))
  (.seq (.ite .e (.block []) keyLoop)
  (.seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 96), .mov .ecx (.imm 0x36),
      .alu .cmp .edx (.reg .eax)])
  (.seq (.ite .e (.block []) padLoop)
  (.seq (.block ((List.range 16).flatMap opadWord))
  (.seq (compressBuf .ebx)
  (.seq (compressBuf .esi)
    (.block (.mov .eax (.reg .ebp) :: restore .eax))))))))

/-! ## `finalize`

`vg_sha256_finalize` (`Impl.Sha256.X86.Stream.finalize`) is used up to
writing the digest (`finalizeHash`), with our arguments rearranged into its
`(state, count lo, count hi, out, scratch)`: it saves our caller's
`ebx, esi, edi, ebp` in `scratch[112..128)` (we have not changed them yet)
and `out` in `scratch[136]`, and leaves the inner hash value in the inner
state, `inner` in `ebx` and `scratch` in `ebp`. The address of `outer` is
kept in `scratch[176]`.

The outer hash, of the 96 bytes `(K₀ ⊕ opad) ‖ digest`, is then a single
compression of a block laid out at known offsets: the inner state gets the
outer hash value and, in its buffer, the digest (big-endian), `0x80`, zeros
and the length in bits (768, big-endian). Its hash value is the MAC,
written big-endian to `out` last. (The constant-time analysis loses track of
which words in memory are public once the padding of `finalizeHash` is
written at a variable address, but the registers holding `inner` and
`scratch` stay known.) -/

/-- `vg_sha256_finalize` up to writing the digest. -/
def finalizeHash : Prog isa :=
  match Impl.Sha256.X86.Stream.finalize with
  | .seq a (.seq b (.seq c _)) => .seq a (.seq b c)
  | p => p

/-- Word `k` from `[src + o₁]` to `[dst + o₂]`, byte-swapped. -/
def bswapWord (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ src (o₁ + 4 * k))), .bswap .ecx, .store (at_ dst (o₂ + 4 * k)) .ecx]

/-- Word `k` from `[src + o₁]` to `[dst + o₂]`. -/
def copyWord (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ src (o₁ + 4 * k))), .store (at_ dst (o₂ + 4 * k)) .ecx]

/-- The rest of the block: `0x80`, zeros, and the length in bits, 768, big-endian. -/
def padWords : List Instr :=
  [.mov .ecx (.imm 0x80), .store (at_ .ebx 64) .ecx, .mov .ecx (.imm 0)] ++
  (List.range 6).map (fun k => .store (at_ .ebx (68 + 4 * k)) .ecx) ++
  [.mov .ecx (.imm 0x00030000), .store (at_ .ebx 92) .ecx]

def finalize : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .esp 24)), .mov .ecx (.mem (at_ .esp 8)), .store (at_ .edx 176) .ecx,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .esp 8) .ecx,
      .mov .ecx (.mem (at_ .esp 16)), .store (at_ .esp 12) .ecx,
      .mov .ecx (.mem (at_ .esp 20)), .store (at_ .esp 16) .ecx, .store (at_ .esp 20) .edx])
  (.seq finalizeHash
  -- The inner digest into the inner buffer, and the outer hash value into the inner state.
  (.seq (.block ((List.range 8).flatMap (bswapWord .ebx .ebx 0 32) ++ .mov .edx (.mem (at_ .ebp 176)) ::
      (List.range 8).flatMap (copyWord .edx .ebx 0 0) ++ padWords ++
      [.store (at_ .esp 4) .ebx, .store (at_ .esp 16) .ebp, .mov .eax (.reg .ebx), .alu .add .eax (.imm 32)]))
  (.seq compressAt
    (.block (.mov .eax (.mem (at_ .ebp 136)) :: (List.range 8).flatMap (bswapWord .ebx .eax 0 0) ++
      .mov .eax (.reg .ebp) :: restore .eax)))))

end VG.Impl.Hmac.X86
