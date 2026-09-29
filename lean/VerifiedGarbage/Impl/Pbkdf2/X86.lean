import VerifiedGarbage.Impl.Hmac.X86

/-!
# PBKDF2-HMAC-SHA-256's iteration: x86 (32-bit) implementation

`iterate(key, u, n, t, scratch)`, every argument on the stack (cdecl), runs
`n` steps `U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for
the key whose inner and outer streaming states are at `key` and `key + 96`.

The same design as on the other targets (`VG.Impl.Pbkdf2.Arm`): the inner
and outer states have each absorbed one block, so HMAC-SHA-256 of the
32-byte `U` is two compressions (calls of `vg_sha256_compress`, through the
streaming code's `compressAt`), each of one block that is 32 bytes of
message followed by the padding of a 96-byte message.

The hash value being compressed is `t` itself, and `T` is kept in `scratch`
and copied back to `t` at the end. `scratch` holds the compression's scratch
space (`[0..112)`), our caller's `ebx`, `esi`, `edi`, `ebp`
(`[112..128)`, where the streaming code's `save` and `restore` keep them),
`T` (`[160..192)`) and the block (`[192..256)`: the 32 bytes of message,
then the padding, written once). The compression function preserves `ebx`,
`esi`, `edi` and `ebp`, so our variables live there: `ebx` = `t`, `ebp` =
`scratch`, `esi` = `key` and `edi` = the steps left; `eax`, `ecx` and `edx`
are temporaries. Each call uses the 20 bytes below `esp`, for its frame of
arguments and its return address. Every address and branch depends only on
`esp`, the pointers and `n`.
-/

namespace VG.Impl.Pbkdf2.X86

open VG.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (save restore compressAt)
open VG.Impl.Hmac.X86 (bswapWord copyWord)

/-- The padding of a 96-byte message, after 32 bytes of it, in `scratch[224..256)`:
`0x80`, zeros, and the length in bits (768), big-endian. -/
def padding : List Instr :=
  [.mov .ecx (.imm 0x80), .store (at_ .ebp 224) .ecx, .mov .ecx (.imm 0)] ++
  (List.range 6).map (fun k => .store (at_ .ebp (228 + 4 * k)) .ecx) ++
  [.mov .ecx (.imm 0x00030000), .store (at_ .ebp 252) .ecx]

/-- The hash value at `[esi + o]` into `t` (at `ebx`). -/
def load (o : Nat) : List Instr := (List.range 8).flatMap (copyWord .esi .ebx o 0)

/-- The digest (the hash value's words, big-endian) into the block's first 32 bytes. -/
def digest : List Instr := (List.range 8).flatMap (bswapWord .ebx .ebp 0 192)

/-- `T ← T ⊕ U` for 32-bit word `k`, with `T` in `scratch[160..192)` and `U`
the block's first 32 bytes. -/
def xorW (k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .ebp (160 + 4 * k))), .alu .xor .ecx (.mem (at_ .ebp (192 + 4 * k))),
    .store (at_ .ebp (160 + 4 * k)) .ecx]

/-- Pointing `eax` at the block, for `compressAt`. -/
def atBlock : List Instr := [.mov .eax (.reg .ebp), .alu .add .eax (.imm 192)]

/-- One step. -/
def body : Prog isa :=
  .seq (.block (load 0 ++ atBlock))
  (.seq (compressAt .ebx .ebp)
  (.seq (.block (digest ++ load 96 ++ atBlock))
  (.seq (compressAt .ebx .ebp)
    (.block (digest ++ (List.range 8).flatMap xorW ++ [.alu .sub .edi (.imm 1)])))))

/-- Saving our caller's registers, setting up ours, and writing `U` and the
padding into the block and `T` into `scratch`. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ save .eax ++
    [.mov .ebp (.reg .eax), .mov .esi (.mem (at_ .esp 4)), .mov .edi (.mem (at_ .esp 12)),
      .mov .ebx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 8))] ++
    (List.range 8).flatMap (copyWord .edx .ebp 0 192) ++ (List.range 8).flatMap (copyWord .ebx .ebp 0 160) ++
    padding ++ [.alu .test .edi (.reg .edi)]

/-- `T` back into `t`, and restoring our caller's registers. -/
def epilogue : List Instr :=
  (List.range 8).flatMap (copyWord .ebp .ebx 160 0) ++ .mov .eax (.reg .ebp) :: restore .eax

def iterate : Prog isa :=
  .seq (.block prologue)
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block epilogue))

end VG.Impl.Pbkdf2.X86
