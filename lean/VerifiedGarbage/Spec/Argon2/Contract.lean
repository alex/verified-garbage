import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.TCB.Artifact

/-!
# Argon2: contracts on every target

**Trusted** (as every file in `Spec/`). The compression function G, H′,
and the complete Argon2 derivation of RFC 9106, including all hashing,
memory filling and finalization in verified assembly. The Rust caller
validates parameters and supplies allocations; it does not implement any
cryptographic step. Version 1.3 (0x13) is fixed by the specification.

Only pointers, lengths and numeric parameters are public. Password, salt,
secret, associated data, intermediate blocks and output remain secret.
Argon2d/id permit leakage of their data-dependent reference block indices,
as specified by `references`; Argon2i permits no secret-dependent leakage.
The worker limit `threads` is public and does not affect the derived key.
It is a maximum, so a serial implementation is permitted for any valid
limit. Lanes are algorithm inputs and must never be reduced to this limit.

The caller provides `m′` 1024-byte memory blocks and 16 KiB of scratch.
Scratch has room for the block permutation, address-generation blocks,
BLAKE2b state and scratch, and saved arguments. It has a fixed size because
the entry point permits serial evaluation of the lanes. `stack` and
`writeArgs` account for the verified calls within the derivation.
-/

namespace VG.Spec.Argon2

open Blake2 (bytesAt)

/-- A block at `p`, decoded as little-endian words. -/
def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun j => m.read (p + BitVec.ofNat 64 (8 * j.val)) 8

/-- `vg_argon2_compress(x: *const [u64; 128], y: *const [u64; 128],
out: *mut [u64; 128], scratch: *mut [u64; 512])`.
G: two input blocks, one output block and 4 KiB of working space. -/
def compressSig : Sig where
  params := [("x", .array false .u64 128), ("y", .array false .u64 128),
    ("out", .array true .u64 128), ("scratch", .array true .u64 512)]

def compressContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  compressSig.contract A
    (post := fun x y out _scratch m m' _ => blockAt m' out = compress (blockAt m x) (blockAt m y))
    (writeArgs := true) (stack := stack)

def compressApi : Api where
  module := "argon2"
  name := "vg_argon2_compress"
  sig := compressSig
  writeArgs := true
  contracts := some fun A stack => compressContract A stack
  summary := "Argon2's compression function G (RFC 9106 §3.5–3.6): writes G(*x, *y) to \
    `*out`. Each block is 128 little-endian 64-bit words.\n\n\
    Contract: `VG.Spec.Argon2.compressContract`. Constant time: only the pointers may affect \
    timing, not the input blocks."
  safety := ["`scratch` is working space: its contents on return are unspecified."]

/-- `vg_argon2_hprime(input: *const u8, input_len: usize, out: *mut u8,
out_len: usize, scratch: *mut [u64; 2048])`.
H′ with a runtime output length, including the LE32 length prefix. -/
def hPrimeSig : Sig where
  params := [("input", .slice false .u8 "input_len"), ("out", .slice true .u8 "out_len"),
    ("scratch", .array true .u64 2048)]

def hPrimeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  hPrimeSig.contract A
    (pre := fun _input inputLen _out outLen _scratch _m =>
      inputLen.toNat < 2 ^ 32 ∧ 1 ≤ outLen.toNat ∧ outLen.toNat < 2 ^ 32)
    (post := fun input inputLen out outLen _scratch m m' _ =>
      bytesAt m' out outLen.toNat = hPrime outLen.toNat (bytesAt m input inputLen.toNat))
    (writeArgs := true) (stack := stack)

def hPrimeApi : Api where
  module := "argon2"
  name := "vg_argon2_hprime"
  sig := hPrimeSig
  writeArgs := true
  contracts := some fun A stack => hPrimeContract A stack
  summary := "Argon2's variable-length hash H′ (RFC 9106 §3.3): hashes the `input_len` bytes \
    at `input` to `out_len` bytes at `out`, including the LE32 output-length prefix and \
    the BLAKE2b chaining required for outputs longer than 64 bytes.\n\n\
    Contract: `VG.Spec.Argon2.hPrimeContract`. Constant time: only pointers and lengths may \
    affect timing, not the input or the output."
  safety := ["`input_len` must be less than 2^32; `out_len` must be in 1..2^32-1.",
    "`scratch` is working space: its contents on return are unspecified."]

/-- Decode the public type parameter. The contract requires `kind ≤ 2`. -/
def params (kind passes memory lanes tagLen : Nat) : Params :=
  { variant := if kind = 0 then .d else if kind = 1 then .i else .id,
    passes, memory, lanes, tagLen }

/-- `vg_argon2(kind: u32, password: *const u8, password_len: usize,
salt: *const u8, salt_len: usize, iterations: u32, memory_cost: u32,
lanes: u32, threads: u32, secret: *const u8, secret_len: usize,
associated_data: *const u8, ad_len: usize, memory: *mut [u64; 128],
blocks: usize, scratch: *mut [u64; 2048], out: *mut u8, out_len: usize)`.
Complete derivation. `memory_cost` is in KiB; `blocks` is the rounded
allocation length, in 1024-byte blocks. All four byte-string inputs are
secret. `threads` is a positive maximum worker count, independent of
`lanes`. Scratch is 2048 words (16 KiB). -/
def deriveSig : Sig where
  params := [("kind", .int .u32 true),
    ("password", .slice false .u8 "password_len"), ("salt", .slice false .u8 "salt_len"),
    ("iterations", .int .u32 true), ("memory_cost", .int .u32 true),
    ("lanes", .int .u32 true), ("threads", .int .u32 true),
    ("secret", .slice false .u8 "secret_len"), ("associated_data", .slice false .u8 "ad_len"),
    ("memory", .slice true (.array .u64 128) "blocks"),
    ("scratch", .array true .u64 2048), ("out", .slice true .u8 "out_len")]

/-- RFC 9106 §3.2, end to end. No preinitialized blocks, hashes or Rust
cryptographic computations are required. The allocation length uses the
rounded memory count, but H₀ uses the original `memory_cost`. -/
def deriveContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  deriveSig.contract A
    (pre := fun kind _password passwordLen _salt saltLen iterations memoryCost lanes threads
        _secret secretLen _ad adLen _memory blocks _scratch _out outLen _m =>
      let p := params kind.toNat iterations.toNat memoryCost.toNat lanes.toNat outLen.toNat
      kind.toNat ≤ 2 ∧ valid p passwordLen.toNat saltLen.toNat secretLen.toNat adLen.toNat ∧
        1 ≤ threads.toNat ∧ threads.toNat < 2 ^ 24 ∧ blocks.toNat = p.blocks)
    (post := fun kind password passwordLen salt saltLen iterations memoryCost lanes _threads
        secret secretLen ad adLen _memory _blocks _scratch out outLen m m' _ =>
      bytesAt m' out outLen.toNat =
        derive (params kind.toNat iterations.toNat memoryCost.toNat lanes.toNat outLen.toNat)
          (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat)
          (bytesAt m secret secretLen.toNat) (bytesAt m ad adLen.toNat))
    (writeArgs := true) (stack := stack)
    (leak := some fun kind password passwordLen salt saltLen iterations memoryCost lanes _threads
        secret secretLen ad adLen _memory _blocks _scratch _out outLen m =>
      references (params kind.toNat iterations.toNat memoryCost.toNat lanes.toNat outLen.toNat)
        (bytesAt m password passwordLen.toNat) (bytesAt m salt saltLen.toNat)
        (bytesAt m secret secretLen.toNat) (bytesAt m ad adLen.toNat))

def deriveApi : Api where
  module := "argon2"
  name := "vg_argon2"
  sig := deriveSig
  writeArgs := true
  contracts := some fun A stack => deriveContract A stack
  summary := "Argon2 version 1.3 (RFC 9106): derives `out_len` bytes at `out` from the \
    password, salt, optional secret and associated data. `kind` selects Argon2d (0), \
    Argon2i (1) or Argon2id (2). Performs the entire derivation: H₀, H′, initialization, \
    all memory-filling passes, the final lane XOR and H′ of that block.\n\n\
    `iterations` is the pass count, `memory_cost` is the requested KiB count, and `lanes` \
    is the algorithm's parallelism parameter. `threads` limits execution workers and \
    does not change the result; serial execution is permitted.\n\n\
    Contract: `VG.Spec.Argon2.deriveContract`. Argon2i is constant time in all input contents. \
    Argon2d/id additionally permit timing to depend on the sequence of data-dependent \
    reference block indices (`VG.Spec.Argon2.references`), as required by their addressing \
    rules, but on nothing else secret. Pointers, lengths and numeric parameters are public."
  safety := ["`kind` must be 0, 1 or 2; `iterations` must be positive; `lanes` and `threads` \
      must be in 1..2^24-1; `memory_cost` must be at least `8 * lanes`.",
    "All input lengths must be less than 2^32; `out_len` must be in 4..2^32-1.",
    "`blocks` must equal `4 * lanes * floor(memory_cost / (4 * lanes))`.",
    "`memory` and `scratch` are working space: their initial contents are arbitrary and \
      their contents on return are unspecified."]

end VG.Spec.Argon2
