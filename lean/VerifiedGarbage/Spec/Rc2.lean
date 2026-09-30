import VerifiedGarbage.TCB.Mem

/-!
# RC2 and CBC

**Trusted** (as every file in `Spec/`). RC2 is transcribed from RFC 2268
§§2–4 (https://www.rfc-editor.org/rfc/rfc2268). Words are 16 bits, with
arithmetic modulo 2¹⁶; blocks and the expanded key use little-endian words.
Keys have 1–128 bytes and effective key lengths have 1–1024 bits. These
are independent parameters: effective bits may exceed the supplied key's
bit length. Neither parameter is silently clamped.

CBC uses the recurrence of NIST SP 800-38A §6.2, with RC2's 8-byte block
size (this does not assert that RC2 is a NIST-approved cipher).

The streaming model follows issue #1's `init(key, iv, direction)`,
`update(ctx, data)` and `finalize(ctx)`. The default effective bit count is
eight times the key length; `initWithEffectiveBits` makes it explicit.
Updates emit all complete blocks and retain a partial block. Finalization
rejects a partial block; padding is the caller's responsibility. The
immutable model returns the next context; the Rust API can mutate its own
context and consume it on finalization.

These functions describe values, not timing. In particular, neither the
PITABLE indices nor the mashing-round indices are public in the contracts:
an implementation must prove constant time despite these secret indices.
-/

namespace VG.Spec.Rc2

abbrev Word := BitVec 16
abbrev Block := Vector Byte 8
abbrev State := Vector Word 4
abbrev Schedule := Vector Word 64

/-- RFC 2268 §2, PITABLE (not the distinct RC2Version table in §6). -/
def piTable : Vector Byte 256 :=
  let rows : Vector (Vector Byte 16) 16 := #v[
    #v[0xd9, 0x78, 0xf9, 0xc4, 0x19, 0xdd, 0xb5, 0xed, 0x28, 0xe9, 0xfd, 0x79, 0x4a, 0xa0, 0xd8, 0x9d],
    #v[0xc6, 0x7e, 0x37, 0x83, 0x2b, 0x76, 0x53, 0x8e, 0x62, 0x4c, 0x64, 0x88, 0x44, 0x8b, 0xfb, 0xa2],
    #v[0x17, 0x9a, 0x59, 0xf5, 0x87, 0xb3, 0x4f, 0x13, 0x61, 0x45, 0x6d, 0x8d, 0x09, 0x81, 0x7d, 0x32],
    #v[0xbd, 0x8f, 0x40, 0xeb, 0x86, 0xb7, 0x7b, 0x0b, 0xf0, 0x95, 0x21, 0x22, 0x5c, 0x6b, 0x4e, 0x82],
    #v[0x54, 0xd6, 0x65, 0x93, 0xce, 0x60, 0xb2, 0x1c, 0x73, 0x56, 0xc0, 0x14, 0xa7, 0x8c, 0xf1, 0xdc],
    #v[0x12, 0x75, 0xca, 0x1f, 0x3b, 0xbe, 0xe4, 0xd1, 0x42, 0x3d, 0xd4, 0x30, 0xa3, 0x3c, 0xb6, 0x26],
    #v[0x6f, 0xbf, 0x0e, 0xda, 0x46, 0x69, 0x07, 0x57, 0x27, 0xf2, 0x1d, 0x9b, 0xbc, 0x94, 0x43, 0x03],
    #v[0xf8, 0x11, 0xc7, 0xf6, 0x90, 0xef, 0x3e, 0xe7, 0x06, 0xc3, 0xd5, 0x2f, 0xc8, 0x66, 0x1e, 0xd7],
    #v[0x08, 0xe8, 0xea, 0xde, 0x80, 0x52, 0xee, 0xf7, 0x84, 0xaa, 0x72, 0xac, 0x35, 0x4d, 0x6a, 0x2a],
    #v[0x96, 0x1a, 0xd2, 0x71, 0x5a, 0x15, 0x49, 0x74, 0x4b, 0x9f, 0xd0, 0x5e, 0x04, 0x18, 0xa4, 0xec],
    #v[0xc2, 0xe0, 0x41, 0x6e, 0x0f, 0x51, 0xcb, 0xcc, 0x24, 0x91, 0xaf, 0x50, 0xa1, 0xf4, 0x70, 0x39],
    #v[0x99, 0x7c, 0x3a, 0x85, 0x23, 0xb8, 0xb4, 0x7a, 0xfc, 0x02, 0x36, 0x5b, 0x25, 0x55, 0x97, 0x31],
    #v[0x2d, 0x5d, 0xfa, 0x98, 0xe3, 0x8a, 0x92, 0xae, 0x05, 0xdf, 0x29, 0x10, 0x67, 0x6c, 0xba, 0xc9],
    #v[0xd3, 0x00, 0xe6, 0xcf, 0xe1, 0x9e, 0xa8, 0x2c, 0x63, 0x16, 0x01, 0x3f, 0x58, 0xe2, 0x89, 0xa9],
    #v[0x0d, 0x38, 0x34, 0x1b, 0xab, 0x33, 0xff, 0xb0, 0xbb, 0x48, 0x0c, 0x5f, 0xb9, 0xb1, 0xcd, 0x2e],
    #v[0xc5, 0xf3, 0xdb, 0x47, 0xe5, 0xa5, 0x9c, 0x77, 0x0a, 0xa6, 0x20, 0x68, 0xfe, 0x7f, 0xc1, 0xad]]
  rows.flatten

def pi (b : Byte) : Byte := piTable.getD b.toNat 0

/-- The valid key parameters of RFC 2268 §§2 and 6. -/
def validKey (keyLen effectiveBits : Nat) : Prop :=
  1 ≤ keyLen ∧ keyLen ≤ 128 ∧ 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024

instance (keyLen effectiveBits : Nat) : Decidable (validKey keyLen effectiveBits) :=
  inferInstanceAs (Decidable (1 ≤ keyLen ∧ keyLen ≤ 128 ∧
    1 ≤ effectiveBits ∧ effectiveBits ≤ 1024))

/-- §2: fill L to 128 bytes, reduce to T1 effective bits, then run the
descending XOR/PITABLE loop. Defined for all inputs, used only with valid
key parameters. For T1 = 1024 the descending loop is empty. -/
def expandBytes (key : List Byte) (effectiveBits : Nat) : Vector Byte 128 := Id.run do
  let t := key.length
  let mut l : Vector Byte 128 := Vector.ofFn fun i => key.getD i 0
  for j in List.range (128 - t) do
    let i := t + j
    l := l.set! i (pi (l.getD (i - 1) 0 + l.getD (i - t) 0))
  let t8 := (effectiveBits + 7) / 8
  let tm := BitVec.ofNat 8 (255 % 2 ^ (8 + effectiveBits - 8 * t8))
  l := l.set! (128 - t8) (pi (l.getD (128 - t8) 0 &&& tm))
  for j in List.range (128 - t8) do
    let i := 127 - t8 - j
    l := l.set! i (pi (l.getD (i + 1) 0 ^^^ l.getD (i + t8) 0))
  return l

/-- §2: K[i] = L[2i] + 256 L[2i+1]. -/
def expandKey (key : List Byte) (effectiveBits : Nat) : Schedule :=
  let l := expandBytes key effectiveBits
  Vector.ofFn fun i => (l.getD (2 * i.val) 0).zeroExtend 16 |||
    ((l.getD (2 * i.val + 1) 0).zeroExtend 16 <<< 8)

def decodeBlock (b : Block) : State :=
  Vector.ofFn fun i => (b.getD (2 * i.val) 0).zeroExtend 16 |||
    ((b.getD (2 * i.val + 1) 0).zeroExtend 16 <<< 8)

def encodeBlock (r : State) : Block :=
  Vector.ofFn fun i => ((r.getD (i.val / 2) 0) >>> (8 * (i.val % 2))).setWidth 8

/-- §3.1: the rotations s[0..3]. -/
def rotation (i : Nat) : Nat := #[1, 2, 3, 5][i % 4]!

/-- §3.1, a single mix, using the current (already partly updated) state. -/
def mix (k : Schedule) (j i : Nat) (r : State) : State :=
  let a := r.getD ((i + 3) % 4) 0
  let b := r.getD ((i + 2) % 4) 0
  let c := r.getD ((i + 1) % 4) 0
  r.set! i ((r.getD i 0 + k.getD j 0 + (a &&& b) + (~~~a &&& c)).rotateLeft (rotation i))

/-- §3.2, mixing round number `round` (0–15). -/
def mixRound (k : Schedule) (round : Nat) (r : State) : State :=
  (List.range 4).foldl (fun r i => mix k (4 * round + i) i r) r

/-- §§3.3–3.4, sequential mashing (each step sees preceding writes). -/
def mash (k : Schedule) (i : Nat) (r : State) : State :=
  r.set! i (r.getD i 0 + k.getD ((r.getD ((i + 3) % 4) 0 &&& 63).toNat) 0)

def mashRound (k : Schedule) (r : State) : State :=
  (List.range 4).foldl (fun r i => mash k i r) r

/-- §4.1: rotate right, then subtract the key and composite word. -/
def reverseMix (k : Schedule) (j i : Nat) (r : State) : State :=
  let a := r.getD ((i + 3) % 4) 0
  let b := r.getD ((i + 2) % 4) 0
  let c := r.getD ((i + 1) % 4) 0
  r.set! i ((r.getD i 0).rotateRight (rotation i) - k.getD j 0 - (a &&& b) - (~~~a &&& c))

/-- §4.2: undo mixing round `round`, in order 3, 2, 1, 0. -/
def reverseMixRound (k : Schedule) (round : Nat) (r : State) : State :=
  [3, 2, 1, 0].foldl (fun r i => reverseMix k (4 * round + i) i r) r

/-- §§4.3–4.4: reverse mashing, also in order 3, 2, 1, 0. -/
def reverseMash (k : Schedule) (i : Nat) (r : State) : State :=
  r.set! i (r.getD i 0 - k.getD ((r.getD ((i + 3) % 4) 0 &&& 63).toNat) 0)

def reverseMashRound (k : Schedule) (r : State) : State :=
  [3, 2, 1, 0].foldl (fun r i => reverseMash k i r) r

/-- §3.5: 5 mixing rounds, mash, 6 mixing rounds, mash, 5 mixing rounds. -/
def encryptBlock (k : Schedule) (b : Block) : Block :=
  encodeBlock ((List.range 16).foldl (fun r j =>
    let r := mixRound k j r
    if j = 4 ∨ j = 10 then mashRound k r else r) (decodeBlock b))

/-- §4.5: undo rounds 15–11, mash, rounds 10–5, mash, rounds 4–0. -/
def decryptBlock (k : Schedule) (b : Block) : Block :=
  encodeBlock ((List.range 16).foldl (fun r j =>
    let r := reverseMixRound k (15 - j) r
    if j = 4 ∨ j = 10 then reverseMashRound k r else r) (decodeBlock b))

inductive Direction | encrypt | decrypt
  deriving DecidableEq, Repr

def xorBlock (a b : Block) : Block :=
  Vector.ofFn fun i => a[i] ^^^ b[i]

/-- CBC (§6.2), returning `(output, next IV)`. Decryption retains the
original ciphertext as the next IV, including for an in-place caller. -/
def cbcStep (k : Schedule) (direction : Direction) (iv input : Block) : Block × Block :=
  match direction with
  | .encrypt => let out := encryptBlock k (xorBlock input iv); (out, out)
  | .decrypt => (xorBlock (decryptBlock k input) iv, input)

/-- CBC on complete blocks, including the final chaining value. On empty
input the output is empty and the IV is unchanged. -/
def cbc (k : Schedule) (direction : Direction) (iv : Block) :
    List Block → List Block × Block
  | [] => ([], iv)
  | b :: bs =>
    let (out, iv') := cbcStep k direction iv b
    let (rest, last) := cbc k direction iv' bs
    (out :: rest, last)

/-- Complete blocks only; a partial suffix is handled by `update`. -/
def blocks (data : List Byte) : List Block :=
  (List.range (data.length / 8)).map fun j =>
    Vector.ofFn fun i => data.getD (8 * j + i.val) 0

structure Context where
  schedule : Schedule
  direction : Direction
  iv : Block
  pending : List Byte := []

inductive Error | invalidKeyLength | invalidEffectiveBits | invalidIvLength | incompleteBlock
  deriving DecidableEq, Repr

/-- Initialize CBC with explicitly selected effective key bits (1–1024). -/
def initWithEffectiveBits (key iv : List Byte) (direction : Direction) (effectiveBits : Nat) :
    Except Error Context := do
  unless 1 ≤ key.length ∧ key.length ≤ 128 do throw .invalidKeyLength
  unless 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024 do throw .invalidEffectiveBits
  unless iv.length = 8 do throw .invalidIvLength
  return {
    schedule := expandKey key effectiveBits
    direction := direction
    iv := Vector.ofFn fun i => iv.getD i 0 }

/-- Issue #1's initialization, defaulting to the supplied key's bit length. -/
def init (key iv : List Byte) (direction : Direction) : Except Error Context :=
  initWithEffectiveBits key iv direction (8 * key.length)

/-- Emit all complete blocks, retaining at most seven bytes for the next
update. Empty updates leave every valid context unchanged. -/
def update (ctx : Context) (data : List Byte) : Context × List Byte :=
  let input := ctx.pending ++ data
  let (output, iv) := cbc ctx.schedule ctx.direction ctx.iv (blocks input)
  ({ ctx with iv, pending := input.drop (8 * (input.length / 8)) },
    output.flatMap Vector.toList)

/-- Unpadded CBC: success emits no bytes; a trailing partial block is an
error in either direction. -/
def finalize (ctx : Context) : Except Error (List Byte) :=
  if ctx.pending.isEmpty then .ok [] else .error .incompleteBlock

/-! ## Memory layouts for the contracts -/

def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)

/-- The schedule is 128 bytes, pairs of bytes encoding little-endian words. -/
def scheduleAt (m : Mem) (p : Addr) : Schedule :=
  Vector.ofFn fun i =>
    (m (p + BitVec.ofNat 64 (2 * i.val))).zeroExtend 16 |||
    ((m (p + BitVec.ofNat 64 (2 * i.val + 1))).zeroExtend 16 <<< 8)

def blocksAt (m : Mem) (p : Addr) (n : Nat) : List Block :=
  (List.range n).map fun i => blockAt m (p + BitVec.ofNat 64 (8 * i))

end VG.Spec.Rc2
