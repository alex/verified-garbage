import VerifiedGarbage.TCB.Mem

/-!
# BLAKE2b and BLAKE2s (RFC 7693)

**Trusted** (as every file in `Spec/`). The BLAKE2 cryptographic hash
functions, transcribed from RFC 7693, *The BLAKE2 Cryptographic Hash and
Message Authentication Code (MAC)* (November 2015); section numbers below
refer to it. The RFC defines BLAKE2 once, for words of `w` bits, and
instantiates it as BLAKE2b (`w = 64`) and BLAKE2s (`w = 32`), which differ
only in the parameters of §2.1 and in the initialization vector (§2.6): so
does this file (`Params`, `b` and `s`). Every multi-byte quantity is
little-endian (§2.4). Keys and messages are sequences of bytes.

The primitives implemented in assembly are the compression function `F` over
a run of whole blocks (`compressBlocks`), and the streaming (incremental)
interface: initialize with the output length and a key, absorb message bytes,
and compress the last block and output the final state, on a streaming state
that `Repr` relates to the data (the padded key followed by the message)
absorbed so far. Their contracts are in `Spec/Blake2/Contract.lean`.
-/

namespace VG.Spec.Blake2

/-- The parameters of a BLAKE2 variant with words of `w` bits (§2.1), and its
initialization vector (§2.6). -/
structure Params (w : Nat) where
  /-- The number of rounds in `F`, `r`. -/
  r : Nat
  /-- The rotation constants of `G`, `(R1, R2, R3, R4)`. -/
  R1 : Nat
  R2 : Nat
  R3 : Nat
  R4 : Nat
  /-- The maximum hash size and key size in bytes (`nn` and `kk` are at most
  this, §2.1). -/
  maxBytes : Nat
  /-- The initialization vector `IV[0..7]`. -/
  IV : Vector (BitVec w) 8

/-- BLAKE2b: `w = 64`, `r = 12`, `(R1, R2, R3, R4) = (32, 24, 16, 63)`,
`1 ≤ nn ≤ 64`, `0 ≤ kk ≤ 64` (§2.1); its IV is that of Appendix C (the SHA-512
IV, §2.6). -/
def b : Params 64 where
  r := 12
  R1 := 32
  R2 := 24
  R3 := 16
  R4 := 63
  maxBytes := 64
  IV := #v[0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
    0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- BLAKE2s: `w = 32`, `r = 10`, `(R1, R2, R3, R4) = (16, 12, 8, 7)`,
`1 ≤ nn ≤ 32`, `0 ≤ kk ≤ 32` (§2.1); its IV is that of Appendix D (the SHA-256
IV, §2.6). -/
def s : Params 32 where
  r := 10
  R1 := 16
  R2 := 12
  R3 := 8
  R4 := 7
  maxBytes := 32
  IV := #v[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB,
    0x5BE0CD19]

/-- The block size in bytes, `bb`: sixteen words of `w / 8` bytes (§2.1: 128
for BLAKE2b, 64 for BLAKE2s). -/
def blockBytes (w : Nat) : Nat := 16 * (w / 8)

/-- The hash state `h[0..7]` (§2.2). -/
abbrev HashValue (w : Nat) := Vector (BitVec w) 8

/-- The local work vector `v[0..15]` of `F` (§3.2). -/
abbrev Work (w : Nat) := Vector (BitVec w) 16

/-- A message block `m[0..15]`: sixteen words (§2.2). -/
abbrev Block (w : Nat) := Fin 16 → BitVec w

/-! ## Words as bytes (§2.4) -/

/-- The `n`-byte little-endian integer whose bytes are `byte 0 … byte (n-1)`,
least significant first (as `Mem.read`). -/
def leBytes : (n : Nat) → (Nat → Byte) → BitVec (8 * n)
  | 0, _ => 0#0
  | n + 1, byte => (leBytes n (fun i => byte (i + 1)) ++ byte 0 : BitVec (8 * n + 8))

/-- The `w`-bit word whose little-endian bytes are `byte 0 … byte (w/8 - 1)`. -/
def leWord (w : Nat) (byte : Nat → Byte) : BitVec w := (leBytes (w / 8) byte).setWidth w

/-- The little-endian bytes of a word. -/
def wordBytes {w : Nat} (x : BitVec w) : List Byte :=
  (List.range (w / 8)).map fun i => x.extractLsb' (8 * i) 8

/-- The block whose `j`-th word is made of bytes `(w/8)·j … (w/8)·j + w/8 - 1`
of `byte`, least significant first. -/
def parseBlock {w : Nat} (byte : Nat → Byte) : Block w := fun j =>
  leWord w fun i => byte (w / 8 * j + i)

/-! ## The message schedule (§2.7) -/

/-- `SIGMA[0..9]`: the message word permutation of each round. Round `i` uses
`SIGMA[i mod 10]` (so rounds 10 and 11 of BLAKE2b use `SIGMA[0]` and
`SIGMA[1]`). -/
def sigma : List (List (Fin 16)) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- `SIGMA[i mod 10][j]`. -/
def sigmaAt (i : Nat) (j : Nat) : Fin 16 := (sigma.getD (i % 10) []).getD j 0

/-! ## The mixing function `G` (§3.1) -/

/-- `G(v[0..15], a, b, c, d, x, y)`: additions are modulo `2^w`, and `>>>` is
rotation to the right (§2.3). -/
def G {w : Nat} (P : Params w) (v : Work w) (a b c d : Fin 16) (x y : BitVec w) : Work w :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight P.R1)
  let v := v.set c (v[c] + v[d])
  let v := v.set b ((v[b] ^^^ v[c]).rotateRight P.R2)
  let v := v.set a (v[a] + v[b] + y)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight P.R3)
  let v := v.set c (v[c] + v[d])
  v.set b ((v[b] ^^^ v[c]).rotateRight P.R4)

/-! ## The compression function `F` (§3.2) -/

/-- Round `i` of `F`, on the message block `m`. -/
def round {w : Nat} (P : Params w) (m : Block w) (v : Work w) (i : Nat) : Work w :=
  let s := sigmaAt i
  let v := G P v 0 4 8 12 (m (s 0)) (m (s 1))
  let v := G P v 1 5 9 13 (m (s 2)) (m (s 3))
  let v := G P v 2 6 10 14 (m (s 4)) (m (s 5))
  let v := G P v 3 7 11 15 (m (s 6)) (m (s 7))
  let v := G P v 0 5 10 15 (m (s 8)) (m (s 9))
  let v := G P v 1 6 11 12 (m (s 10)) (m (s 11))
  let v := G P v 2 7 8 13 (m (s 12)) (m (s 13))
  G P v 3 4 9 14 (m (s 14)) (m (s 15))

/-- `F(h[0..7], m[0..15], t, f)`. The offset counter `t` is a `2w`-bit
integer: `t` here is taken modulo `2^(2w)`, its low word being `t mod 2^w`
and its high word `t >> w`. -/
def F {w : Nat} (P : Params w) (h : HashValue w) (m : Block w) (t : Nat) (f : Bool) :
    HashValue w :=
  -- Initialize the local work vector: first half from the state, second
  -- half from the IV.
  let v : Work w := h ++ P.IV
  -- The low and high words of the offset.
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat w t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat w (t / 2 ^ w))
  -- The last block flag: invert all bits.
  let v := if f then v.set 14 (v[14] ^^^ BitVec.allOnes w) else v
  -- Rounds `0 … r-1`.
  let v := (List.range P.r).foldl (round P m) v
  -- XOR the two halves.
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

/-! ## Padding data and computing a digest (§3.3) -/

/-- `x` padded with zero bytes to a multiple of the block size. -/
def padZeros (w : Nat) (x : List Byte) : List Byte :=
  x ++ List.replicate ((blockBytes w - x.length % blockBytes w) % blockBytes w) 0

/-- The padded key and data blocks `d[0..dd-1]`, as their `bb · dd` bytes:
the key padded with zeros to a block if `kk > 0` (`d[0]`), then the message
padded with zeros to a multiple of the block size; one all-zero block for an
unkeyed empty message. -/
def paddedData (w : Nat) (key m : List Byte) : List Byte :=
  let d := (if key.length > 0 then padZeros w key else []) ++ padZeros w m
  if d.length = 0 then List.replicate (blockBytes w) 0 else d

/-- The initial state: the IV, with the parameter block `p[0] = 0x0101kknn`
XORed into `h[0]` (§2.5, §3.3). -/
def init {w : Nat} (P : Params w) (nn kk : Nat) : HashValue w :=
  P.IV.set 0 (P.IV[0] ^^^ 0x01010000 ^^^ (BitVec.ofNat w kk <<< 8) ^^^ BitVec.ofNat w nn)

/-- `BLAKE2(d[0..dd-1], ll, kk, nn)` for the key `key` (`kk` bytes, `0 ≤ kk ≤
P.maxBytes`) and the message `m` (`ll` bytes): the first `nn` bytes of the
final state (`1 ≤ nn ≤ P.maxBytes`). -/
def blake2 {w : Nat} (P : Params w) (nn : Nat) (key m : List Byte) : List Byte :=
  let bb := blockBytes w
  let kk := key.length
  let ll := m.length
  let d := paddedData w key m
  let dd := d.length / bb
  let block (i : Nat) : Block w := parseBlock fun k => d.getD (bb * i + k) 0
  -- Process padded key and data blocks.
  let h := (List.range (dd - 1)).foldl (fun h i => F P h (block i) ((i + 1) * bb) false)
    (init P nn kk)
  -- Final block.
  let h := F P h (block (dd - 1)) (if kk = 0 then ll else ll + bb) true
  (h.toList.flatMap wordBytes).take nn

/-- BLAKE2b with an `nn`-byte digest and the key `key` (empty for unkeyed
hashing). -/
def blake2b (nn : Nat) (key m : List Byte) : List Byte := blake2 b nn key m

/-- BLAKE2s with an `nn`-byte digest and the key `key` (empty for unkeyed
hashing). -/
def blake2s (nn : Nat) (key m : List Byte) : List Byte := blake2 s nn key m

/-! ## Streaming

The streaming primitives hash the data `d` of §3.3 (the key padded to a block
if there is one, followed by the message) given in pieces. Unlike the
Merkle–Damgård hash functions, BLAKE2 compresses the last block differently
(with the final block flag, and the counter at the end of the data rather
than of the block), and a block is only known not to be the last when more
data follows it: so the streaming state keeps the last block, of 1 to `bb`
bytes, buffered, and has compressed every block before it.

The state is `8 · w/8 + bb` bytes (192 for BLAKE2b, 96 for BLAKE2s): the
hash state `h` (as `[u64; 8]` or `[u32; 8]`), followed by a `bb`-byte buffer.
As for the other hash functions, the length of the data is not part of the
state: the caller keeps it (in bytes, modulo 2⁶⁴) and passes it to every call.
(Lengths are public, so it may live anywhere.) The contracts are stated for
data of fewer than 2⁶⁴ bytes, which that count determines; BLAKE2s allows
fewer than 2⁶⁴ bytes in all, and BLAKE2b fewer than 2¹²⁸. -/

/-- The key as data: padded with zeros to a block if it is not empty (`d[0]`),
nothing otherwise. -/
def keyBlock (w : Nat) (key : List Byte) : List Byte :=
  if key.length = 0 then [] else padZeros w key

/-- How many blocks of the data `d` a streaming state has compressed: all but
the last, which holds 1 to `bb` bytes (none for empty data). -/
def compressed (w : Nat) (d : List Byte) : Nat := (d.length - 1) / blockBytes w

/-- `h` updated with the first `n` blocks of the data `d`, none of them the
last: block `i` is compressed with the offset counter `(i + 1) · bb`, the
offset at its end. -/
def compressList {w : Nat} (P : Params w) (h : HashValue w) (d : List Byte) (n : Nat) :
    HashValue w :=
  (List.range n).foldl
    (fun h i => F P h (parseBlock fun k => d.getD (blockBytes w * i + k) 0)
      ((i + 1) * blockBytes w) false) h

/-- The final state (all 8 words, as little-endian bytes) of hashing the data
`d` from the initial state `h0`: every block but the last compressed as by
`compressList`, then the last one (padded with zeros), with the offset counter
`|d|` and the final block flag. The BLAKE2 digest is its first `nn` bytes,
with `h0 = init P nn kk` and `d = keyBlock w key ++ m`. -/
def finalHash {w : Nat} (P : Params w) (h0 : HashValue w) (d : List Byte) : List Byte :=
  let n := compressed w d
  let h := compressList P h0 d n
  let h := F P h (parseBlock fun k => d.getD (blockBytes w * n + k) 0) d.length true
  h.toList.flatMap wordBytes

/-! ## The compression function on memory

These read the arguments of the assembly primitives from memory: a state is
stored as eight little-endian words, and message blocks are consecutive runs
of `bb` bytes. -/

/-- The state stored as `[u64; 8]` (BLAKE2b) or `[u32; 8]` (BLAKE2s) at `p`. -/
def stateAt (w : Nat) (m : Mem) (p : Addr) : HashValue w :=
  Vector.ofFn fun j => m.readW (p + BitVec.ofNat 64 (w / 8 * j)) w

/-- The block at `p`. -/
def blockAt (w : Nat) (m : Mem) (p : Addr) : Block w :=
  parseBlock fun k => m (p + BitVec.ofNat 64 k)

/-- `h` updated with the `n` consecutive blocks at `p`: block `i` is
compressed with the offset counter `t + i · bb`, and with the final block flag
if `f`. -/
def compressBlocks {w : Nat} (P : Params w) (h : HashValue w) (m : Mem) (p : Addr) (n t : Nat)
    (f : Bool) : HashValue w :=
  (List.range n).foldl
    (fun h i => F P h (blockAt w m (p + BitVec.ofNat 64 (blockBytes w * i)))
      (t + i * blockBytes w) f) h

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- The streaming state at `p` represents the data `d`, hashed from the initial
state `h0`: its hash state is `h0` updated with every block of `d` but the last
(`compressed w d` of them), and its buffer, `8 · w/8` bytes in, starts with the
remaining bytes of `d` (1 to `bb`, none for empty data). The rest of the
buffer is unspecified. -/
def Repr {w : Nat} (P : Params w) (h0 : HashValue w) (mem : Mem) (p : Addr) (d : List Byte) :
    Prop :=
  stateAt w mem p = compressList P h0 d (compressed w d) ∧
  bytesAt mem (p + BitVec.ofNat 64 (8 * (w / 8))) (d.length - blockBytes w * compressed w d) =
    d.drop (blockBytes w * compressed w d)

end VG.Spec.Blake2
