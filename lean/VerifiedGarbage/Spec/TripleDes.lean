import VerifiedGarbage.TCB.Mem

/-!
# Triple DES and ECB

**Trusted.** DES's permutations, S-boxes, Feistel rounds and key schedule
are transcribed from FIPS 46-3, pp. 10–21 and Appendix 1:
https://csrc.nist.gov/files/pubs/fips/46-3/final/docs/fips46-3.pdf.
TDEA uses E(K3, D(K2, E(K1, input))) and its inverse (pp. 15–16).
ECB applies this independently to each block (SP 800-38A §6.1).

The API accepts 24-byte keys (K1 || K2 || K3), or 16-byte keys
(K1 || K2, with K3 = K1). PC-1 discards each byte's parity bit;
parity is neither checked nor changed. Weak and repeated component keys
are accepted: this specifies the cipher, not a key-generation policy.

Issue #1's streaming interface buffers partial blocks, emits complete
8-byte blocks, and rejects a partial block at finalization. There is no
padding. All key bytes, round keys and data are secret in the contracts;
S-box indexing here does not permit secret-dependent memory access in an
implementation.
-/

namespace VG.Spec.TripleDes

abbrev Block := Vector Byte 8
abbrev DesSchedule := Vector (BitVec 48) 16
/-- Three encryption-order DES schedules. Each 48-bit key is zero-extended
into a 64-bit slot; the memory representation is little-endian. -/
abbrev Schedule := Vector (BitVec 64) 48

def ip : Vector Nat 64 := #v[
  58, 50, 42, 34, 26, 18, 10, 2,
  60, 52, 44, 36, 28, 20, 12, 4,
  62, 54, 46, 38, 30, 22, 14, 6,
  64, 56, 48, 40, 32, 24, 16, 8,
  57, 49, 41, 33, 25, 17, 9, 1,
  59, 51, 43, 35, 27, 19, 11, 3,
  61, 53, 45, 37, 29, 21, 13, 5,
  63, 55, 47, 39, 31, 23, 15, 7]

def fp : Vector Nat 64 := #v[
  40, 8, 48, 16, 56, 24, 64, 32,
  39, 7, 47, 15, 55, 23, 63, 31,
  38, 6, 46, 14, 54, 22, 62, 30,
  37, 5, 45, 13, 53, 21, 61, 29,
  36, 4, 44, 12, 52, 20, 60, 28,
  35, 3, 43, 11, 51, 19, 59, 27,
  34, 2, 42, 10, 50, 18, 58, 26,
  33, 1, 41, 9, 49, 17, 57, 25]

def expansion : Vector Nat 48 := #v[
  32, 1, 2, 3, 4, 5,
  4, 5, 6, 7, 8, 9,
  8, 9, 10, 11, 12, 13,
  12, 13, 14, 15, 16, 17,
  16, 17, 18, 19, 20, 21,
  20, 21, 22, 23, 24, 25,
  24, 25, 26, 27, 28, 29,
  28, 29, 30, 31, 32, 1]

def p : Vector Nat 32 := #v[
  16, 7, 20, 21,
  29, 12, 28, 17,
  1, 15, 23, 26,
  5, 18, 31, 10,
  2, 8, 24, 14,
  32, 27, 3, 9,
  19, 13, 30, 6,
  22, 11, 4, 25]

def pc1 : Vector Nat 56 := #v[
  57, 49, 41, 33, 25, 17, 9,
  1, 58, 50, 42, 34, 26, 18,
  10, 2, 59, 51, 43, 35, 27,
  19, 11, 3, 60, 52, 44, 36,
  63, 55, 47, 39, 31, 23, 15,
  7, 62, 54, 46, 38, 30, 22,
  14, 6, 61, 53, 45, 37, 29,
  21, 13, 5, 28, 20, 12, 4]

def pc2 : Vector Nat 48 := #v[
  14, 17, 11, 24, 1, 5,
  3, 28, 15, 6, 21, 10,
  23, 19, 12, 4, 26, 8,
  16, 7, 27, 20, 13, 2,
  41, 52, 31, 37, 47, 55,
  30, 40, 51, 45, 33, 48,
  44, 49, 39, 56, 34, 53,
  46, 42, 50, 36, 29, 32]

/-- FIPS bit positions are one-based, most significant bit first. -/
def permute {n m : Nat} (positions : Vector Nat m) (x : BitVec n) : BitVec m :=
  (List.range m).foldl (fun out i =>
    (out <<< 1) ||| (((x >>> (n - positions.getD i 1)) &&& 1).setWidth m)) 0

/-- Appendix 1: four rows of sixteen entries per S-box, in printed order. -/
def sBoxes : Vector (Vector (BitVec 4) 64) 8 := #v[
  #v[
    14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7,
    0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8,
    4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0,
    15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13],
  #v[
    15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10,
    3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5,
    0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15,
    13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9],
  #v[
    10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8,
    13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1,
    13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7,
    1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12],
  #v[
    7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15,
    13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9,
    10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4,
    3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14],
  #v[
    2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9,
    14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6,
    4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14,
    11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3],
  #v[
    12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11,
    10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8,
    9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6,
    4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13],
  #v[
    4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1,
    13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6,
    1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2,
    6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12],
  #v[
    13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7,
    1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2,
    7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8,
    2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11]]

def sBox (i : Nat) (x : BitVec 6) : BitVec 4 :=
  let row := 2 * ((x >>> 5).toNat) + (x &&& 1).toNat
  let col := ((x >>> 1) &&& 15).toNat
  (sBoxes.getD i (Vector.replicate 64 0)).getD (16 * row + col) 0

def roundFunction (r : BitVec 32) (k : BitVec 48) : BitVec 32 :=
  let x := permute expansion r ^^^ k
  let substituted : BitVec 32 := (List.range 8).foldl (fun out i =>
    (out <<< 4) ||| (sBox i ((x >>> (6 * (7 - i))).setWidth 6)).zeroExtend 32) 0
  permute p substituted

def rotations : Vector Nat 16 := #v[1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1]

def expandDesKey (key : BitVec 64) : DesSchedule := Id.run do
  let selected := permute pc1 key
  let mut c := (selected >>> 28).setWidth 28
  let mut d := selected.setWidth 28
  let mut keys : DesSchedule := Vector.replicate 16 0
  for j in List.range 16 do
    c := c.rotateLeft (rotations.getD j 0)
    d := d.rotateLeft (rotations.getD j 0)
    keys := keys.set! j (permute pc2 (c ++ d))
  return keys

/-- External blocks and component keys are big-endian. -/
def decodeBlock (b : Block) : BitVec 64 :=
  b.toList.foldl (fun out byte => (out <<< 8) ||| byte.zeroExtend 64) 0

def encodeBlock (x : BitVec 64) : Block :=
  Vector.ofFn fun i => (x >>> (8 * (7 - i.val))).setWidth 8

def validKey (n : Nat) : Prop := n = 16 ∨ n = 24

instance (n : Nat) : Decidable (validKey n) :=
  inferInstanceAs (Decidable (n = 16 ∨ n = 24))

/-- For 16-byte keys the third component repeats the first. Defined on
all lists; initialization and the expansion contract require a valid length. -/
def expandKey (key : List Byte) : Schedule :=
  let component (i : Nat) :=
    let offset := if i = 2 ∧ key.length = 16 then 0 else 8 * i
    expandDesKey (decodeBlock (Vector.ofFn fun j => key.getD (offset + j.val) 0))
  let first := component 0
  let second := component 1
  let third := component 2
  Vector.ofFn fun i =>
    ((if i.val < 16 then first else if i.val < 32 then second else third).getD
      (i.val % 16) 0).zeroExtend 64

inductive Direction | encrypt | decrypt
  deriving DecidableEq, Repr

/-- DES: initial permutation, sixteen Feistel rounds, final swap, IP⁻¹.
Decryption changes only the order of the round keys. -/
def des (keys : DesSchedule) (direction : Direction) (input : BitVec 64) : BitVec 64 :=
  let initial := permute ip input
  let (l, r) := (List.range 16).foldl (fun (l, r) j =>
    let k := keys.getD (if direction = .encrypt then j else 15 - j) 0
    (r, l ^^^ roundFunction r k)) ((initial >>> 32).setWidth 32, initial.setWidth 32)
  permute fp (r ++ l)

def componentSchedule (k : Schedule) (i : Nat) : DesSchedule :=
  Vector.ofFn fun j => (k.getD (16 * i + j.val) 0).setWidth 48

def encryptBlock (k : Schedule) (b : Block) : Block :=
  encodeBlock (des (componentSchedule k 2) .encrypt
    (des (componentSchedule k 1) .decrypt (des (componentSchedule k 0) .encrypt (decodeBlock b))))

def decryptBlock (k : Schedule) (b : Block) : Block :=
  encodeBlock (des (componentSchedule k 0) .decrypt
    (des (componentSchedule k 1) .encrypt (des (componentSchedule k 2) .decrypt (decodeBlock b))))

/-- SP 800-38A §6.1, including empty input. -/
def ecb (k : Schedule) (direction : Direction) (input : List Block) : List Block :=
  input.map (match direction with | .encrypt => encryptBlock k | .decrypt => decryptBlock k)

def blocks (data : List Byte) : List Block :=
  (List.range (data.length / 8)).map fun j =>
    Vector.ofFn fun i => data.getD (8 * j + i.val) 0

structure Context where
  schedule : Schedule
  direction : Direction
  pending : List Byte := []

inductive Error | invalidKeyLength | incompleteBlock
  deriving DecidableEq, Repr

def init (key : List Byte) (direction : Direction) : Except Error Context := do
  unless validKey key.length do throw .invalidKeyLength
  return { schedule := expandKey key, direction }

def update (ctx : Context) (data : List Byte) : Context × List Byte :=
  let input := ctx.pending ++ data
  ({ ctx with pending := input.drop (8 * (input.length / 8)) },
    (ecb ctx.schedule ctx.direction (blocks input)).flatMap Vector.toList)

def finalize (ctx : Context) : Except Error (List Byte) :=
  if ctx.pending.isEmpty then .ok [] else .error .incompleteBlock

/-! ## Memory layouts for contracts -/

def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

def blockAt (m : Mem) (p : Addr) : Block :=
  Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)

/-- 384 bytes: 48 little-endian 64-bit slots. Expansion writes zero in
bits 48–63; the block functions ignore those bits for arbitrary schedules. -/
def scheduleAt (m : Mem) (p : Addr) : Schedule :=
  Vector.ofFn fun i =>
    (List.range 8).foldl (fun out j =>
      out ||| ((m (p + BitVec.ofNat 64 (8 * i.val + j))).zeroExtend 64 <<< (8 * j))) 0

def blocksAt (m : Mem) (p : Addr) (n : Nat) : List Block :=
  (List.range n).map fun i => blockAt m (p + BitVec.ofNat 64 (8 * i))

end VG.Spec.TripleDes
