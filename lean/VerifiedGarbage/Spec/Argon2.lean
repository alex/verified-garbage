import VerifiedGarbage.Spec.Blake2

/-!
# Argon2 version 1.3 (RFC 9106)

**Trusted** (as every file in `Spec/`). Argon2d, Argon2i and Argon2id,
transcribed from RFC 9106, *Argon2 Memory-Hard Function for Password Hashing
and Proof-of-Work Applications* (September 2021). Section numbers below
refer to that RFC. Words and length prefixes are little-endian; arithmetic
in `GB` is modulo 2⁶⁴. `Blake2.blake2b` supplies H, including its digest
length parameter (a shorter digest is not a truncated 64-byte digest).

`derive` is the whole algorithm: H₀, H′, initialization, every memory-filling
pass, the final lane XOR, and H′ of that block. Lanes are evaluated in
increasing order within each slice, one of the orders §3.2 permits. Worker
count is an execution parameter, not an input to the hash. `fill` also
records the reference indices of data-dependent steps, so the contracts
can permit exactly this inherent leakage for Argon2d/id without making
the password, secret, intermediate blocks or derived key public.
-/

namespace VG.Spec.Argon2

/-- The type numbers `y` of §3.1. -/
inductive Variant where
  | d | i | id
  deriving DecidableEq, BEq, Repr

def Variant.code : Variant → Nat
  | .d => 0
  | .i => 1
  | .id => 2

/-- The public algorithm parameters. `memory` is the requested KiB count,
which is hashed into H₀ before it is rounded down for allocation. -/
structure Params where
  variant : Variant
  passes : Nat
  memory : Nat
  lanes : Nat
  tagLen : Nat
  deriving Repr

/-- The actual number `m′` of 1024-byte blocks (§3.2, step 2). -/
def Params.blocks (p : Params) : Nat := 4 * p.lanes * (p.memory / (4 * p.lanes))

/-- Blocks per lane (`q`) and per segment (`q / 4`). -/
def Params.laneLen (p : Params) : Nat := p.blocks / p.lanes
def Params.segmentLen (p : Params) : Nat := p.laneLen / 4

/-- RFC 9106 §3.1 bounds. Salt length zero is allowed by the RFC (§3.2,
step 1); applications may impose a stronger salt policy. -/
def valid (p : Params) (passwordLen saltLen secretLen adLen : Nat) : Prop :=
  1 ≤ p.lanes ∧ p.lanes < 2 ^ 24 ∧
  1 ≤ p.passes ∧ p.passes < 2 ^ 32 ∧
  8 * p.lanes ≤ p.memory ∧ p.memory < 2 ^ 32 ∧
  4 ≤ p.tagLen ∧ p.tagLen < 2 ^ 32 ∧
  passwordLen < 2 ^ 32 ∧ saltLen < 2 ^ 32 ∧ secretLen < 2 ^ 32 ∧ adLen < 2 ^ 32

instance (p : Params) (a b c d : Nat) : Decidable (valid p a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev Word := BitVec 64
abbrev Block := Vector Word 128

/-- LE32, including the length prefixes in H₀ and H′. -/
def le32 (n : Nat) : List Byte := Blake2.wordBytes (BitVec.ofNat 32 n)

/-- A 1024-byte block as 128 little-endian words; zero outside the input. -/
def parseBlock (bs : List Byte) : Block :=
  Vector.ofFn fun j => Blake2.leWord 64 fun k => bs.getD (8 * j.val + k) 0

def serialize (b : Block) : List Byte := b.toList.flatMap Blake2.wordBytes

def zeroBlock : Block := Vector.replicate 128 0

def xorBlock (a b : Block) : Block := Vector.zipWith (· ^^^ ·) a b

/-! ## H and H′ (§3.3) -/

/-- Unkeyed BLAKE2b with its output length set to `n`. -/
def H (n : Nat) (input : List Byte) : List Byte := Blake2.blake2b n [] input

/-- Emit `r` 32-byte prefixes, starting with V₁ = `v`, followed by the
last digest of length `lastLen`. The recursive argument counts prefixes,
not hashes: the final hash consumes Vᵣ, not Vᵣ₊₁. -/
def longHash (lastLen : Nat) : Nat → List Byte → List Byte
  | 0, v => H lastLen v
  | 1, v => v.take 32 ++ H lastLen v
  | r + 2, v => v.take 32 ++ longHash lastLen (r + 1) (H 64 v)

/-- H′ with an `n`-byte output (§3.3), for `1 ≤ n < 2³²`. -/
def hPrime (n : Nat) (input : List Byte) : List Byte :=
  let input := le32 n ++ input
  if n ≤ 64 then H n input else
    let r := (n + 31) / 32 - 2
    longHash (n - 32 * r) r (H 64 input)

/-- H₀ (§3.2, step 1). The version byte is 0x13, encoded as LE32. -/
def initialHash (p : Params) (password salt secret ad : List Byte) : List Byte :=
  H 64 (le32 p.lanes ++ le32 p.tagLen ++ le32 p.memory ++ le32 p.passes ++
    le32 0x13 ++ le32 p.variant.code ++
    le32 password.length ++ password ++ le32 salt.length ++ salt ++
    le32 secret.length ++ secret ++ le32 ad.length ++ ad)

/-! ## Compression G and permutation P (§3.5–3.6) -/

/-- `a + b + 2 · trunc(a) · trunc(b)` modulo 2⁶⁴ (§3.6). -/
def addMul (a b : Word) : Word :=
  a + b + 2 * (a &&& 0xffffffff) * (b &&& 0xffffffff)

/-- GB on the four selected words (§3.6, Figure 19). -/
def GB (v : Vector Word 16) (a b c d : Fin 16) : Vector Word 16 :=
  let v := v.set a (addMul v[a] v[b])
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight 32)
  let v := v.set c (addMul v[c] v[d])
  let v := v.set b ((v[b] ^^^ v[c]).rotateRight 24)
  let v := v.set a (addMul v[a] v[b])
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight 16)
  let v := v.set c (addMul v[c] v[d])
  v.set b ((v[b] ^^^ v[c]).rotateRight 63)

/-- P: four column GBs followed by four diagonal GBs (Figure 18). -/
def permute (v : Vector Word 16) : Vector Word 16 :=
  let v := GB v 0 4 8 12
  let v := GB v 1 5 9 13
  let v := GB v 2 6 10 14
  let v := GB v 3 7 11 15
  let v := GB v 0 5 10 15
  let v := GB v 1 6 11 12
  let v := GB v 2 7 8 13
  GB v 3 4 9 14

/-- A word in row `r` of the 8×8 matrix of 128-bit registers. -/
def rowIndex (r : Fin 8) (j : Fin 16) : Fin 128 := ⟨16 * r.val + j.val, by omega⟩

/-- A word in column `c`. Each matrix element is two consecutive words. -/
def colIndex (c : Fin 8) (j : Fin 16) : Fin 128 :=
  ⟨16 * (j.val / 2) + 2 * c.val + j.val % 2, by omega⟩

/-- Apply P to the sixteen words selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) (b : Block) : Block :=
  let v := permute (Vector.ofFn fun j => b[index j])
  (List.finRange 16).foldl (fun b j => b.set (index j) v[j]) b

/-- G(X,Y): XOR, P on each row, P on each column, XOR the original
X XOR Y back in (§3.5). -/
def compress (x y : Block) : Block :=
  let r := xorBlock x y
  let q := (List.finRange 8).foldl (fun b i => permuteAt (rowIndex i) b) r
  let z := (List.finRange 8).foldl (fun b i => permuteAt (colIndex i) b) q
  xorBlock z r

/-! ## Reference blocks (§3.4) -/

/-- Whether a segment uses Argon2i addressing. -/
def independent (p : Params) (pass slice : Nat) : Bool :=
  p.variant == .i || (p.variant == .id && pass == 0 && slice < 2)

/-- The address block of §3.4.1.2. Counter `counter` starts at one;
each block supplies 128 pairs J₁,J₂. -/
def addressBlock (p : Params) (pass lane slice counter : Nat) : Block :=
  let input := zeroBlock |>.set 0 (BitVec.ofNat 64 pass)
    |>.set 1 (BitVec.ofNat 64 lane) |>.set 2 (BitVec.ofNat 64 slice)
    |>.set 3 (BitVec.ofNat 64 p.blocks) |>.set 4 (BitVec.ofNat 64 p.passes)
    |>.set 5 (BitVec.ofNat 64 p.variant.code) |>.set 6 (BitVec.ofNat 64 counter)
  compress zeroBlock (compress zeroBlock input)

/-- The number of eligible reference blocks W (§3.4.2). `index` is the
offset within the current segment. On later passes W spans the preceding
three segments, wrapping around the lane, and (for the same lane) the
already-computed part of this segment. The immediate predecessor is
excluded. A cross-lane reference also excludes the last completed block
when `index = 0`. -/
def referenceCount (p : Params) (pass slice index : Nat) (sameLane : Bool) : Nat :=
  if pass = 0 then
    if sameLane then slice * p.segmentLen + index - 1
    else slice * p.segmentLen - (if index = 0 then 1 else 0)
  else if sameLane then p.laneLen - p.segmentLen + index - 1
  else p.laneLen - p.segmentLen - (if index = 0 then 1 else 0)

/-- Map J₁ (low half of `random`) and J₂ (high half) to the lane and
column of the reference block (§3.4.2). W is ordered chronologically:
from column zero in pass zero, otherwise from the next slice, wrapping. -/
def reference (p : Params) (pass lane slice index : Nat) (random : Word) : Nat × Nat :=
  let refLane := if pass = 0 ∧ slice = 0 then lane else (random >>> 32).toNat % p.lanes
  let count := referenceCount p pass slice index (refLane == lane)
  let j1 := (random &&& 0xffffffff).toNat
  let x := j1 * j1 / 2 ^ 32
  let relative := count - 1 - count * x / 2 ^ 32
  let start := if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen
  (refLane, (start + relative) % p.laneLen)

/-! ## Initialization, passes and finalization (§3.2) -/

/-- The memory matrix in lane-major order, and the reversed list of
data-dependent references made so far. Independent addresses need no
leakage allowance: they are determined entirely by public parameters. -/
structure FillState where
  memory : Array Block
  indices : List (Nat × Nat) := []

/-- B[i][0] and B[i][1] (§3.2, steps 3–4). Other cells start at zero;
the first pass overwrites them before any permitted reference reads them. -/
def initMemory (p : Params) (h0 : List Byte) : FillState :=
  let memory := (List.range p.blocks).toArray.map fun k =>
    if k % p.laneLen < 2 then
      parseBlock (hPrime 1024 (h0 ++ le32 (k % p.laneLen) ++ le32 (k / p.laneLen)))
    else zeroBlock
  ⟨memory, []⟩

/-- One block of a pass. Pass zero skips the first two initialized blocks
in each lane; later passes XOR the previous contents of the destination
with G (§3.2, steps 5–6). -/
def fillBlock (p : Params) (pass slice lane index : Nat) (s : FillState) : FillState :=
  if pass = 0 ∧ slice = 0 ∧ index < 2 then s else
    let column := slice * p.segmentLen + index
    let current := lane * p.laneLen + column
    let prev := s.memory[lane * p.laneLen + (column + p.laneLen - 1) % p.laneLen]?.getD zeroBlock
    let ind := independent p pass slice
    let random := if ind then
        (addressBlock p pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide))
      else prev[0]
    let ref := reference p pass lane slice index random
    let other := s.memory[ref.1 * p.laneLen + ref.2]?.getD zeroBlock
    let next := compress prev other
    let next := if pass = 0 then next else xorBlock next (s.memory[current]?.getD zeroBlock)
    { memory := s.memory.set! current next,
      indices := if ind then s.indices else ref :: s.indices }

/-- One complete pass, slice first, then lane, then offset (§3.2). -/
def fillPass (p : Params) (s : FillState) (pass : Nat) : FillState :=
  (List.range 4).foldl (fun s slice =>
    (List.range p.lanes).foldl (fun s lane =>
      (List.range p.segmentLen).foldl (fun s index => fillBlock p pass slice lane index s) s) s) s

/-- Initialization and all passes. -/
def fill (p : Params) (password salt secret ad : List Byte) : FillState :=
  (List.range p.passes).foldl (fillPass p) (initMemory p (initialHash p password salt secret ad))

/-- XOR the last block of every lane, then H′ to the tag length (§3.2,
steps 7–8). -/
def finish (p : Params) (memory : Array Block) : List Byte :=
  let last := (List.range p.lanes).foldl (fun b lane =>
    xorBlock b (memory[(lane + 1) * p.laneLen - 1]?.getD zeroBlock)) zeroBlock
  hPrime p.tagLen (serialize last)

/-- The complete Argon2 v1.3 derivation, for valid parameters. -/
def derive (p : Params) (password salt secret ad : List Byte) : List Byte :=
  finish p (fill p password salt secret ad).memory

/-- The sequence of data-dependent reference block indices permitted to
leak, in execution order and flattened as `lane * q + column`; empty for
Argon2i. -/
def references (p : Params) (password salt secret ad : List Byte) : List Nat :=
  (fill p password salt secret ad).indices.reverse.map fun (lane, column) => lane * p.laneLen + column

end VG.Spec.Argon2
