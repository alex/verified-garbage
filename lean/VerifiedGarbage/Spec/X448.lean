import VerifiedGarbage.TCB.Mem

/-!
# X448 (RFC 7748)

**Trusted** (as every file in `Spec/`). The Diffie-Hellman function X448,
transcribed from RFC 7748, *Elliptic Curves for Security* (January 2016),
§4.2, §5 and §6.2. Byte strings are little-endian. The structure follows
`Spec/X25519.lean`, with the field, decoding and ladder parameters of X448.

All field operations are in `Fin P`, modulo `P = 2⁴⁴⁸ - 2²²⁴ - 1`.
Inputs to `x448` are 56-byte strings, as enforced by its memory contract in
`Spec/X448/Contract.lean`. Every input bit of the u-coordinate is used;
noncanonical coordinates are reduced modulo `P`.
-/

namespace VG.Spec.X448

/-- The prime `p = 2⁴⁴⁸ - 2²²⁴ - 1` (§4.2). -/
def P : Nat := 2 ^ 448 - 2 ^ 224 - 1

instance : NeZero P := ⟨by decide +kernel⟩

/-- An element of `GF(p)`. -/
abbrev Fe := Fin P

/-- `a24 = (156326 - 2) / 4 = 39081` for curve448 (§5). -/
def a24 : Fe := 39081

/-- Exponentiation in `GF(p)` by square-and-multiply; `a ^ 0 = 1`. -/
def pow (a : Fe) (e : Nat) : Fe :=
  if e = 0 then 1 else
  let r := pow (a * a) (e / 2)
  if e % 2 = 0 then r else a * r
termination_by e
decreasing_by omega

/-- `decodeLittleEndian(b, 448)`: the first 56 bytes read as an unsigned
little-endian integer (§5). -/
def decodeLittleEndian (b : List Byte) : Nat :=
  ((List.range 56).map fun i => (b.getD i 0).toNat <<< (8 * i)).sum

/-- `decodeUCoordinate(u, 448)` (§5). All 448 bits are used, including the
most significant bit of the last byte. Reduction modulo `P` happens in
`x448`, so every 56-byte encoding is accepted. -/
def decodeUCoordinate (u : List Byte) : Nat := decodeLittleEndian u

/-- `encodeUCoordinate(u, 448)` (§5): the canonical representative in
`[0, P)` encoded as 56 bytes in little-endian order. -/
def encodeUCoordinate (u : Fe) : List Byte :=
  (List.range 56).map fun i => BitVec.ofNat 8 (u.val >>> (8 * i))

/-- `decodeScalar448(k)` (§5): clear the two least significant bits and
set bit 447, then read the 56 bytes as a little-endian integer. -/
def decodeScalar448 (k : List Byte) : Nat :=
  let k := k.set 0 (k.getD 0 0 &&& 252)
  let k := k.set 55 (k.getD 55 0 ||| 128)
  decodeLittleEndian k

/-- `cswap(swap, a, b)` of §5. -/
def cswap (swap : Nat) (a b : Fe) : Fe × Fe := if swap = 1 then (b, a) else (a, b)

/-- The Montgomery ladder's variables between iterations (§5). -/
structure Ladder where
  x2 : Fe
  z2 : Fe
  x3 : Fe
  z3 : Fe
  swap : Nat

/-- One iteration of the loop of §5, for bit `t` of the decoded scalar
`k`, with `x_1 = x1`. Names follow the RFC's pseudocode. -/
def ladderStep (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) : Ladder :=
  let kt := (k >>> t) &&& 1
  let swap := st.swap ^^^ kt
  let (x2, x3) := cswap swap st.x2 st.x3
  let (z2, z3) := cswap swap st.z2 st.z3
  let swap := kt
  let A := x2 + z2
  let AA := A * A
  let B := x2 - z2
  let BB := B * B
  let E := AA - BB
  let C := x3 + z3
  let D := x3 - z3
  let DA := D * A
  let CB := C * B
  let x3 := (DA + CB) * (DA + CB)
  let z3 := x1 * ((DA - CB) * (DA - CB))
  let x2 := AA * BB
  let z2 := E * (AA + a24 * E)
  { x2, z2, x3, z3, swap }

/-- `X448(k, u)` (§5), for a 56-byte scalar and u-coordinate: decode,
run the Montgomery ladder from bit 447 down to bit 0, do the final swap,
and encode `x2 * z2^(P - 2)`. The result may be all zero; the protocol
caller decides whether to reject that result (§6.2). -/
def x448 (k u : List Byte) : List Byte :=
  let k := decodeScalar448 k
  let u : Fe := Fin.ofNat P (decodeUCoordinate u)
  let st := (List.range 448).reverse.foldl (ladderStep k u)
    { x2 := 1, z2 := 0, x3 := u, z3 := 1, swap := 0 }
  let (x2, _) := cswap st.swap st.x2 st.x3
  let (z2, _) := cswap st.swap st.z2 st.z3
  encodeUCoordinate (x2 * pow z2 (P - 2))

/-- The base point's u-coordinate, 5 (§4.2), encoded as the byte 5
followed by 55 zero bytes (§6.2). -/
def basePoint : List Byte := 5 :: List.replicate 55 0

end VG.Spec.X448
