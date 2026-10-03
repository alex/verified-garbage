import VerifiedGarbage.Spec.X448
import VerifiedGarbage.Spec.Sha3

/-!
# Ed448 (RFC 8032)

**Trusted** (as every file in `Spec/`). Ed448, transcribed from RFC 8032,
*Edwards-Curve Digital Signature Algorithm (EdDSA)* (January 2017), §5.2,
with its context string: `dom4(0, C)` prefixes every hash of a message, the
flag being 0 since `PH(M) = M`. Ed448ph (flag 1, `PH = SHAKE256(·, 64)`) is
a separate algorithm and is not specified here. Byte strings are
little-endian.

The field and its exponentiation are those already specified for X448:
`Fin (2^448 - 2^224 - 1)`, with arithmetic modulo that prime. Points use
the projective coordinates and the addition formula of §5.2.4, which is
complete (`d` is not a square), so it is used for doubling too. This is a
mathematical specification; its branches on scalars are not an assembly
implementation or a claim about timing.

Verification checks the cofactored equation of §5.2.7,
`[4][S]B = [4]R + [4][k]A`, as the reference code of Appendix A does, with
`k = SHAKE256(dom4(0, C) || R || A || M, 114)` reduced modulo `L` as
Appendix A reduces it. The curve's group has order `4L`, so `[4]A` has
order dividing `L` and the reduction does not change the predicate; it is
part of the contract nonetheless, so that implementations need not rely on
the group's order. Encodings must be canonical, including the sign of a zero
x-coordinate, and `S < L`. There is no additional subgroup or small-order
rejection.
-/

namespace VG.Spec.Ed448

open X448 (Fe P pow)

/-- The prime-order subgroup's order `L` (§5.2, the table of parameters). -/
def L : Nat := 2 ^ 446 - 13818066809895115352007386748515426880336692474882178609894547503885

/-- The Edwards curve parameter `d = -39081` of `x^2 + y^2 = 1 + d x^2 y^2`
(§5.2). -/
def d : Fe := 0 - 39081

/-- A little-endian byte string interpreted as an unsigned integer (§5.2.2). -/
def decodeLE : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLE bs

/-- The low `n` bytes of an integer, in little-endian order (§5.2.2). -/
def encodeLE (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x >>> (8 * i))

/-- Projective coordinates: `x = X/Z`, `y = Y/Z` (§5.2.4). Only valid
points, with `Z ≠ 0`, are passed to group operations by the top-level
functions. -/
structure Point where
  X : Fe
  Y : Fe
  Z : Fe
  deriving DecidableEq

/-- The neutral point `(0, 1)` (§5.2.4). -/
def identity : Point := ⟨0, 1, 1⟩

/-- The base point `B` from the table of §5.2, with `Z = 1`. -/
def basePoint : Point :=
  ⟨224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710,
   298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660,
   1⟩

/-- The addition formula of §5.2.4, in its stated order. It is complete, so
it also doubles a point. -/
def pointAdd (p q : Point) : Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let dd := p.Y * q.Y
  let e := d * c * dd
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (q.X + q.Y)
  ⟨a * f * (h - c - dd), a * g * (dd - c), f * g⟩

/-- `[s]p`, by double-and-add. The scalar is not implicitly reduced modulo
`L`: a decoded point need not have order `L`. -/
def pointMul (s : Nat) (p : Point) : Point :=
  if s = 0 then identity else
  let q := pointMul (s / 2) (pointAdd p p)
  if s % 2 = 0 then q else pointAdd q p
termination_by s
decreasing_by omega

/-- Equality of affine coordinates, without an inversion. -/
def pointEqual (p q : Point) : Bool :=
  p.X * q.Z == q.X * p.Z && p.Y * q.Z == q.Y * p.Z

/-- Encode a valid point as 57 bytes: its y-coordinate, and the low bit of x
as bit 455 (§5.2.2). -/
def encodePoint (p : Point) : List Byte :=
  let zi := pow p.Z (P - 2)
  let x := p.X * zi
  let y := p.Y * zi
  encodeLE 57 (y.val + (x.val % 2) * 2 ^ 455)

/-- Recover x from a canonical y and the sign bit `x_0` (§5.2.3, steps 2–4):
the candidate root `x = u^3 v (u^5 v^3)^((p-3)/4)` of `u/v`, for
`u = y^2 - 1` and `v = d y^2 - 1`. -/
def recoverX (y : Fe) (sign : Bool) : Option Fe := do
  let u := y * y - 1
  let v := d * y * y - 1
  let x := u * u * u * v * pow (u * u * u * u * u * v * v * v) ((P - 3) / 4)
  if v * x * x ≠ u then none
  else if x = 0 && sign then none
  else some (if (x.val % 2 == 1) == sign then x else 0 - x)

/-- Decode exactly 57 bytes, rejecting y ≥ p (which includes any of bits
448–454 set), nonsquares and negative zero (§5.2.3). The y-coordinate is
checked before conversion to `Fe`. -/
def decodePoint (bs : List Byte) : Option Point := do
  if bs.length != 57 then none else do
    let n := decodeLE bs
    let y := n % 2 ^ 455
    if h : y < P then
      let x ← recoverX ⟨y, h⟩ (n / 2 ^ 455 == 1)
      pure ⟨x, ⟨y, h⟩, 1⟩
    else none

/-- `dom4(x, y) = "SigEd448" || octet(x) || octet(OLEN(y)) || y` (§2), for a
context `y` of at most 255 bytes. -/
def dom4 (x : Nat) (y : List Byte) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++
    [BitVec.ofNat 8 x, BitVec.ofNat 8 y.length] ++ y

/-- `H(dom4(0, C) || x)`, with `H(x) = SHAKE256(x, 114)` (§5.2). -/
def hash (context x : List Byte) : List Byte := Sha3.shake256 (dom4 0 context ++ x) 114

/-- Prune the first half of the 114-byte hash (§5.2.5, steps 2–3): clear
the two least significant bits of the first byte and all of the last (57th)
byte, and set the highest bit of the 56th. -/
def prune (h : List Byte) : Nat :=
  (decodeLE (h.take 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447

/-- The secret scalar and the second half of `SHAKE256(k, 114)`, the nonce
prefix, from a 57-byte private key `k` (§5.2.5, steps 1–3; §5.2.6, step 1).
This hash has no `dom4` prefix. -/
def expandSecret (seed : List Byte) : Nat × List Byte :=
  let h := Sha3.shake256 seed 114
  (prune h, h.drop 57)

/-- Reduce a little-endian integer modulo the subgroup order, as 57 bytes.
Used for 114-byte hashes (§5.2.6, steps 2 and 4–5). -/
def scalarReduce (wide : List Byte) : List Byte := encodeLE 57 (decodeLE wide % L)

/-- `(r + k*s) mod L`, as 57 bytes (§5.2.6, step 5). Inputs are unsigned
little-endian integers and need not be canonical scalars. -/
def scalarMulAdd (r k s : List Byte) : List Byte :=
  encodeLE 57 ((decodeLE r + decodeLE k * decodeLE s) % L)

/-- Encode `[s]B` for an unsigned little-endian scalar. This function does
not prune its input (§5.2.5, step 4; §5.2.6, step 3). -/
def scalarBase (s : List Byte) : List Byte := encodePoint (pointMul (decodeLE s) basePoint)

/-- The public key derived from a 57-byte private key (§5.2.5). -/
def publicKey (seed : List Byte) : List Byte :=
  encodePoint (pointMul (expandSecret seed).1 basePoint)

/-- Ed448 signing with a 57-byte private key and a context of at most 255
bytes (§5.2.6). There is no separately supplied public key that could
disagree with the private key. -/
def sign (seed context message : List Byte) : List Byte :=
  let (s, noncePrefix) := expandSecret seed
  let a := encodePoint (pointMul s basePoint)
  let r := decodeLE (hash context (noncePrefix ++ message)) % L
  let rr := encodePoint (pointMul r basePoint)
  let k := decodeLE (hash context (rr ++ a ++ message)) % L
  rr ++ encodeLE 57 ((r + k * s) % L)

/-- Verify canonical encodings and the cofactored equation of §5.2.7,
`[4][S]B = [4]R + [4][k]A`, using the challenge integer `k` supplied by the
caller as 57 little-endian bytes, as given. `verify` passes
`SHAKE256(dom4(0, C) || R || A || M, 114) mod L`. -/
def verifyEquation (pk signature challenge : List Byte) : Bool :=
  if pk.length != 57 || signature.length != 114 || challenge.length != 57 then false else
  match decodePoint pk, decodePoint (signature.take 57) with
  | some a, some r =>
    let s := decodeLE (signature.drop 57)
    s < L && pointEqual (pointMul 4 (pointMul s basePoint))
      (pointAdd (pointMul 4 r) (pointMul 4 (pointMul (decodeLE challenge) a)))
  | _, _ => false

/-- Ed448 verification (§5.2.7), including all encoding checks, with the
challenge `k = SHAKE256(dom4(0, C) || R || A || M, 114)` reduced modulo `L`.
A context longer than 255 bytes is not an Ed448 context, and nothing
verifies with it. -/
def verify (pk context message signature : List Byte) : Bool :=
  context.length ≤ 255 &&
    verifyEquation pk signature
      (scalarReduce (hash context (signature.take 57 ++ pk ++ message)))

end VG.Spec.Ed448
