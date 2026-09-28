/-!
# AArch64 AdvSIMD values and the cryptographic functions of the Arm ARM

**Trusted.** Helpers for the semantics of the AdvSIMD and cryptographic
instructions in `TCB/AArch64/Isa.lean`: the lanes of a 128-bit vector
register, and the shared pseudocode functions that the Arm Architecture
Reference Manual for A-profile (DDI 0487) uses in the descriptions of the
cryptographic instructions (chapter J1, "shared/functions/crypto").

Lanes are numbered from the least significant, as the pseudocode's
`Elem[vector, e, size]` does: lane `e` of size `size` is bits
`(e+1)*size-1 : e*size`. On a little-endian machine, lane `e` of a register
loaded by `LDR (immediate, SIMD&FP)` holds the `e`-th `size`-bit value in
memory.
-/

namespace VG.AArch64

/-- `Elem[x, e, 8]`: byte `e` of `x`. -/
def vbyte (x : BitVec 128) (e : Nat) : BitVec 8 := x.extractLsb' (8 * e) 8

/-- `Elem[x, e, 32]`: word `e` of `x`. -/
def vword (x : BitVec 128) (e : Nat) : BitVec 32 := x.extractLsb' (32 * e) 32

/-- `Elem[x, e, 64]`: doubleword `e` of `x`. -/
def vdword (x : BitVec 128) (e : Nat) : BitVec 64 := x.extractLsb' (64 * e) 64

/-- The vector whose byte `e` is `f e`. -/
def ofVBytes (f : Nat → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++
    f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-- The vector whose words are `w0` (bits 31:0), `w1`, `w2`, `w3` (bits 127:96). -/
def ofVWords (w0 w1 w2 w3 : BitVec 32) : BitVec 128 := w3 ++ w2 ++ w1 ++ w0

/-- The vector whose doublewords are `d0` (bits 63:0) and `d1` (bits 127:64). -/
def ofVDwords (d0 d1 : BitVec 64) : BitVec 128 := d1 ++ d0

/-! ## SHA (DDI 0487, J1, "shared/functions/crypto") -/

/-- `SHAchoose(x, y, z) = ((y EOR z) AND x) EOR z`. -/
def shaChoose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z

/-- `SHAmajority(x, y, z) = ((x AND y) OR ((x OR y) AND z))`. -/
def shaMajority (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)

/-- `SHAparity(x, y, z) = (x EOR y EOR z)`. -/
def shaParity (x y z : BitVec 32) : BitVec 32 := x ^^^ y ^^^ z

/-- `SHAhashSIGMA0(x) = ROR(x, 2) EOR ROR(x, 13) EOR ROR(x, 22)`. -/
def shaHashSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `SHAhashSIGMA1(x) = ROR(x, 6) EOR ROR(x, 11) EOR ROR(x, 25)`. -/
def shaHashSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- One iteration of the loops of SHA1C, SHA1P and SHA1M, with the function
`f` (`SHAchoose`, `SHAparity` or `SHAmajority`), on `(Y, X)`:
`t = f(X<63:32>, X<95:64>, X<127:96>); Y = Y + ROL(X<31:0>, 5) + t +
Elem[W, e, 32]; X<63:32> = ROL(X<63:32>, 30); <Y, X> = ROL(Y:X, 32)`.
The 160-bit rotation leaves `X<127:96>` in `Y` and `X<95:0>:Y` in `X`. -/
def sha1Step (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (w : BitVec 32)
    (yx : BitVec 32 × BitVec 128) : BitVec 32 × BitVec 128 :=
  let (y, x) := yx
  let t := f (vword x 1) (vword x 2) (vword x 3)
  let y := y + (vword x 0).rotateLeft 5 + t + w
  let x := ofVWords (vword x 0) ((vword x 1).rotateLeft 30) (vword x 2) (vword x 3)
  (vword x 3, ofVWords y (vword x 0) (vword x 1) (vword x 2))

/-- SHA1C, SHA1P, SHA1M: `X = V[d]; Y = V[n]<31:0>; W = V[m]`, then the loop
`for e = 0 to 3` of `sha1Step`, and `V[d] = X`. -/
def sha1Hash (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (x : BitVec 128)
    (y : BitVec 32) (w : BitVec 128) : BitVec 128 :=
  (sha1Step f (vword w 3) (sha1Step f (vword w 2) (sha1Step f (vword w 1)
    (sha1Step f (vword w 0) (y, x))))).2

/-- SHA1SU0: `result = operand2<63:0> : operand1<127:64>; result = result
EOR operand1 EOR operand3`, where `operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`. -/
def sha1Su0 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  ofVDwords (vdword op1 1) (vdword op2 0) ^^^ op1 ^^^ op3

/-- SHA1SU1: `T = X EOR LSR(Y, 32); W0 = ROL(T<31:0>, 1); W1 = ROL(T<63:32>,
1); W2 = ROL(T<95:64>, 1); W3 = ROL(T<127:96>, 1) EOR ROL(T<31:0>, 2);
V[d] = W3:W2:W1:W0`, where `X = V[d]`, `Y = V[n]`. -/
def sha1Su1 (x y : BitVec 128) : BitVec 128 :=
  let t := x ^^^ (y >>> 32)
  ofVWords ((vword t 0).rotateLeft 1) ((vword t 1).rotateLeft 1) ((vword t 2).rotateLeft 1)
    ((vword t 3).rotateLeft 1 ^^^ (vword t 0).rotateLeft 2)

/-- One iteration of the loop of `SHA256hash(X, Y, W, part1)`:
`chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>); maj = SHAmajority(X<31:0>,
X<63:32>, X<95:64>); t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs +
Elem[W, e, 32]; X<127:96> = t + X<127:96>; Y<127:96> = t +
SHAhashSIGMA0(X<31:0>) + maj; <Y, X> = ROL(Y : X, 32)`. The 256-bit
rotation leaves `Y<95:0>:X<127:96>` in `Y` and `X<95:0>:Y<127:96>` in `X`. -/
def sha256Step (w : BitVec 32) (xy : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let (x, y) := xy
  let chs := shaChoose (vword y 0) (vword y 1) (vword y 2)
  let maj := shaMajority (vword x 0) (vword x 1) (vword x 2)
  let t := vword y 3 + shaHashSigma1 (vword y 0) + chs + w
  let x3 := t + vword x 3
  let y3 := t + shaHashSigma0 (vword x 0) + maj
  (ofVWords y3 (vword x 0) (vword x 1) (vword x 2),
    ofVWords x3 (vword y 0) (vword y 1) (vword y 2))

/-- `SHA256hash(X, Y, W, part1)`: the loop `for e = 0 to 3` of `sha256Step`,
then `X` if `part1`, else `Y`. -/
def sha256Hash (x y w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let r := sha256Step (vword w 3) (sha256Step (vword w 2) (sha256Step (vword w 1)
    (sha256Step (vword w 0) (x, y))))
  if part1 then r.1 else r.2

/-- SHA256SU0: `T = operand2<31:0> : operand1<127:32>`; for `e = 0 to 3`:
`elt = Elem[T, e, 32]; elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
Elem[result, e, 32] = elt + Elem[operand1, e, 32]`, where `operand1 =
V[d]`, `operand2 = V[n]`. -/
def sha256Su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let t := ofVWords (vword op1 1) (vword op1 2) (vword op1 3) (vword op2 0)
  let f (e : Nat) : BitVec 32 :=
    let elt := vword t e
    (elt.rotateRight 7 ^^^ elt.rotateRight 18 ^^^ elt >>> 3) + vword op1 e
  ofVWords (f 0) (f 1) (f 2) (f 3)

/-- SHA256SU1: `T0 = operand3<31:0> : operand2<127:32>; T1 = operand3<127:64>`;
for `e = 0 to 1`: `elt = Elem[T1, e, 32]; elt = ROR(elt, 17) EOR ROR(elt, 19)
EOR LSR(elt, 10); elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
Elem[result, e, 32] = elt`; then `T1 = result<63:0>` and for `e = 2 to 3`
the same with `Elem[T1, e-2, 32]`. `operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`. -/
def sha256Su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let t0 := ofVWords (vword op2 1) (vword op2 2) (vword op2 3) (vword op3 0)
  let sig (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10
  let r0 := sig (vword op3 2) + vword op1 0 + vword t0 0
  let r1 := sig (vword op3 3) + vword op1 1 + vword t0 1
  let r2 := sig r0 + vword op1 2 + vword t0 2
  let r3 := sig r1 + vword op1 3 + vword t0 3
  ofVWords r0 r1 r2 r3

/-- `ROR(x, a) EOR ROR(x, b) EOR ROR(x, c)` on 64 bits. -/
def ror3 (x : BitVec 64) (a b c : Nat) : BitVec 64 :=
  x.rotateRight a ^^^ x.rotateRight b ^^^ x.rotateRight c

/-- SHA512H, with `X = V[n]`, `Y = V[m]`, `W = V[d]`:
`MSigma1 = ROR(Y<127:64>, 14) EOR ROR(Y<127:64>, 18) EOR ROR(Y<127:64>, 41);
Vtmp<127:64> = (Y<127:64> AND X<63:0>) EOR (NOT(Y<127:64>) AND X<127:64>);
Vtmp<127:64> = (Vtmp<127:64> + MSigma1 + W<127:64>); tmp = Vtmp<127:64> +
Y<63:0>; MSigma1 = ROR(tmp, 14) EOR ROR(tmp, 18) EOR ROR(tmp, 41);
Vtmp<63:0> = (tmp AND Y<127:64>) EOR (NOT(tmp) AND X<63:0>); Vtmp<63:0> =
(Vtmp<63:0> + MSigma1 + W<63:0>); V[d] = Vtmp`. -/
def sha512H (w x y : BitVec 128) : BitVec 128 :=
  let y1 := vdword y 1
  let hi := ((y1 &&& vdword x 0) ^^^ (~~~y1 &&& vdword x 1)) + ror3 y1 14 18 41 + vdword w 1
  let tmp := hi + vdword y 0
  let lo := ((tmp &&& y1) ^^^ (~~~tmp &&& vdword x 0)) + ror3 tmp 14 18 41 + vdword w 0
  ofVDwords lo hi

/-- SHA512H2, with `X = V[n]`, `Y = V[m]`, `W = V[d]`:
`NSigma0 = ROR(Y<63:0>, 28) EOR ROR(Y<63:0>, 34) EOR ROR(Y<63:0>, 39);
Vtmp<127:64> = (X<63:0> AND Y<127:64>) EOR (X<63:0> AND Y<63:0>) EOR
(Y<127:64> AND Y<63:0>); Vtmp<127:64> = (Vtmp<127:64> + NSigma0 +
W<127:64>); NSigma0 = ROR(Vtmp<127:64>, 28) EOR ROR(Vtmp<127:64>, 34) EOR
ROR(Vtmp<127:64>, 39); Vtmp<63:0> = (Vtmp<127:64> AND Y<63:0>) EOR
(Vtmp<127:64> AND Y<127:64>) EOR (Y<127:64> AND Y<63:0>); Vtmp<63:0> =
(Vtmp<63:0> + NSigma0 + W<63:0>); V[d] = Vtmp`. -/
def sha512H2 (w x y : BitVec 128) : BitVec 128 :=
  let x0 := vdword x 0
  let y0 := vdword y 0
  let y1 := vdword y 1
  let hi := ((x0 &&& y1) ^^^ (x0 &&& y0) ^^^ (y1 &&& y0)) + ror3 y0 28 34 39 + vdword w 1
  let lo := ((hi &&& y0) ^^^ (hi &&& y1) ^^^ (y1 &&& y0)) + ror3 hi 28 34 39 + vdword w 0
  ofVDwords lo hi

/-- SHA512SU0, with `operand1 = V[d]`, `operand2 = V[n]`:
`sig0 = ROR(operand1<127:64>, 1) EOR ROR(operand1<127:64>, 8) EOR
('0000000':operand1<127:71>); Vtmp<63:0> = operand1<63:0> + sig0;
sig0 = ROR(operand2<63:0>, 1) EOR ROR(operand2<63:0>, 8) EOR
('0000000':operand2<63:7>); Vtmp<127:64> = operand1<127:64> + sig0`. -/
def sha512Su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let sig (x : BitVec 64) : BitVec 64 := x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ x >>> 7
  ofVDwords (vdword op1 0 + sig (vdword op1 1)) (vdword op1 1 + sig (vdword op2 0))

/-- SHA512SU1, with `operand1 = V[d]`, `operand2 = V[n]`, `operand3 = V[m]`:
`sig1 = ROR(operand2<127:64>, 19) EOR ROR(operand2<127:64>, 61) EOR
('000000':operand2<127:70>); Vtmp<127:64> = operand1<127:64> + sig1 +
operand3<127:64>; sig1 = ROR(operand2<63:0>, 19) EOR ROR(operand2<63:0>, 61)
EOR ('000000':operand2<63:6>); Vtmp<63:0> = operand1<63:0> + sig1 +
operand3<63:0>`. -/
def sha512Su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let sig (x : BitVec 64) : BitVec 64 := x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ x >>> 6
  ofVDwords (vdword op1 0 + sig (vdword op2 0) + vdword op3 0)
    (vdword op1 1 + sig (vdword op2 1) + vdword op3 1)

/-! ## AES (DDI 0487, J1, "shared/functions/crypto")

The pseudocode's `AESSubBytes`, `AESInvSubBytes`, `AESShiftRows`,
`AESInvShiftRows`, `AESMixColumns` and `AESInvMixColumns` are the
transformations of the AES standard, FIPS 197 (§5), on the state whose
`s[r, c]` (FIPS 197 §3.4) is byte `r + 4c` of the 128-bit operand. They are
defined here from FIPS 197 rather than by the pseudocode's tables (the
S-boxes are FIPS 197's), and `VerifiedGarbageTest/AArch64Simd.lean` checks
them against the instructions. -/

/-- FIPS 197 §4.2, `XTIMES(b)`: `b` shifted left by one bit, XOR `{1b}` if the
bit shifted out was 1. -/
def aesXtimes (b : BitVec 8) : BitVec 8 := (b <<< 1) ^^^ (if b.msb then 0x1b else 0)

/-- FIPS 197 §4.2, the product `b • c` in GF(2⁸): the XOR of `XTIMES` applied
`i` times to `c`, for each bit `i` of `b` that is 1. -/
def aesMul (b c : BitVec 8) : BitVec 8 :=
  (List.range 8).foldl (fun acc i => if b.getLsbD i then acc ^^^ Nat.repeat aesXtimes i c else acc) 0

/-- FIPS 197 §4.4, the inverse `b⁻¹ = b²⁵⁴` in GF(2⁸), with `{00} ↦ {00}`:
`b^254 = b^2 • b^4 • … • b^128`, by repeated squaring. -/
def aesInv (b : BitVec 8) : BitVec 8 :=
  ((List.range 7).foldl (fun (acc, sq) _ => let sq := aesMul sq sq; (aesMul acc sq, sq))
    ((1 : BitVec 8), b)).1

/-- The byte whose bit `i` is `f i`. -/
def ofBits8 (f : Nat → Bool) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range 8).foldl (fun acc i => acc + if f i then 2 ^ i else 0) 0)

/-- FIPS 197 §5.1.1, the S-box: `b ↦ b⁻¹`, then `b'ᵢ = bᵢ ⊕ b₍ᵢ₊₄₎ mod 8 ⊕
b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₆₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ cᵢ` with `c = {63}`. -/
def aesSbox (b : BitVec 8) : BitVec 8 :=
  let b := aesInv b
  let c : BitVec 8 := 0x63
  ofBits8 fun i => b.getLsbD i ^^ b.getLsbD ((i + 4) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^
    b.getLsbD ((i + 6) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ c.getLsbD i

/-- FIPS 197 §5.3.2, the inverse S-box: the inverse of the affine
transformation, `b'ᵢ = b₍ᵢ₊₂₎ mod 8 ⊕ b₍ᵢ₊₅₎ mod 8 ⊕ b₍ᵢ₊₇₎ mod 8 ⊕ dᵢ` with
`d = {05}`, then `b ↦ b⁻¹`. -/
def aesInvSbox (b : BitVec 8) : BitVec 8 :=
  let d : BitVec 8 := 0x05
  aesInv (ofBits8 fun i =>
    b.getLsbD ((i + 2) % 8) ^^ b.getLsbD ((i + 5) % 8) ^^ b.getLsbD ((i + 7) % 8) ^^ d.getLsbD i)

/-- `AESSubBytes` and `AESInvSubBytes`: `f` applied to every byte. -/
def aesMapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => f (vbyte x i)

/-- `AESShiftRows`, FIPS 197 §5.1.2: `s'[r, c] = s[r, (c + r) mod 4]`. -/
def aesShiftRows (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => vbyte x (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- `AESInvShiftRows`, FIPS 197 §5.3.1: `s'[r, c] = s[r, (c − r) mod 4]`. -/
def aesInvShiftRows (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => vbyte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))

/-- FIPS 197 §5.1.3 `MIXCOLUMNS` (with `m = [{02}, {03}, {01}, {01}]`) and
§5.3.3 `INVMIXCOLUMNS` (with `m = [{0e}, {0b}, {0d}, {09}]`):
`s'[r, c] = m₀ • s[r, c] ⊕ m₁ • s[r + 1, c] ⊕ m₂ • s[r + 2, c] ⊕ m₃ • s[r + 3, c]`,
rows modulo 4. -/
def aesMixWith (m₀ m₁ m₂ m₃ : BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let a (k : Nat) : BitVec 8 := vbyte x ((i % 4 + k) % 4 + 4 * (i / 4))
    aesMul m₀ (a 0) ^^^ aesMul m₁ (a 1) ^^^ aesMul m₂ (a 2) ^^^ aesMul m₃ (a 3)

/-- `AESMixColumns`. -/
def aesMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x02 0x03 0x01 0x01

/-- `AESInvMixColumns`. -/
def aesInvMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x0e 0x0b 0x0d 0x09

/-! ## Polynomial multiplication -/

/-- `PolynomialMult(op1, op2)` for 64-bit operands: `result = Zeros(128);
extended_op2 = ZeroExtend(op2, 128); for i = 0 to 63: if op1<i> == '1'
then result = result EOR LSL(extended_op2, i)`. -/
def polyMul (a b : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 128 <<< i) else acc) 0

end VG.AArch64
