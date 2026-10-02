import VerifiedGarbage.TCB.X86.State

/-!
# IA-32 legacy SSE and cryptographic instructions

**Trusted.** Intel SDM Vol. 2, the 128-bit legacy forms of the named
instructions, https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html.
There are only eight XMM registers outside 64-bit mode. All operations
below leave flags and memory unchanged. SSE2 is the target baseline;
SSSE3, AES, PCLMULQDQ and SHA requirements are recorded in `Instr.requires`.
No vector integer multiplication instructions with Intel's MCDT hazard
are included. These are the same bit-value semantics as the x86-64 model,
restricted to the instructions the 32-bit implementations need.
-/

namespace VG.X86

/-- Register forms only; memory operands use the explicit unaligned MOVDQU. -/
inductive XBinOp
  | movdqa | paddd | pxor | por | pand | pandn
  | punpckldq | punpckhdq | punpcklqdq | punpckhqdq
  | pshufb | sha256msg1 | sha256msg2 | aesenc | aesenclast
  deriving DecidableEq, Repr

inductive XShiftOp | pslld | psrld | psllq | psrlq | pslldq | psrldq
  deriving DecidableEq, Repr

inductive XOp
  | bin (op : XBinOp) (dst src : XReg)
  | shift (op : XShiftOp) (dst : XReg) (count : BitVec 8)
  | pshufd (dst src : XReg) (order : BitVec 8)
  | palignr (dst src : XReg) (shift : BitVec 8)
  /-- SHA256RNDS2 reads XMM0 implicitly. -/
  | sha256rnds2 (dst src : XReg)
  /-- MOVD xmm, r32: zero-extends to 128 bits, unlike the 64-bit MOVQ form. -/
  | movd (dst : XReg) (src : Reg)
  | aeskeygenassist (dst src : XReg) (rcon : BitVec 8)
  | pclmulqdq (dst src : XReg) (sel : BitVec 8)
  deriving DecidableEq, Repr

/-- Doubleword `i` of `x`: bits `32i+31:32i`. -/
def dword (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * i) 32

/-- Quadword `i` of `x`: bits `64i+63:64i`. -/
def qword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * i) 64

/-- The 128-bit value with doublewords `d0` (bits 31:0), `d1`, `d2`, `d3` (bits 127:96). -/
def ofDwords (d0 d1 d2 d3 : BitVec 32) : BitVec 128 := d3 ++ d2 ++ d1 ++ d0

/-- Byte `i` of `x`: bits `8i+7:8i`. -/
def byte (x : BitVec 128) (i : Nat) : BitVec 8 := x.extractLsb' (8 * i) 8

/-- The 128-bit value whose byte `i` (bits `8i+7:8i`) is `f i`. -/
def ofBytes (f : Nat → BitVec 8) : BitVec 128 :=
  f 15 ++ f 14 ++ f 13 ++ f 12 ++ f 11 ++ f 10 ++ f 9 ++ f 8 ++
    f 7 ++ f 6 ++ f 5 ++ f 4 ++ f 3 ++ f 2 ++ f 1 ++ f 0

/-! The SHA-256 functions used, but not defined, by the SDM's pseudocode for
the SHA extensions: those of the SHA-256 standard, FIPS 180-4 §4.1.2, where
`ROTRⁿ` is a 32-bit rotate right and `SHRⁿ` a logical shift right. -/

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` -/
def sha256Ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` -/
def sha256Maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)` -/
def sha256BigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- `Σ1(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)` -/
def sha256BigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- `σ0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)` -/
def sha256Sigma0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3

/-- `σ1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)` -/
def sha256Sigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-- SDM Vol. 2, "SHA256MSG2": `W14 := SRC2[95:64]; W15 := SRC2[127:96];
W16 := SRC1[31:0] + σ1(W14); W17 := SRC1[63:32] + σ1(W15); W18 :=
SRC1[95:64] + σ1(W16); W19 := SRC1[127:96] + σ1(W17); DEST[127:96] := W19;
DEST[95:64] := W18; DEST[63:32] := W17; DEST[31:0] := W16`. -/
def sha256Msg2 (src1 src2 : BitVec 128) : BitVec 128 :=
  let w14 := dword src2 2
  let w15 := dword src2 3
  let w16 := dword src1 0 + sha256Sigma1 w14
  let w17 := dword src1 1 + sha256Sigma1 w15
  let w18 := dword src1 2 + sha256Sigma1 w16
  let w19 := dword src1 3 + sha256Sigma1 w17
  ofDwords w16 w17 w18 w19

/-! The AES transformations used, but not defined, by the SDM's pseudocode
for the AES instructions: those of the AES standard, FIPS 197 (§4 and §5).
The state `s[r, c]` (FIPS 197 §3.4) is byte `r + 4c` of the 128-bit operand,
so the operand is the state's 16 bytes in memory order. -/

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

/-- FIPS 197 §5.1.1 `SUBBYTES`: `f` applied to every byte. -/
def aesMapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => f (byte x i)

/-- FIPS 197 §5.1.2 `SHIFTROWS`: `s'[r, c] = s[r, (c + r) mod 4]`. -/
def aesShiftRows (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i => byte x (i % 4 + 4 * ((i / 4 + i % 4) % 4))

/-- FIPS 197 §5.1.3 `MIXCOLUMNS` (with `m = [{02}, {03}, {01}, {01}]`):
`s'[r, c] = m₀ • s[r, c] ⊕ m₁ • s[r + 1, c] ⊕ m₂ • s[r + 2, c] ⊕ m₃ • s[r + 3, c]`,
rows modulo 4. -/
def aesMixWith (m₀ m₁ m₂ m₃ : BitVec 8) (x : BitVec 128) : BitVec 128 :=
  ofBytes fun i =>
    let a (k : Nat) : BitVec 8 := byte x ((i % 4 + k) % 4 + 4 * (i / 4))
    aesMul m₀ (a 0) ^^^ aesMul m₁ (a 1) ^^^ aesMul m₂ (a 2) ^^^ aesMul m₃ (a 3)

def aesMixColumns : BitVec 128 → BitVec 128 := aesMixWith 0x02 0x03 0x01 0x01

/-- The carry-less product of two quadwords. SDM Vol. 2, "PCLMULQDQ", defines
bit `i` of the product as `TEMP1[0] AND TEMP2[i]` XOR … XOR `TEMP1[j] AND
TEMP2[i−j]` over all `j` with `0 ≤ i − j ≤ 63`, and bit 127 as 0; that is
the XOR, over the bits `j` of `a` that are 1, of `b` shifted left by `j`. -/
def clmul (a b : BitVec 64) : BitVec 128 :=
  (List.range 64).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0

/-- SDM Vol. 2, named legacy register forms: MOVDQA copies all 128 bits;
PADDD wraps independently in four doublewords; PXOR/POR/PAND/PANDN are
bitwise (PANDN complements the old destination); PUNPCK interleaves the
selected low/high elements. PSHUFB selects bytes by each source byte's low
nibble, zeroing when bit 7 is set. SHA256MSG1 adds sigma0 of the next word
(including source word 0); SHA256MSG2 is the dependent recurrence above.
AESENC applies ShiftRows, SubBytes, MixColumns, then XORs the round key;
AESENCLAST omits MixColumns (AESENC/AESENCLAST Operation pseudocode). -/
def XBinOp.eval : XBinOp → BitVec 128 → BitVec 128 → BitVec 128
  | .movdqa, _, b => b
  | .paddd, a, b =>
    ofDwords (dword a 0 + dword b 0) (dword a 1 + dword b 1) (dword a 2 + dword b 2)
      (dword a 3 + dword b 3)
  | .pxor, a, b => a ^^^ b
  | .por, a, b => a ||| b
  | .punpckldq, a, b => ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1)
  | .punpckhdq, a, b => ofDwords (dword a 2) (dword b 2) (dword a 3) (dword b 3)
  | .punpcklqdq, a, b => qword b 0 ++ qword a 0
  | .punpckhqdq, a, b => qword b 1 ++ qword a 1
  | .pshufb, a, b => ofBytes fun i =>
    let c := byte b i
    if c.msb then 0 else byte a (c.extractLsb' 0 4).toNat
  | .sha256msg1, a, b =>
    ofDwords (dword a 0 + sha256Sigma0 (dword a 1)) (dword a 1 + sha256Sigma0 (dword a 2))
      (dword a 2 + sha256Sigma0 (dword a 3)) (dword a 3 + sha256Sigma0 (dword b 0))
  | .sha256msg2, a, b => sha256Msg2 a b
  | .pand, a, b => a &&& b
  | .pandn, a, b => ~~~a &&& b
  | .aesenc, a, b => aesMixColumns (aesMapBytes aesSbox (aesShiftRows a)) ^^^ b
  | .aesenclast, a, b => aesMapBytes aesSbox (aesShiftRows a) ^^^ b
/-- SDM Vol. 2 PSLLD/PSRLD/PSLLQ/PSRLQ: each element shifts logically,
becoming zero for counts greater than its width minus one. PSLLDQ/PSRLDQ
shift the whole register by bytes, becoming zero for counts at least 16.
All forms use an imm8 and leave flags unchanged. -/
def XShiftOp.eval (op : XShiftOp) (a : BitVec 128) (count : BitVec 8) : BitVec 128 :=
  let n := count.toNat
  let dwords (f : BitVec 32 → BitVec 32) : BitVec 128 :=
    if 31 < n then 0 else ofDwords (f (dword a 0)) (f (dword a 1)) (f (dword a 2)) (f (dword a 3))
  let qwords (f : BitVec 64 → BitVec 64) : BitVec 128 :=
    if 63 < n then 0 else f (qword a 1) ++ f (qword a 0)
  match op with
  | .pslld => dwords (· <<< n)
  | .psrld => dwords (· >>> n)
  | .psllq => qwords (· <<< n)
  | .psrlq => qwords (· >>> n)
  | .pslldq => a <<< (min n 16 * 8)
  | .psrldq => a >>> (min n 16 * 8)
/-- SDM Vol. 2, "PSHUFD": `DEST[31:0] := (SRC >> (ORDER[1:0] * 32))[31:0];
DEST[63:32] := (SRC >> (ORDER[3:2] * 32))[31:0]; DEST[95:64] := (SRC >>
(ORDER[5:4] * 32))[31:0]; DEST[127:96] := (SRC >> (ORDER[7:6] * 32))[31:0]`.
No flags are affected. -/
def shufDwords (a : BitVec 128) (order : BitVec 8) : BitVec 128 :=
  ofDwords (dword a (order.extractLsb' 0 2).toNat) (dword a (order.extractLsb' 2 2).toNat)
    (dword a (order.extractLsb' 4 2).toNat) (dword a (order.extractLsb' 6 2).toNat)

/-- SDM Vol. 2, "PALIGNR", 128-bit legacy SSE version: `temp1[255:0] :=
((DEST[127:0] << 128) OR SRC[127:0])>>(imm8*8); DEST[127:0] :=
temp1[127:0]`. No flags are affected. -/
def alignRight (dst src : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  ((dst ++ src) >>> (imm.toNat * 8)).extractLsb' 0 128

/-- SDM Vol. 2, "SHA256RNDS2", where `SRC1` is the destination, `SRC2` the
source and `wk` the implicit operand `XMM0`: `A_0 := SRC2[127:96]; B_0 :=
SRC2[95:64]; C_0 := SRC1[127:96]; D_0 := SRC1[95:64]; E_0 := SRC2[63:32];
F_0 := SRC2[31:0]; G_0 := SRC1[63:32]; H_0 := SRC1[31:0]; WK0 :=
XMM0[31:0]; WK1 := XMM0[63:32]; FOR i = 0 to 1 A_(i+1) := Ch(E_i, F_i,
G_i) + Σ1(E_i) + WKi + H_i + Maj(A_i, B_i, C_i) + Σ0(A_i); B_(i+1) := A_i;
C_(i+1) := B_i; D_(i+1) := C_i; E_(i+1) := Ch(E_i, F_i, G_i) + Σ1(E_i) +
WKi + H_i + D_i; F_(i+1) := E_i; G_(i+1) := F_i; H_(i+1) := G_i; ENDFOR
DEST[127:96] := A_2; DEST[95:64] := B_2; DEST[63:32] := E_2; DEST[31:0] :=
F_2`. No flags are affected. -/
def sha256Rnds2 (src1 src2 wk : BitVec 128) : BitVec 128 :=
  let a0 := dword src2 3
  let b0 := dword src2 2
  let c0 := dword src1 3
  let d0 := dword src1 2
  let e0 := dword src2 1
  let f0 := dword src2 0
  let g0 := dword src1 1
  let h0 := dword src1 0
  let wk0 := dword wk 0
  let wk1 := dword wk 1
  let a1 := sha256Ch e0 f0 g0 + sha256BigSigma1 e0 + wk0 + h0 + sha256Maj a0 b0 c0 +
    sha256BigSigma0 a0
  let b1 := a0
  let c1 := b0
  let d1 := c0
  let e1 := sha256Ch e0 f0 g0 + sha256BigSigma1 e0 + wk0 + h0 + d0
  let f1 := e0
  let g1 := f0
  let h1 := g0
  let a2 := sha256Ch e1 f1 g1 + sha256BigSigma1 e1 + wk1 + h1 + sha256Maj a1 b1 c1 +
    sha256BigSigma0 a1
  let b2 := a1
  let e2 := sha256Ch e1 f1 g1 + sha256BigSigma1 e1 + wk1 + h1 + d1
  let f2 := e1
  ofDwords f2 e2 b2 a2

/-- SDM Vol. 2, "AESKEYGENASSIST": `X3[31:0] := SRC[127:96]; X2[31:0] :=
SRC[95:64]; X1[31:0] := SRC[63:32]; X0[31:0] := SRC[31:0]; RCON[31:0] :=
ZeroExtend(imm8[7:0]); DEST[31:0] := SubWord(X1); DEST[63:32] :=
RotWord(SubWord(X1)) XOR RCON; DEST[95:64] := SubWord(X3); DEST[127:96] :=
RotWord(SubWord(X3)) XOR RCON`, where `SubWord` applies the S-box to each
byte and `RotWord(x) = (x >> 8) OR (x << 24)` (a 32-bit rotate right by 8).
No flags are affected. -/
def aesKeygenAssist (src : BitVec 128) (rcon : BitVec 8) : BitVec 128 :=
  let subWord (x : BitVec 32) : BitVec 32 :=
    aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
      aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)
  let rc : BitVec 32 := rcon.setWidth 32
  let x1 := subWord (dword src 1)
  let x3 := subWord (dword src 3)
  ofDwords x1 (x1.rotateRight 8 ^^^ rc) x3 (x3.rotateRight 8 ^^^ rc)

/-- SDM Vol. 2, "PCLMULQDQ", 128-bit legacy SSE version: `IF (imm8[0] = 0)
THEN TEMP1 := SRC1[63:0] ELSE TEMP1 := SRC1[127:64]; IF (imm8[4] = 0) THEN
TEMP2 := SRC2[63:0] ELSE TEMP2 := SRC2[127:64]`, and `DEST[127:0]` the
carry-less product of `TEMP1` and `TEMP2` (`clmul`). No flags are affected. -/
def pclmul (src1 src2 : BitVec 128) (sel : BitVec 8) : BitVec 128 :=
  clmul (qword src1 (if sel.getLsbD 0 then 1 else 0)) (qword src2 (if sel.getLsbD 4 then 1 else 0))

/-- Intel SDM Vol. 2 MOVD/MOVQ, legacy MOVD xmm, r32:
DEST[31:0] := SRC[31:0]; DEST[127:32] := 0. Other forms use the value
operations above. No flags are affected. -/
def XOp.exec : XOp → State → State
  | .bin op d r, s => s.setXmm d (op.eval (s.xmm d) (s.xmm r))
  | .shift op d n, s => s.setXmm d (op.eval (s.xmm d) n)
  | .pshufd d r o, s => s.setXmm d (shufDwords (s.xmm r) o)
  | .palignr d r n, s => s.setXmm d (alignRight (s.xmm d) (s.xmm r) n)
  | .sha256rnds2 d r, s => s.setXmm d (sha256Rnds2 (s.xmm d) (s.xmm r) (s.xmm .xmm0))
  | .movd d r, s => s.setXmm d ((0 : BitVec 96) ++ s.gpr r)
  | .aeskeygenassist d r n, s => s.setXmm d (aesKeygenAssist (s.xmm r) n)
  | .pclmulqdq d r n, s => s.setXmm d (pclmul (s.xmm d) (s.xmm r) n)

end VG.X86
