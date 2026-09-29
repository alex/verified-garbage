import VerifiedGarbage.TCB.Arm.Isa

/-!
# ML-KEM: the coefficient-wise primitives on 32-bit ARM

The primitives of `Spec/MlKem/Poly.lean` (and the encapsulation key check of
`Spec/MlKem/Contract.lean`) that go through the coefficients once, each a
loop with a straight-line body. They take at most four arguments, in
`r0`–`r3`, and use only those registers and `r12`, so they save nothing and
use no stack. Every loop counts down to zero with `subs` and `bne`.

A value `u` in `(-q, q)` (as a 32-bit two's complement number) is reduced
into `[0, q)` without a branch by `fixup`: `c = u >> 31` (1 if `u` is
negative), then `u + c·q`, with `c·q = c + (c << 8) + (c << 10) + (c << 11)`
(`q = 3329 = 2¹¹ + 2¹⁰ + 2⁸ + 1`). A sum `a + b` of reduced values is
reduced as `fixup (a + b - q)`, a difference as `fixup (a - b)`; `q` is not
an encodable immediate, so `- q` is two subtractions (`subQ`).

The model has no register-offset addressing and no `bic`/`ubfx`: fields of
bytes are extracted with pairs of shifts, and pointers advance through the
arrays.

* `vg_mlkem_add(f = r0, g = r1)`, `vg_mlkem_sub(f = r0, g = r1)`: a loop
  over the 256 coefficients, `r2` counting.
* `vg_mlkem_encode12(f = r0, out = r1)`: a loop over the 128 pairs of
  coefficients, storing three bytes each; `r2` counting.
* `vg_mlkem_decode12(b = r0, f = r1)`: a loop over the 128 groups of three
  bytes, each two 12-bit fields, each reduced with one `fixup`.
* `vg_mlkem_cbd2(b = r0, f = r1)`: a loop over the 128 bytes, each two
  coefficients: `x - y` for the numbers of bits set `x` and `y` in two
  2-bit fields `v`, each `v - (v >> 1)`, reduced with `fixup`. The byte is
  loaded again for each field, as there are only two temporaries.
* `vg_mlkem_compress_encode(f = r0, d = r1, out = r2, len = r3)` branches
  on `d` (public), and loops over the output: `Compress_d(x)` is
  `((x · M_d + 2¹⁸ - 64) >> 19) mod 2ᵈ` (`VG.Proof.MlKem.compress_eq`),
  with `M_d` built in `r12` and `mul`. The bits of the byte being built
  are added into the low bits of `r3`, whose top 8 bits count the loop
  down (the count is shifted down, decremented with `subs`, and shifted
  back, which also clears the low bits).
* `vg_mlkem_decode_decompress(b = r0, len = r1, d = r2, f = r3)` branches
  on `d`, and loops over the input with `len` counting down:
  `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`.
* `vg_mlkem768_check_ek(ek = r0)`: counts, in `r2`, the 12-bit fields of
  `ek[0 : 1152]` that are at least `q` (the sign bit of `3328 - F`), and
  returns 1 if there are none: `1 - ((0 - n) >> 31)`.

Every address is a pointer plus a constant, and every branch depends on a
counter or `d`: only the pointers, `d` and `len` can affect timing.
-/

namespace VG.Impl.MlKem.Arm

open VG.Arm

/-- `r := r - q`. -/
def subQ (r : Reg) : List Instr := [.dp .sub r r (.imm 3328), .dp .sub r r (.imm 1)]

/-- `r := r + q` if `r` is negative, with `t` as a temporary. -/
def fixup (r t : Reg) : List Instr :=
  [.mov t (.shifted r .lsr 31), .dp .add r r (.reg t), .dp .add r r (.shifted t .lsl 8),
   .dp .add r r (.shifted t .lsl 10), .dp .add r r (.shifted t .lsl 11)]

/-! ## Addition and subtraction -/

/-- The end of an iteration over coefficients: `f` and `g` advance, `r2`
counts down. -/
def accTail : List Instr :=
  [.str .r3 .r0 0, .dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .subs .r2 .r2 (.imm 1)]

def addBody : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r12 .r1 0, .dp .add .r3 .r3 (.reg .r12)] ++ subQ .r3 ++ fixup .r3 .r12 ++
    accTail

def subBody : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r12 .r1 0, .dp .sub .r3 .r3 (.reg .r12)] ++ fixup .r3 .r12 ++ accTail

def add : Prog isa := .seq (.block [.mov .r2 (.imm 256)]) (.loop (.block addBody) .ne)

def sub : Prog isa := .seq (.block [.mov .r2 (.imm 256)]) (.loop (.block subBody) .ne)

/-! ## `ByteEncode₁₂` and `ByteDecode₁₂` -/

def encode12Body : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r12 .r0 4, .strb .r3 .r1 0, .mov .r3 (.shifted .r3 .lsr 8),
   .dp .add .r3 .r3 (.shifted .r12 .lsl 4), .strb .r3 .r1 1, .mov .r12 (.shifted .r12 .lsr 4),
   .strb .r12 .r1 2, .dp .add .r0 .r0 (.imm 8), .dp .add .r1 .r1 (.imm 3), .subs .r2 .r2 (.imm 1)]

def encode12 : Prog isa := .seq (.block [.mov .r2 (.imm 128)]) (.loop (.block encode12Body) .ne)

/-- The first field of a group, `b₀ + 256 (b₁ mod 16)`, reduced, stored. -/
def decode12Lo : List Instr :=
  [.ldrb .r3 .r0 0, .ldrb .r12 .r0 1, .mov .r12 (.shifted .r12 .lsl 28),
   .dp .add .r3 .r3 (.shifted .r12 .lsr 20)] ++ subQ .r3 ++ fixup .r3 .r12 ++ [.str .r3 .r1 0]

/-- The second field of a group, `⌊b₁ / 16⌋ + 16 b₂`, reduced, stored. -/
def decode12Hi : List Instr :=
  [.ldrb .r3 .r0 1, .mov .r3 (.shifted .r3 .lsr 4), .ldrb .r12 .r0 2,
   .dp .add .r3 .r3 (.shifted .r12 .lsl 4)] ++ subQ .r3 ++ fixup .r3 .r12 ++ [.str .r3 .r1 4]

def decode12Body : List Instr :=
  decode12Lo ++ decode12Hi ++
    [.dp .add .r0 .r0 (.imm 3), .dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)]

def decode12 : Prog isa := .seq (.block [.mov .r2 (.imm 128)]) (.loop (.block decode12Body) .ne)

/-! ## `SamplePolyCBD₂` -/

/-- The number of bits set in the 2-bit field `v` of the byte at `r0` from
bit `k` (`k ≤ 6`), into `r`: `v - (v >> 1)`. -/
def pop2 (r : Reg) (k : Nat) : List Instr :=
  [.ldrb r .r0 0, .mov r (.shifted r .lsl (30 - k)), .mov r (.shifted r .lsr 30),
   .dp .sub r r (.shifted r .lsr 1)]

/-- The coefficient of the nibble of the byte at `r0` from bit `k`, stored
at `r1 + off`. -/
def cbdCoeff (k off : Nat) : List Instr :=
  pop2 .r3 k ++ pop2 .r12 (k + 2) ++ [.dp .sub .r3 .r3 (.reg .r12)] ++ fixup .r3 .r12 ++
    [.str .r3 .r1 off]

def cbd2Body : List Instr :=
  cbdCoeff 0 0 ++ cbdCoeff 4 4 ++
    [.dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 8), .subs .r2 .r2 (.imm 1)]

def cbd2 : Prog isa := .seq (.block [.mov .r2 (.imm 128)]) (.loop (.block cbd2Body) .ne)

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- `(x · M + 2¹⁸ - 64) >> 19` of the coefficient at `r0 + off`, into `r1`,
with `M` built in `r12`. -/
def compressAt (off : Nat) (mlo mhi : BitVec 16) : List Instr :=
  [.ldr .r1 .r0 off, .movw .r12 mlo] ++ (if mhi = 0 then [] else [.movt .r12 mhi]) ++
  [.mul .r1 .r1 .r12, .dp .add .r1 .r1 (.imm 0x40000), .dp .sub .r1 .r1 (.imm 0x40),
   .mov .r1 (.shifted .r1 .lsr 19)]

/-- The end of an output byte: stored, the count in the top 8 bits of `r3`
decremented, and the low bits cleared. -/
def byteTail : List Instr :=
  [.strb .r3 .r2 0, .mov .r3 (.shifted .r3 .lsr 24), .subs .r3 .r3 (.imm 1),
   .mov .r3 (.shifted .r3 .lsl 24)]

/-- Bit `j` of an output byte of `ByteEncode₁(Compress₁)`. -/
def ce1Bit (j : Nat) : List Instr :=
  compressAt (4 * j) 315 0 ++
    [.mov .r1 (.shifted .r1 .lsl 31), .dp .add .r3 .r3 (.shifted .r1 .lsr (31 - j))]

def ce1Body : List Instr :=
  (List.range 8).flatMap ce1Bit ++ byteTail ++ [.dp .add .r0 .r0 (.imm 32), .dp .add .r2 .r2 (.imm 1)]

/-- Nibble `k` of an output byte of `ByteEncode₄(Compress₄)`. -/
def ce4Nibble (k : Nat) : List Instr :=
  compressAt (4 * k) 2520 0 ++
    [.mov .r1 (.shifted .r1 .lsl 28), .dp .add .r3 .r3 (.shifted .r1 .lsr (28 - 4 * k))]

def ce4Body : List Instr :=
  ce4Nibble 0 ++ ce4Nibble 1 ++ byteTail ++ [.dp .add .r0 .r0 (.imm 8), .dp .add .r2 .r2 (.imm 1)]

/-- `Compress₁₀` of coefficient `k` of the group, into `r1`. -/
def ce10Coeff (k : Nat) : List Instr :=
  compressAt (4 * k) 0x75F7 0x2 ++ [.mov .r1 (.shifted .r1 .lsl 22), .mov .r1 (.shifted .r1 .lsr 22)]

/-- Clears the low 24 bits of `r3`. -/
def clearAcc : List Instr := [.mov .r3 (.shifted .r3 .lsr 24), .mov .r3 (.shifted .r3 .lsl 24)]

def ce10Body : List Instr :=
  ce10Coeff 0 ++ [.strb .r1 .r2 0, .dp .add .r3 .r3 (.shifted .r1 .lsr 8)] ++
  ce10Coeff 1 ++ [.dp .add .r3 .r3 (.shifted .r1 .lsl 2), .strb .r3 .r2 1] ++ clearAcc ++
    [.dp .add .r3 .r3 (.shifted .r1 .lsr 6)] ++
  ce10Coeff 2 ++ [.dp .add .r3 .r3 (.shifted .r1 .lsl 4), .strb .r3 .r2 2] ++ clearAcc ++
    [.dp .add .r3 .r3 (.shifted .r1 .lsr 4)] ++
  ce10Coeff 3 ++ [.dp .add .r3 .r3 (.shifted .r1 .lsl 6), .strb .r3 .r2 3] ++ clearAcc ++
    [.mov .r1 (.shifted .r1 .lsr 2), .strb .r1 .r2 4] ++
  [.subs .r3 .r3 (.imm 0x1000000), .dp .add .r0 .r0 (.imm 16), .dp .add .r2 .r2 (.imm 5)]

def compressEncode : Prog isa :=
  .seq (.block [.cmp .r1 (.imm 1)])
    (.ite .eq (.seq (.block [.mov .r3 (.imm 0x20000000)]) (.loop (.block ce1Body) .ne))
      (.seq (.block [.cmp .r1 (.imm 4)])
        (.ite .eq (.seq (.block [.mov .r3 (.imm 0x80000000)]) (.loop (.block ce4Body) .ne))
          (.seq (.block [.mov .r3 (.imm 0x40000000)]) (.loop (.block ce10Body) .ne)))))

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- `(q · y + 2ᵈ⁻¹) >> d` of `y` in `r2`, stored at `r3 + off`, with `r12`
as a temporary. -/
def decompressTo (d off : Nat) : List Instr :=
  [.dp .add .r12 .r2 (.shifted .r2 .lsl 8), .dp .add .r12 .r12 (.shifted .r2 .lsl 10),
   .dp .add .r12 .r12 (.shifted .r2 .lsl 11), .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (2 ^ (d - 1)))),
   .mov .r12 (.shifted .r12 .lsr d), .str .r12 .r3 off]

/-- Coefficient `j` of a byte of `ByteDecode₁`: bit `j`. -/
def dd1Bit (j : Nat) : List Instr :=
  [.ldrb .r2 .r0 0, .mov .r2 (.shifted .r2 .lsl (31 - j)), .mov .r2 (.shifted .r2 .lsr 31)] ++
    decompressTo 1 (4 * j)

def dd1Body : List Instr :=
  (List.range 8).flatMap dd1Bit ++
    [.dp .add .r0 .r0 (.imm 1), .dp .add .r3 .r3 (.imm 32), .subs .r1 .r1 (.imm 1)]

def dd4Body : List Instr :=
  [.ldrb .r2 .r0 0, .mov .r2 (.shifted .r2 .lsl 28), .mov .r2 (.shifted .r2 .lsr 28)] ++
    decompressTo 4 0 ++
  [.ldrb .r2 .r0 0, .mov .r2 (.shifted .r2 .lsr 4)] ++ decompressTo 4 4 ++
  [.dp .add .r0 .r0 (.imm 1), .dp .add .r3 .r3 (.imm 8), .subs .r1 .r1 (.imm 1)]

/-- Field `k < 3` of a group of `ByteDecode₁₀`: the high `2k + 2` bits of
byte `k`, and the low `8 - 2k` bits of byte `k + 1`, shifted up. -/
def dd10Field (k : Nat) : List Instr :=
  [.ldrb .r2 .r0 (k + 1), .mov .r2 (.shifted .r2 .lsl (30 - 2 * k)), .mov .r2 (.shifted .r2 .lsr 22),
   .ldrb .r12 .r0 k] ++
  (if k = 0 then [.dp .add .r2 .r2 (.reg .r12)] else [.dp .add .r2 .r2 (.shifted .r12 .lsr (2 * k))]) ++
  decompressTo 10 (4 * k)

def dd10Body : List Instr :=
  dd10Field 0 ++ dd10Field 1 ++ dd10Field 2 ++
  [.ldrb .r2 .r0 4, .mov .r2 (.shifted .r2 .lsl 2), .ldrb .r12 .r0 3,
   .dp .add .r2 .r2 (.shifted .r12 .lsr 6)] ++ decompressTo 10 12 ++
  [.dp .add .r0 .r0 (.imm 5), .dp .add .r3 .r3 (.imm 16), .subs .r1 .r1 (.imm 5)]

def decodeDecompress : Prog isa :=
  .seq (.block [.cmp .r2 (.imm 1)])
    (.ite .eq (.loop (.block dd1Body) .ne)
      (.seq (.block [.cmp .r2 (.imm 4)])
        (.ite .eq (.loop (.block dd4Body) .ne) (.loop (.block dd10Body) .ne))))

/-! ## The encapsulation key check -/

/-- Adds 1 to `r2` if the field in `r3` is at least `q`. -/
def countBad : List Instr :=
  [.mov .r12 (.imm 3328), .dp .sub .r12 .r12 (.reg .r3), .dp .add .r2 .r2 (.shifted .r12 .lsr 31)]

def checkEkBody : List Instr :=
  [.ldrb .r3 .r0 1, .mov .r3 (.shifted .r3 .lsl 28), .mov .r3 (.shifted .r3 .lsr 20),
   .ldrb .r12 .r0 0, .dp .add .r3 .r3 (.reg .r12)] ++ countBad ++
  [.ldrb .r3 .r0 1, .mov .r3 (.shifted .r3 .lsr 4), .ldrb .r12 .r0 2,
   .dp .add .r3 .r3 (.shifted .r12 .lsl 4)] ++ countBad ++
  [.dp .add .r0 .r0 (.imm 3), .subs .r1 .r1 (.imm 1)]

def checkEk : Prog isa :=
  .seq (.block [.mov .r1 (.imm 384), .mov .r2 (.imm 0)])
    (.seq (.loop (.block checkEkBody) .ne)
      (.block [.mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31),
        .mov .r0 (.imm 1), .dp .sub .r0 .r0 (.reg .r3)]))

end VG.Impl.MlKem.Arm
