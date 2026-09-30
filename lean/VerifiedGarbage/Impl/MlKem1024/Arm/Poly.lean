import VerifiedGarbage.Impl.MlKem.Arm.Poly

/-!
# ML-KEM-1024: the compression to 5 and 11 bits, and the key check, on 32-bit ARM

The primitives of `Spec/MlKem/Contract1024.lean` that go through the
coefficients once, as `Impl/MlKem/Arm/Poly.lean` does for ML-KEM-768: they
take their arguments in `r0`–`r3`, use only those registers and `r12`, so
save nothing and use no stack, and every loop counts down to zero with
`subs` and `bne`.

A group of 8 coefficients is `d` bytes, for both widths. Field `k` of a
group starts at bit `d k`: in byte `j = ⌊d k / 8⌋`, at bit `t = d k mod 8`,
and spans `n = ⌈(t + d) / 8⌉` bytes (`fieldAt`). The loop over the groups
has a body of the 8 fields, each a few instructions of the same shapes.

* `vg_mlkem1024_compress_encode(f = r0, d = r1, out = r2, len = r3)`
  branches on `d` (public), and loops over the 32 groups with `r3`
  counting. `Compress_d(x)` is `((x · M_d + 2¹⁸ - 2⁸) >> 19) mod 2ᵈ`
  (`VG.Proof.MlKem.compress1024_eq`), with `M_d` built in `r12` and `mul`
  (and the reduction modulo `2⁵` an `and`; the value for `d = 11` is less
  than `2¹¹`). Field `k` completes byte `j` (adding its low bits, shifted
  by `t`, to what the fields before it stored there, or storing them if
  `t = 0`) and starts the bytes after it (each the next 8 bits: `strb`
  stores the low byte of a register).
* `vg_mlkem1024_decode_decompress(b = r0, len = r1, d = r2, f = r3)`
  branches on `d`, and loops over the input with `len` counting down: field
  `k` is the bytes it spans, shifted into place and added, then reduced
  modulo `2ᵈ` by a pair of shifts, and `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d`
  (`VG.Impl.MlKem.Arm.decompressTo`).
* `vg_mlkem1024_check_ek(ek = r0)`: `vg_mlkem768_check_ek`'s loop, over
  the 512 groups of three bytes of `ek[0 : 1536]`.

Every address is a pointer plus a constant, and every branch depends on a
counter or `d`: only the pointers, `d` and `len` can affect timing.
-/

namespace VG.Impl.MlKem1024.Arm

open VG.Arm
open VG.Impl.MlKem.Arm (decompressTo countBad checkEkBody)

/-- Field `k` of a group of `d`-bit fields: its first byte `j`, its first
bit `t` in that byte, and the number of bytes it spans. -/
def fieldAt (d k : Nat) : Nat × Nat × Nat := (d * k / 8, d * k % 8, (d * k % 8 + d + 7) / 8)

/-! ## `ByteEncode_d ∘ Compress_d` -/

/-- `(x · M + 2¹⁸ - 2⁸) >> 19` of the coefficient at `r0 + off`, into `r1`,
with `M` built in `r12`. -/
def compressAt4 (off : Nat) (mlo mhi : BitVec 16) : List Instr :=
  [.ldr .r1 .r0 off, .movw .r12 mlo] ++ (if mhi = 0 then [] else [.movt .r12 mhi]) ++
  [.mul .r1 .r1 .r12, .dp .add .r1 .r1 (.imm 0x40000), .dp .sub .r1 .r1 (.imm 0x100),
   .mov .r1 (.shifted .r1 .lsr 19)]

/-- `Compress_d` of coefficient `k` of the group, into `r1`. -/
def ceCoeff (d k : Nat) : List Instr :=
  if d = 5 then compressAt4 (4 * k) 5040 0 ++ [.dp .and .r1 .r1 (.imm 31)]
  else compressAt4 (4 * k) 0xEBEE 0x4

/-- The low bits of the field in `r1` into byte `j` of the group: stored if
the field starts the byte (`t = 0`), and added to the byte otherwise. -/
def ceHead (j t : Nat) : List Instr :=
  if t = 0 then [.strb .r1 .r2 j]
  else [.ldrb .r12 .r2 j, .dp .add .r12 .r12 (.shifted .r1 .lsl t), .strb .r12 .r2 j]

/-- Byte `j + 1 + i` of the group: the next 8 bits of the field. -/
def ceNext (j t i : Nat) : List Instr :=
  [.mov .r1 (.shifted .r1 .lsr (if i = 0 then 8 - t else 8)), .strb .r1 .r2 (j + 1 + i)]

/-- Field `k` of a group, compressed and encoded. -/
def ceField (d k : Nat) : List Instr :=
  ceCoeff d k ++ ceHead (fieldAt d k).1 (fieldAt d k).2.1 ++
    (List.range ((fieldAt d k).2.2 - 1)).flatMap (ceNext (fieldAt d k).1 (fieldAt d k).2.1)

/-- A group of 8 coefficients, into `d` bytes. -/
def ceBody (d : Nat) : List Instr :=
  (List.range 8).flatMap (ceField d) ++
    [.dp .add .r0 .r0 (.imm 32), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 d)), .subs .r3 .r3 (.imm 1)]

def compressEncode1024 : Prog isa :=
  .seq (.block [.cmp .r1 (.imm 5), .mov .r3 (.imm 32)])
    (.ite .eq (.loop (.block (ceBody 5)) .ne) (.loop (.block (ceBody 11)) .ne))

/-! ## `Decompress_d ∘ ByteDecode_d` -/

/-- The first byte of a field, shifted down by `t`, into `r2`. -/
def ddHead (j t : Nat) : List Instr :=
  .ldrb .r2 .r0 j :: (if t = 0 then [] else [.mov .r2 (.shifted .r2 .lsr t)])

/-- Byte `j + 1 + i` of the group added to the field, shifted into place. -/
def ddNext (j t i : Nat) : List Instr :=
  [.ldrb .r12 .r0 (j + 1 + i), .dp .add .r2 .r2 (.shifted .r12 .lsl (8 * (i + 1) - t))]

/-- Field `k` of a group, decoded and decompressed into coefficient `k`. -/
def ddField (d k : Nat) : List Instr :=
  ddHead (fieldAt d k).1 (fieldAt d k).2.1 ++
    (List.range ((fieldAt d k).2.2 - 1)).flatMap (ddNext (fieldAt d k).1 (fieldAt d k).2.1) ++
    [.mov .r2 (.shifted .r2 .lsl (32 - d)), .mov .r2 (.shifted .r2 .lsr (32 - d))] ++
    decompressTo d (4 * k)

/-- A group of `d` bytes, into 8 coefficients. -/
def ddBody (d : Nat) : List Instr :=
  (List.range 8).flatMap (ddField d) ++
    [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 d)), .dp .add .r3 .r3 (.imm 32),
     .subs .r1 .r1 (.imm (BitVec.ofNat 32 d))]

def decodeDecompress1024 : Prog isa :=
  .seq (.block [.cmp .r2 (.imm 5)])
    (.ite .eq (.loop (.block (ddBody 5)) .ne) (.loop (.block (ddBody 11)) .ne))

/-! ## The encapsulation key check -/

def checkEk1024 : Prog isa :=
  .seq (.block [.mov .r1 (.imm 512), .mov .r2 (.imm 0)])
    (.seq (.loop (.block checkEkBody) .ne)
      (.block [.mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31),
        .mov .r0 (.imm 1), .dp .sub .r0 .r0 (.reg .r3)]))

end VG.Impl.MlKem1024.Arm
