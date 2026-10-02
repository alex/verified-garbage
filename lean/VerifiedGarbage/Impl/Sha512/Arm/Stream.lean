import VerifiedGarbage.Impl.Sha512.Arm
import VerifiedGarbage.Impl.MdStream.Arm

/-!
# Streaming SHA-512: 32-bit ARM implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`); each 64-bit word of the hash
value is stored little-endian, so as its low half followed by its high half.

* `init iv (state = r0)` stores the initial hash value `iv`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sha512_compress`) with `scratch[0..224)` as its scratch space, and
  saving our caller's `r4`–`r11` and `lr` in `scratch[224..260)`. The length
  field is the length in bits as a 128-bit big-endian integer: `count >> 61`,
  then `count << 3` (modulo 2⁶⁴); the words of the final hash value are
  big-endian.
-/

namespace VG.Impl.Sha512.Arm.Stream

open VG.Arm
open VG.Impl.Sha512.Arm (compress lo hi)
open VG.Impl.MdStream.Arm (Params len64)

/-- Store word `k` of `iv`. -/
def initW (iv : Spec.Sha512.HashValue) (k : Nat) : List Instr :=
  [.movw .r12 ((lo iv[k]!).extractLsb' 0 16), .movt .r12 ((lo iv[k]!).extractLsb' 16 16),
   .str .r12 .r0 (8 * k),
   .movw .r12 ((hi iv[k]!).extractLsb' 0 16), .movt .r12 ((hi iv[k]!).extractLsb' 16 16),
   .str .r12 .r0 (8 * k + 4)]

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap (initW iv))

/-- Word `k` of the final hash value, big-endian. -/
def outW (k : Nat) : List Instr :=
  [.ldr .r9 .r0 (8 * k), .ldr .r10 .r0 (8 * k + 4), .rev .r10 .r10, .rev .r9 .r9,
   .str .r10 .r6 (8 * k), .str .r9 .r6 (8 * k + 4)]

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 64
  B := 128
  L := 16
  so := 224
  len := [.mov .r9 (.imm 0), .str .r9 .r0 176, .mov .r9 (.shifted .r5 .lsr 29), .rev .r9 .r9, .str .r9 .r0 180] ++
    len64 184 true
  out := (List.range 8).flatMap outW

def update : Prog isa := MdStream.Arm.update params "vg_sha512_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sha512_compress" compress

end VG.Impl.Sha512.Arm.Stream
