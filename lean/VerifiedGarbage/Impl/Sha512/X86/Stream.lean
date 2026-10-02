import VerifiedGarbage.Impl.Sha512.X86
import VerifiedGarbage.Impl.MdStream.X86

/-!
# Streaming SHA-512: x86 (32-bit) implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`); each 64-bit word of the hash
value is stored little-endian, so as its low half followed by its high half.
Every argument is on the stack (cdecl).

* `init iv (state)` stores the initial hash value `iv`.
* `update(state, count, data, len, scratch)` and
  `finalize(state, count, out, scratch)` are the generic streaming code of
  `Impl/MdStream/X86.lean`, calling `vg_sha512_compress`
  (`Impl.Sha512.X86.compress`) with `scratch[0..224)` as its scratch space;
  our caller's callee-saved registers are saved in `scratch[224..240)`, and
  `finalize` keeps `count` and `out` in `scratch[240..252)`. The length
  field is the length in bits as a 128-bit big-endian integer: `count >> 61`,
  then `count << 3` (modulo 2⁶⁴); the words of the final hash value are
  big-endian.
-/

namespace VG.Impl.Sha512.X86.Stream

open VG.X86
open VG.Impl.Sha512.X86 (at_ compress lo hi)
open VG.Impl.MdStream.X86 (Params loadCount len64Of out64)

/-- Store word `k` of `iv`, at `eax`. -/
def initW (iv : Spec.Sha512.HashValue) (k : Nat) : List Instr :=
  [.mov .ecx (.imm (lo iv[k]!)), .store (at_ .eax (8 * k)) .ecx,
   .mov .ecx (.imm (hi iv[k]!)), .store (at_ .eax (8 * k + 4)) .ecx]

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block (.mov .eax (.mem (at_ .esp 4)) :: (List.range 8).flatMap (initW iv))

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 64
  B := 128
  L := 16
  so := 224
  len := loadCount 224 ++ [.mov .edx (.imm 0), .store (at_ .ebx 176) .edx,
    .mov .edx (.reg .ecx), .shift .shr .edx 29, .bswap .edx, .store (at_ .ebx 180) .edx] ++ len64Of 184 true
  out := out64 8

def update : Prog isa := MdStream.X86.update params "vg_sha512_compress" compress

def finalize : Prog isa := MdStream.X86.finalize params "vg_sha512_compress" compress

end VG.Impl.Sha512.X86.Stream
