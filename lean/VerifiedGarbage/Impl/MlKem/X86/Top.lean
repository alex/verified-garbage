import VerifiedGarbage.Impl.MlKem.X86.Sample
import VerifiedGarbage.Impl.MlKem.X86.CheckEk
import VerifiedGarbage.Impl.MlKem.X86.Compress
import VerifiedGarbage.Impl.MlKem.X86.Encode
import VerifiedGarbage.Impl.MlKem.X86.Cbd
import VerifiedGarbage.Impl.MlKem.X86.Ntt

/-!
# ML-KEM on x86 (32-bit): building blocks of the top-level functions

The top-level functions are sequences of calls of the primitives and the
Keccak functions, on buffers at fixed offsets of their arguments (`Buf`),
the last of which is `scratch`, kept in `esi` (which the callees keep).
A buffer's address is computed into a register (`ptrTo`): from `esi`, or
from the argument on the stack (at `[esp + 20 + 4i]`, above the frame of 16
bytes that saves the caller's registers and the return address).

Each call is a block that sets its arguments' registers, and the call in a
frame of its arguments (`callWith`): `nttC`, `mulC`, …; `hash1` and `hash2`
compute a SHA-3 or SHAKE function of one or two buffers (the Keccak state
set to zero by `zeroTop`, the buffers absorbed, the padding, and the output
squeezed). `st8` stores a byte, `copyW` copies words, and `maskA`, after a
call of `vg_mlkem_sample_ntt`, keeps the AND of the values it returned in a
word of `scratch` and sets the sampled polynomial to zero if it returned 0,
so that it is reduced in any case.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- A buffer: `len` bytes at offset `off` of argument `arg`. -/
structure Buf where
  arg : Nat
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- `r ← argument `arg` + off`: from `esi` if `arg` is `sc` (`scratch`), and from the stack
otherwise. -/
def ptrTo (sc : Nat) (r : Reg) (b : Buf) : List Instr :=
  (if b.arg = sc then Instr.mov r (.reg .esi) else .mov r (.mem (at_ .esp (20 + 4 * b.arg)))) ::
    [.alu .add r (.imm (BitVec.ofNat 32 b.off))]

/-- Zero the 50 words at `scratch + st`, through `edx`, `eax` and `ecx`. -/
def zeroTop (st : Nat) : Prog isa :=
  .seq (.block [.mov .edx (.reg .esi), .alu .add .edx (.imm (BitVec.ofNat 32 st)), .mov .eax (.imm 0),
      .mov .ecx (.imm 50)])
    (.loop (.block [.store (at_ .edx 0) .eax, .alu .add .edx (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)

/-- Store the byte `v` at `scratch + o`, through `eax`. -/
def st8 (o v : Nat) : List Instr := [.mov .eax (.imm (BitVec.ofNat 32 v)), .store8 (at_ .esi o) .al]

/-- Copy `n` words from `src` to `dst`, through `edi`, `ebp`, `eax` and `ecx`. -/
def copyW (sc : Nat) (src dst : Buf) (n : Nat) : Prog isa :=
  .seq (.block (ptrTo sc .edi src ++ ptrTo sc .ebp dst ++ ([.mov .ecx (.imm (BitVec.ofNat 32 n))] : List Instr)))
    (.loop (.block [.mov .eax (.mem (at_ .edi 0)), .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)

/-- After a call of `vg_mlkem_sample_ntt` returned `r` (1 or 0) in `eax`: the word at `scratch + ao`
ANDed with `r`, and the polynomial at `scratch + po` with `-r` (all ones, or zero). -/
def maskA (ao po : Nat) : Prog isa :=
  .seq (.block [.mov .edx (.imm 0), .alu .sub .edx (.reg .eax), .mov .ecx (.mem (at_ .esi ao)),
      .alu .and .ecx (.reg .eax), .store (at_ .esi ao) .ecx, .mov .edi (.reg .esi),
      .alu .add .edi (.imm (BitVec.ofNat 32 po)), .mov .ecx (.imm 256)])
    (.loop (.block [.mov .eax (.mem (at_ .edi 0)), .alu .and .eax (.reg .edx), .store (at_ .edi 0) .eax,
      .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)

/-! ## Calls -/

/-- `absorb(scratch + st, rate, pos, b, b.len, scratch + wk)`. -/
def absorbC (sc st wk rate pos : Nat) (b : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax ⟨sc, st, 200⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 rate)),
      .mov .edx (.imm (BitVec.ofNat 32 pos))] : List Instr) ++ ptrTo sc .ebx b ++
      ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++ ptrTo sc .edi ⟨sc, wk, 640⟩))
    (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb)

/-- `pad(scratch + st, rate, pos, sfx, scratch + wk)`. -/
def padC (sc st wk rate pos sfx : Nat) : Prog isa :=
  .seq (.block (ptrTo sc .eax ⟨sc, st, 200⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 rate)),
      .mov .edx (.imm (BitVec.ofNat 32 pos)), .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++
      ptrTo sc .edi ⟨sc, wk, 640⟩))
    (callWith [.edi, .ebx, .edx, .ecx, .eax] "vg_keccak_pad" Impl.Sha3.X86.Stream.pad)

/-- `squeeze(scratch + st, rate, 0, b, b.len, scratch + wk)`. -/
def squeezeC (sc st wk rate : Nat) (b : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax ⟨sc, st, 200⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 rate)),
      .mov .edx (.imm 0)] : List Instr) ++ ptrTo sc .ebx b ++
      ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++ ptrTo sc .edi ⟨sc, wk, 640⟩))
    (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze)

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b` into `o`. -/
def hash1 (sc st wk rate sfx : Nat) (b o : Buf) : Prog isa :=
  .seq (zeroTop st) <| .seq (absorbC sc st wk rate 0 b) <|
  .seq (padC sc st wk rate (b.len % rate) sfx) (squeezeC sc st wk rate o)

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b₁` and then `b₂` into `o`. -/
def hash2 (sc st wk rate sfx : Nat) (b₁ b₂ o : Buf) : Prog isa :=
  .seq (zeroTop st) <| .seq (absorbC sc st wk rate 0 b₁) <|
  .seq (absorbC sc st wk rate (b₁.len % rate) b₂) <|
  .seq (padC sc st wk rate ((b₁.len + b₂.len) % rate) sfx) (squeezeC sc st wk rate o)

/-- `f ← NTT(f)` (`vg_mlkem_ntt`), with the scratch `s`. -/
def nttC (sc : Nat) (f s : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ptrTo sc .ecx s)) (callWith [.ecx, .eax] "vg_mlkem_ntt" ntt)

/-- `f ← NTT⁻¹(f)` (`vg_mlkem_ntt_inv`), with the scratch `s`. -/
def nttInvC (sc : Nat) (f s : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ptrTo sc .ecx s)) (callWith [.ecx, .eax] "vg_mlkem_ntt_inv" nttInv)

/-- `h ← f ×_T g` (`vg_mlkem_multiply_ntts`), with the scratch `s`. -/
def mulC (sc : Nat) (h f g s : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax h ++ ptrTo sc .ecx f ++ ptrTo sc .edx g ++ ptrTo sc .edi s))
    (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_multiply_ntts" multiplyNTTs)

/-- `f ← f + g` (`vg_mlkem_add`). -/
def addC (sc : Nat) (f g : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ptrTo sc .ecx g)) (callWith [.ecx, .eax] "vg_mlkem_add" add)

/-- `f ← f - g` (`vg_mlkem_sub`). -/
def subC (sc : Nat) (f g : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ptrTo sc .ecx g)) (callWith [.ecx, .eax] "vg_mlkem_sub" sub)

/-- `f ← SamplePolyCBD₂(b)` (`vg_mlkem_cbd2`). -/
def cbd2C (sc : Nat) (b f : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax b ++ ptrTo sc .ecx f)) (callWith [.ecx, .eax] "vg_mlkem_cbd2" cbd2)

/-- `o ← ByteEncode₁₂(f)` (`vg_mlkem_encode12`). -/
def enc12C (sc : Nat) (f o : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ptrTo sc .ecx o)) (callWith [.ecx, .eax] "vg_mlkem_encode12" encode12)

/-- `f ← ByteDecode₁₂(b)` (`vg_mlkem_decode12`). -/
def dec12C (sc : Nat) (b f : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax b ++ ptrTo sc .ecx f)) (callWith [.ecx, .eax] "vg_mlkem_decode12" decode12)

/-- `o ← ByteEncode_d(Compress_d(f))` (`vg_mlkem_compress_encode`). -/
def ceC (sc d : Nat) (f o : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax f ++ ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo sc .edx o ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr)))
    (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_compress_encode" compressEncode)

/-- `f ← Decompress_d(ByteDecode_d(b))` (`vg_mlkem_decode_decompress`). -/
def ddC (sc d : Nat) (b f : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax b ++ ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))),
      .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo sc .edi f))
    (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_decode_decompress" decodeDecompress)

/-- `a ← SampleNTT(seed)` (`vg_mlkem_sample_ntt`), with the scratch `s`, returning 1 or 0 in `eax`. -/
def sampleC (sc : Nat) (seed a s : Buf) : Prog isa :=
  .seq (.block (ptrTo sc .eax seed ++ ptrTo sc .ecx a ++ ptrTo sc .edx s))
    (callRet [.edx, .ecx, .eax] "vg_mlkem_sample_ntt" sampleNTT)

end VG.Impl.MlKem.X86
