import VerifiedGarbage.Impl.Blake2.X86.Stream
import VerifiedGarbage.Impl.Blake2.X86.CompressB

/-!
# Argon2 H′ on x86 (32-bit)

`vg_argon2_hprime(input, input_len, out, out_len, scratch)`, cdecl: the
arguments are at `[esp + 4]` … `[esp + 20]`. Every hash is computed by the
x86 BLAKE2b streaming functions (`vg_blake2b_init`, `_update`, `_finalize`),
each called with its arguments pushed in a frame of their own.

`ebx` holds `scratch` throughout; its first bytes are laid out as:
* `[0, 192)`: the BLAKE2b state;
* `[192, 768)`: the BLAKE2b functions' scratch;
* `[768, 832)`: the digest;
* `[832, 836)`: the length prefix LE32(`out_len`);
* `[840, 852)`: the caller's `ebx`, `esi` and `edi`;
* `[856, 864)`: where the next output byte goes, and how many are left.
The calls of the streaming functions are made with `ebx`, and only the
registers they preserve (`ebx`, `esi`, `edi`, `ebp`), so `ebp` is never
written: a caller may keep a frame pointer in it across H′'s macros
(`init`, `update`, `finalize`).
The rest of `scratch` is not used. Only `esp`, the pointers and the lengths
affect branches and addresses.
-/

namespace VG.Impl.Argon2.X86.HPrime

open VG.X86
open VG.Impl.Sha512.X86 (at_)

/-- Where the caller's registers are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 840), (.esi, 844), (.edi, 848)]

/-- The output pointer and the output bytes left. -/
def outOff : Nat := 856
def leftOff : Nat := 860

def initName : String := "vg_blake2b_init"
def updateName : String := "vg_blake2b_update"
def finalizeName : String := "vg_blake2b_finalize"

def initCode : Prog isa := Impl.Blake2.X86.Stream.init Spec.Blake2.b
def updateCode : Prog isa :=
  Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress
def finalizeCode : Prog isa :=
  Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress

/-- Save the caller's registers in `scratch`, point `ebx` to it, and keep
the output pointer, the output length and its prefix there. -/
def setup : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .ebx (.reg .eax),
    .mov .eax (.mem (at_ .esp 12)), .store (at_ .ebx outOff) .eax,
    .mov .eax (.mem (at_ .esp 16)), .store (at_ .ebx leftOff) .eax, .store (at_ .ebx 832) .eax]

/-- Restore the caller's registers, `ebx` last. -/
def restore : List Instr :=
  [.mov .edi (.mem (at_ .ebx 848)), .mov .esi (.mem (at_ .ebx 844)), .mov .ebx (.mem (at_ .ebx 840))]

/-- `init(ebx, edx, ebx, 0)`: an unkeyed hash with the digest length in `edx`. -/
def init : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .mov .ecx (.reg .ebx)])
    (.frame (.push [.eax, .ecx, .edx, .ebx]) (.call initName initCode) (.pop .eax 4))

/-- `update(ebx, ecx:edx, esi, edi, ebx + 192)`: the byte count in `ecx`
(low) and `edx` (high), the data at `esi`, its length in `edi`. -/
def update : Prog isa :=
  .seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192)])
    (.frame (.push [.eax, .edi, .esi, .edx, .ecx, .ebx]) (.call updateName updateCode) (.pop .eax 6))

/-- `finalize(ebx, ecx:edx, ebx + 768, ebx + 192)`: the byte count in `ecx`
(low) and `edx` (high); the digest goes to `scratch[768, 832)`. -/
def finalize : Prog isa :=
  .seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 192), .mov .esi (.reg .ebx),
      .alu .add .esi (.imm 768)])
    (.frame (.push [.eax, .esi, .edx, .ecx, .ebx]) (.call finalizeName finalizeCode) (.pop .eax 5))

/-- Absorb `size` bytes of `scratch` at `offset` into an empty hash state. -/
def absorbFixed (offset size : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .mov .edx (.imm 0), .mov .esi (.reg .ebx),
      .alu .add .esi (.imm (BitVec.ofNat 32 offset)), .mov .edi (.imm (BitVec.ofNat 32 size))])
    update

/-- The first digest has `min(out_len, 64)` bytes. -/
def chooseLength : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .ebx leftOff)), .alu .cmp .edx (.imm 65)])
    (.ite .b (.block []) (.block [.mov .edx (.imm 64)]))

/-- Absorb the caller's input after the four-byte length prefix. -/
def absorbInput : Prog isa :=
  .seq (.block [.mov .ecx (.imm 4), .mov .edx (.imm 0), .mov .esi (.mem (at_ .esp 4)),
      .mov .edi (.mem (at_ .esp 8))])
    update

/-- Finish the hash of the prefix and the input: `4 + input_len` bytes, a
64-bit count. -/
def finishInput : Prog isa :=
  .seq (.block [.mov .ecx (.mem (at_ .esp 8)), .mov .edx (.imm 0), .alu .add .ecx (.imm 4),
      .alu .adc .edx (.imm 0)])
    finalize

/-- H(min(out_len, 64), LE32(out_len) || input). -/
def first : Prog isa :=
  .seq chooseLength (.seq init (.seq (absorbFixed 832 4) (.seq absorbInput finishInput)))

/-- Hash the 64-byte digest, with the new digest length in `edx`. -/
def next : Prog isa :=
  .seq init (.seq (absorbFixed 768 64)
    (.seq (.block [.mov .ecx (.imm 64), .mov .edx (.imm 0)]) finalize))

/-- Copy `esi > 0` digest bytes to the output, advancing the output pointer:
BLAKE2's loop copying bytes (`Impl.Blake2.X86.Stream.copyLoop`), with its
destination offset `0`. -/
def copy : Prog isa :=
  .seq (.block [.mov .edx (.reg .ebx), .alu .add .edx (.imm 768), .mov .edi (.mem (at_ .ebx outOff))])
    (.seq (Impl.Blake2.X86.Stream.copyLoop 0 .edx .edi .esi .al) (.block [.store (at_ .ebx outOff) .edi]))

/-- Emit one 32-byte prefix, and take it off the bytes left. -/
def emitPrefix : Prog isa :=
  .seq (.block [.mov .esi (.imm 32)])
    (.seq copy (.block [.mov .eax (.mem (at_ .ebx leftOff)), .alu .sub .eax (.imm 32),
      .store (at_ .ebx leftOff) .eax]))

/-- Compare the bytes left with 65. -/
def cmpLeft : List Instr := [.mov .eax (.mem (at_ .ebx leftOff)), .alu .cmp .eax (.imm 65)]

/-- Emit further prefixes while more than 64 output bytes are left. -/
def chain : Prog isa :=
  .loop (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) .ae

/-- The prefixes of a long output and the digest after them. -/
def extendDigest : Prog isa :=
  .seq emitPrefix
  (.seq (.block cmpLeft)
  (.seq (.ite .b (.block []) chain)
  (.seq (.block [.mov .edx (.mem (at_ .ebx leftOff))]) next)))

def copyRemaining : Prog isa := .seq (.block [.mov .esi (.mem (at_ .ebx leftOff))]) copy

/-- Emit H′ from its first digest, extending it for outputs over 64 bytes. -/
def finishOutput : Prog isa :=
  .seq (.block cmpLeft) (.seq (.ite .b (.block []) extendDigest) copyRemaining)

/-- H′, including the short-output case and the final 33–64-byte hash. -/
def code : Prog isa :=
  .seq (.block setup) (.seq first (.seq finishOutput (.block restore)))

end VG.Impl.Argon2.X86.HPrime
