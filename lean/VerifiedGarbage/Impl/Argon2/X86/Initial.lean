import VerifiedGarbage.Impl.Argon2.X86.Layout
import VerifiedGarbage.Impl.Argon2.X86.Divide

/-!
# Argon2 on x86 (32-bit): the parameters and H₀

`ebp` points to the derivation's locals (`Impl/Argon2/X86/Layout.lean`).

* `parameters`: the segment length `⌊memory_cost / (4 · lanes)⌋`, by the
  fixed-time division, the lane length (four segments) and its size in
  bytes.
* `code`: H₀ (RFC 9106 §3.2), with H′'s macros (`Impl/Argon2/X86/HPrime.lean`)
  and `ebx` pointing to `scratch`: the six public parameters at
  `scratch + 768`, then LE32 of each input's length (at `scratch + 792`)
  and the input itself; the byte count (64 bits) is kept in the locals. The
  digest is copied to the first 64 bytes of the locals.
-/

namespace VG.Impl.Argon2.X86.Derive

open VG.X86
open VG.Impl.Sha512.X86 (at_)

/-- `[ebp + d]` -/
def fr (d : Nat) : Src := .mem (at_ .ebp d)

/-! ## The parameters -/

def parameters : List Instr :=
  [.mov .eax (fr (argOff lanesArg)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .store (at_ .ebp divisorOff) .eax, .mov .ecx (fr (argOff memoryCostArg))] ++
  Divide.code divisorOff ++
  [.store (at_ .ebp segLenOff) .ecx, .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .store (at_ .ebp laneLenOff) .ecx] ++
  List.replicate 10 (.alu .add .ecx (.reg .ecx)) ++ [.store (at_ .ebp strideOff) .ecx]

/-! ## H₀ -/

/-- The argument whose low 32 bits are word `j` of H₀'s header (but the
version, word 4): lanes, tag length, memory, passes, version, variant. -/
def headerArg (j : Nat) : Nat :=
  if j = 0 then lanesArg else if j = 1 then outLenArg else if j = 2 then memoryCostArg
  else if j = 3 then iterationsArg else kindArg

def headerSlot (j : Nat) : List Instr :=
  if j = 4 then [.mov .eax (.imm 0x13), .store (at_ .ebx (768 + 4 * j)) .eax]
  else [.mov .eax (fr (argOff (headerArg j))), .store (at_ .ebx (768 + 4 * j)) .eax]

def header : List Instr := (List.range 6).flatMap headerSlot

/-- Point `ebx` to `scratch`, start an unkeyed 64-byte hash, and absorb the
header; the byte count is 24. -/
def start : Prog isa :=
  .seq (.block [.mov .ebx (fr (argOff scratchArg)), .mov .edx (.imm 64)])
  (.seq HPrime.init
  (.seq (.block header)
  (.seq (HPrime.absorbFixed 768 24)
    (.block [.mov .eax (.imm 24), .store (at_ .ebp countLoOff) .eax, .mov .eax (.imm 0),
      .store (at_ .ebp countHiOff) .eax]))))

/-- Add `src` to the 64-bit byte count. -/
def addCount (src : Src) : List Instr :=
  [.mov .ecx (fr countLoOff), .mov .edx (fr countHiOff), .alu .add .ecx src, .alu .adc .edx (.imm 0),
    .store (at_ .ebp countLoOff) .ecx, .store (at_ .ebp countHiOff) .edx]

/-- Absorb LE32(length) and the input (`ptr`, `len` are its arguments). -/
def absorb (ptr len : Nat) : Prog isa :=
  .seq (.block [.mov .eax (fr (argOff len)), .store (at_ .ebx 792) .eax, .mov .ecx (fr countLoOff),
      .mov .edx (fr countHiOff), .mov .esi (.reg .ebx), .alu .add .esi (.imm 792), .mov .edi (.imm 4)])
  (.seq HPrime.update
  (.seq (.block (addCount (.imm 4) ++
      [.mov .esi (fr (argOff ptr)), .mov .edi (fr (argOff len))]))
  (.seq HPrime.update (.block (addCount (fr (argOff len)))))))

/-- Copy the digest's word `j` to the locals. -/
def copyWord (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebx (768 + 4 * j))), .store (at_ .ebp (4 * j)) .eax]

/-- Finalize, and copy H₀ to the locals. -/
def finish : Prog isa :=
  .seq (.block [.mov .ecx (fr countLoOff), .mov .edx (fr countHiOff)])
    (.seq HPrime.finalize (.block ((List.range 16).flatMap copyWord)))

def code : Prog isa :=
  .seq start
  (.seq (absorb passwordArg passwordLenArg)
  (.seq (absorb saltArg saltLenArg)
  (.seq (absorb secretArg secretLenArg)
  (.seq (absorb adArg adLenArg) finish))))

end VG.Impl.Argon2.X86.Derive
