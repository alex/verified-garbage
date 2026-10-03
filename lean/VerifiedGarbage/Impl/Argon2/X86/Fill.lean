import VerifiedGarbage.Impl.Argon2.X86.MemoryInit
import VerifiedGarbage.Impl.Argon2.X86.Compress
import VerifiedGarbage.Spec.Argon2.Contract

/-!
# Argon2 on x86 (32-bit): filling the memory

The pass, lane, slice and index are in the locals (`ebp`), so every register
but `ebp` and `esp` is free within a block's update (`fillBlock`):

* the random word (J₁, J₂) is read from the previous block (data-dependent
  addressing) or from the cached address block in `scratch[6144, 7168)`,
  which two calls of `vg_argon2_compress` regenerate every 128 blocks of a
  segment (`scratch[0, 4096)` is G's working space, `[4096, 5120)` its output,
  `[5120, 6144)` the input block and `[7168, 8192)` the zero block);
* the reference lane is J₂ modulo the lane count (the fixed-time division), but
  the current lane in the first slice of the first pass;
* the reference column maps J₁ into the window of eligible blocks
  (RFC 9106 §3.4.2), choosing between the windows of the current lane and of
  another one with a mask rather than a branch;
* G of the previous and reference blocks goes to `scratch[4096, 5120)`, and is
  copied to the current block (first pass) or XORed into it.

Branches and addresses depend only on the public parameters and loop
position, but for the addresses of the previous block's first word (public:
its position is) and of the reference block, which data-dependent addressing
permits to leak.
-/

namespace VG.Impl.Argon2.X86.Derive

open VG.X86
open VG.Impl.Sha512.X86 (at_)

/-- `++`, grouping to the right (see `Impl/Blake2/X86/CompressB.lean`). -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `[ebp + d] := r` -/
def st (d : Nat) (r : Reg) : Instr := .store (at_ .ebp d) r

/-! ## Block addresses -/

/-- `eax := memory + 1024 · (eax · laneLen + ecx)`: block `ecx` of lane `eax`. -/
def blockAddr : List Instr :=
  [.mov .edx (fr laneLenOff), .mul .edx, .alu .add .eax (.reg .ecx)] +++
    List.replicate 10 (.alu .add .eax (.reg .eax)) +++ [.alu .add .eax (fr (argOff memoryArg))]

/-- `ecx :=` the current column, `slice · segLen + index`. -/
def column : List Instr :=
  [.mov .eax (fr sliceOff), .mov .edx (fr segLenOff), .mul .edx, .alu .add .eax (fr indexOff),
    .mov .ecx (.reg .eax)]

/-- `ecx :=` the column before `ecx`, cyclically. -/
def prevColumn : Prog isa :=
  .seq (.block [.alu .cmp .ecx (.imm 0)])
    (.seq (.ite .e (.block [.mov .ecx (fr laneLenOff)]) (.block [])) (.block [.alu .sub .ecx (.imm 1)]))

/-- `eax :=` the address of the previous block. -/
def prevPointer : Prog isa :=
  .seq (.block column) (.seq prevColumn (.block (.mov .eax (fr laneOff) :: blockAddr)))

/-! ## The random word -/

/-- `ecx := 1` for data-independent addressing, else `0`, and ZF if `0`:
Argon2i, or Argon2id in the first two slices of the first pass. -/
def addressMode : List Instr :=
  [.mov .eax (fr (argOff kindArg)),
    .mov .ecx (.reg .eax), .alu .xor .ecx (.imm 1), .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx),
    .mov .edx (.reg .eax), .alu .xor .edx (.imm 2), .alu .cmp .edx (.imm 1), .alu .sbb .edx (.reg .edx),
    .mov .eax (fr passOff), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .and .edx (.reg .eax),
    .mov .eax (fr sliceOff), .alu .cmp .eax (.imm 2), .alu .sbb .eax (.reg .eax), .alu .and .edx (.reg .eax),
    .alu .or .ecx (.reg .edx), .alu .and .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

/-- Data-dependent addressing: J₁, J₂ are the first word of the previous block. -/
def dependentWord : Prog isa :=
  .seq prevPointer
    (.block [.mov .edx (.mem (at_ .eax 0)), st j1Off .edx, .mov .edx (.mem (at_ .eax 4)), st j2Off .edx])

/-- `edx := scratch + d` -/
def scratchAt (d : Nat) : List Instr :=
  [.mov .edx (fr (argOff scratchArg)), .alu .add .edx (.imm (BitVec.ofNat 32 d))]

/-- Zero `scratch[d, d + 1024)`. -/
def clearAt (d : Nat) : List Instr :=
  scratchAt d +++ .mov .eax (.imm 0) :: (List.range 256).map fun k => .store (at_ .edx (4 * k)) .eax

/-- The words of the address-generation input block (its other words are
zero): pass, lane, slice, blocks, passes, type and counter (§3.4.1.2). -/
def addressHeader : List Instr :=
  [.mov .edx (fr (argOff scratchArg)),
    .mov .eax (fr passOff), .store (at_ .edx 5120) .eax,
    .mov .eax (fr laneOff), .store (at_ .edx 5128) .eax,
    .mov .eax (fr sliceOff), .store (at_ .edx 5136) .eax,
    .mov .eax (fr (argOff blocksArg)), .store (at_ .edx 5144) .eax,
    .mov .eax (fr (argOff iterationsArg)), .store (at_ .edx 5152) .eax,
    .mov .eax (fr (argOff kindArg)), .store (at_ .edx 5160) .eax,
    .mov .eax (fr counterOff), .store (at_ .edx 5168) .eax]

def compressName : String := Spec.Argon2.compressApi.name

/-- `compress(eax, esi, ecx, edx)`, its arguments pushed last to first. -/
def compressCall : Prog isa :=
  .frame (.push [.edx, .ecx, .esi, .eax]) (.call compressName Impl.Argon2.X86.compress) (.pop .eax 4)

/-- G(`scratch + x`, `scratch + y`) to `scratch + out`. -/
def stage (x y out : Nat) : Prog isa :=
  .seq (.block [.mov .edx (fr (argOff scratchArg)), .mov .eax (.reg .edx),
      .alu .add .eax (.imm (BitVec.ofNat 32 x)), .mov .esi (.reg .edx),
      .alu .add .esi (.imm (BitVec.ofNat 32 y)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm (BitVec.ofNat 32 out))])
    compressCall

/-- The address block: G(0, G(0, input)). -/
def addressCalls : Prog isa :=
  .seq (.block (clearAt 5120 +++ clearAt 7168 +++ addressHeader))
    (.seq (stage 7168 5120 4096) (stage 7168 4096 6144))

/-- `eax :=` the counter of the address block for the index; ZF if it is the
cached one. -/
def cacheCheck : List Instr :=
  [.mov .eax (fr indexOff), .shift .shr .eax 7, .alu .add .eax (.imm 1), .alu .cmp .eax (fr counterOff)]

/-- J₁, J₂: word `index mod 128` of the address block. -/
def cacheWord : List Instr :=
  [.mov .eax (fr indexOff), .alu .and .eax (.imm 127), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (fr (argOff scratchArg)),
    .mov .edx (.mem (at_ .eax 6144)), st j1Off .edx, .mov .edx (.mem (at_ .eax 6148)), st j2Off .edx]

/-- Data-independent addressing, regenerating the address block when the
index enters a new group of 128. -/
def addressCache : Prog isa :=
  .seq (.block cacheCheck)
    (.seq (.ite .e (.block []) (.seq (.block [st counterOff .eax]) addressCalls)) (.block cacheWord))

def randomSource : Prog isa := .seq (.block addressMode) (.ite .e dependentWord addressCache)

/-! ## The reference block -/

/-- The reference lane: J₂ mod lanes, or the current lane in the first slice of
the first pass. -/
def refLane : Prog isa :=
  .seq (.block (.mov .ecx (fr j2Off) :: Divide.code (argOff lanesArg) +++
      [st refLaneOff .eax, .mov .eax (fr passOff), .alu .or .eax (fr sliceOff)]))
    (.ite .e (.block [.mov .eax (fr laneOff), st refLaneOff .eax]) (.block []))

/-- Where the window starts: 0 in the first pass, else the next slice (0 after
the last one). -/
def refStart : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), st startOff .eax, .mov .ecx (fr passOff), .alu .cmp .ecx (.imm 0)])
    (.ite .e (.block [])
      (.seq (.block [.mov .ecx (fr sliceOff), .alu .cmp .ecx (.imm 3)])
        (.ite .e (.block [])
          (.block [.mov .eax (fr sliceOff), .alu .add .eax (.imm 1), .mov .edx (fr segLenOff), .mul .edx,
            st startOff .eax]))))

/-- `eax :=` the blocks before the current segment that a reference may use:
`slice · segLen` in the first pass, three segments after it. -/
def countBase : Prog isa :=
  .seq (.block [.mov .ecx (fr passOff), .alu .cmp .ecx (.imm 0)])
    (.ite .e (.block [.mov .eax (fr sliceOff), .mov .edx (fr segLenOff), .mul .edx])
      (.block [.mov .eax (fr laneLenOff), .alu .sub .eax (fr segLenOff)]))

/-- The window's size: `base + index - 1` blocks in the current lane, `base`
(less one at index 0) in another one, chosen by a mask. -/
def countSelect : List Instr :=
  [.mov .ecx (.reg .eax), .alu .add .ecx (fr indexOff), .alu .sub .ecx (.imm 1),
    .mov .edx (fr indexOff), .alu .sub .edx (.imm 1), .alu .sbb .edx (.reg .edx), .alu .add .eax (.reg .edx),
    .mov .edx (fr refLaneOff), .alu .xor .edx (fr laneOff), .alu .sub .edx (.imm 1),
    .alu .sbb .edx (.reg .edx),
    .alu .xor .ecx (.reg .eax), .alu .and .ecx (.reg .edx), .alu .xor .eax (.reg .ecx), st countOff .eax]

/-- `eax := count - 1 - ⌊count · ⌊J₁² / 2³²⌋ / 2³²⌋`. -/
def relative : List Instr :=
  [.mov .eax (fr j1Off), .mul .eax, .mov .eax (.reg .edx), .mov .ecx (fr countOff), .mul .ecx,
    .mov .eax (.reg .ecx), .alu .sub .eax (.imm 1), .alu .sub .eax (.reg .edx)]

/-- `eax := (start + eax) mod laneLen`, by one masked subtraction. -/
def wrap : List Instr :=
  [.alu .add .eax (fr startOff), .alu .sub .eax (fr laneLenOff), .alu .sbb .edx (.reg .edx),
    .alu .and .edx (fr laneLenOff), .alu .add .eax (.reg .edx)]

/-- The reference block's address, to `[ebp + tmpOff]`. -/
def refPointer : List Instr :=
  [.mov .ecx (.reg .eax), .mov .eax (fr refLaneOff)] +++ blockAddr +++ [st tmpOff .eax]

/-- The current block's address, to `[ebp + curOff]`. -/
def curPointer : List Instr := column +++ .mov .eax (fr laneOff) :: blockAddr +++ [st curOff .eax]

def reference : Prog isa :=
  .seq refLane (.seq refStart (.seq countBase
    (.block (countSelect +++ relative +++ wrap +++ refPointer +++ curPointer))))

/-! ## The new block -/

/-- G(previous, reference) to `scratch[4096, 5120)`. -/
def fillCompress : Prog isa :=
  .seq prevPointer
    (.seq (.block [.mov .esi (fr tmpOff), .mov .edx (fr (argOff scratchArg)), .mov .ecx (.reg .edx),
      .alu .add .ecx (.imm 4096)]) compressCall)

/-- 32-bit word `k` from `esi` to `edi`, XORed into the old one if `xorOld`. -/
def writeWord (xorOld : Bool) (k : Nat) : List Instr :=
  .mov .eax (.mem (at_ .esi (4 * k))) ::
    ((if xorOld then [.alu .xor .eax (.mem (at_ .edi (4 * k)))] else []) +++
      [.store (at_ .edi (4 * k)) .eax])

def writeBlock (xorOld : Bool) : List Instr := (List.range 256).flatMap (writeWord xorOld)

/-- The new block to the current one: copied in the first pass, XORed later. -/
def fillWrite : Prog isa :=
  .seq (.block [.mov .esi (fr (argOff scratchArg)), .alu .add .esi (.imm 4096), .mov .edi (fr curOff),
      .mov .eax (fr passOff), .alu .cmp .eax (.imm 0)])
    (.ite .e (.block (writeBlock false)) (.block (writeBlock true)))

def fillBlock : Prog isa := .seq randomSource (.seq reference (.seq fillCompress fillWrite))

/-! ## The loops -/

/-- `[ebp + d] += 1`, compared with `src`. -/
def advance (d : Nat) (src : Src) : List Instr :=
  [.mov .eax (fr d), .alu .add .eax (.imm 1), st d .eax, .alu .cmp .eax src]

/-- `[ebp + d] := v` -/
def setLocal (d : Nat) (v : BitVec 32) : List Instr := [.mov .eax (.imm v), st d .eax]

/-- The first index of a segment: 2 in the first slice of the first pass
(whose first two blocks are initialized), else 0; and a new address block. -/
def segmentStart : Prog isa :=
  .seq (.block (setLocal counterOff 0 ++ [.mov .eax (fr passOff), .alu .or .eax (fr sliceOff)]))
    (.ite .e (.block (setLocal indexOff 2)) (.block (setLocal indexOff 0)))

def segment : Prog isa :=
  .seq segmentStart
    (.seq (.block [.mov .eax (fr indexOff), .alu .cmp .eax (fr segLenOff)])
      (.ite .b (.loop (.seq fillBlock (.block (advance indexOff (fr segLenOff)))) .b) (.block [])))

def lanesLoop : Prog isa :=
  .seq (.block (setLocal laneOff 0))
    (.loop (.seq segment (.block (advance laneOff (fr (argOff lanesArg))))) .b)

def slicesLoop : Prog isa :=
  .seq (.block (setLocal sliceOff 0)) (.loop (.seq lanesLoop (.block (advance sliceOff (.imm 4)))) .b)

def passesLoop : Prog isa :=
  .seq (.block (setLocal passOff 0))
    (.loop (.seq slicesLoop (.block (advance passOff (fr (argOff iterationsArg))))) .b)

end VG.Impl.Argon2.X86.Derive
