import VerifiedGarbage.Impl.TripleDes.X86_64.Bitsliced
import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocX

/-!
# Bitsliced Triple DES ECB on x86-64 with SSE2

As `Bitsliced`, but on 128 blocks at a time, in 128-bit words, while at
least 128 blocks are left; the blocks left after that go through the
64-block code (`Bitslice.ecb`).

* The state of 128 blocks (64 words of 16 bytes) is the 1024 bytes of the
  blocks themselves: the 16 bytes at `rsi + 16 i` hold blocks `2i` and
  `2i + 1` as little-endian quadwords, and each quadword lane `q` of the
  64 words is transposed in place as `Bitsliced` transposes its 64 words,
  with quadword shifts. Word `j`'s bit `64 q + i` is then bit `j` of block
  `2i + q`.
* Rounds are those of `Bitsliced`, in `xmm` registers, with the circuits'
  spills in 16-byte slots of the scratch buffer: the key bit masks come
  from `rax` through `rbx` (`add`, `sbb`), broadcast with `movq` and
  `punpcklqdq`; `xmm15` holds all ones for the circuits' NOTs.
* Everything the loops count is in registers (`r8` the key pointer, `r9`
  its step, `r10` the pairs of rounds and `r11` the passes left), and
  `rbx`, the only callee-saved register used, is saved in the scratch
  buffer.
-/

namespace VG.Impl.TripleDes.X86_64.BitsliceSse

open VG.X86_64 VG.Impl.TripleDes.Bitslice
open VG.Impl.TripleDes.X86_64.Bitslice (passKey swapMask)
open VG.Spec.TripleDes (Direction)

/-- State word `j`, at `rsi + 16 j`. -/
def word (j : Nat) : MemOp := { base := .rsi, disp := ((16 * j : Nat) : Int) }

def xload (d : XReg) (m : MemOp) : Instr := .movdquLoad d m
def xstore (m : MemOp) (r : XReg) : Instr := .movdquStore m r

/-- Where `rbx` is saved: the last 8 bytes of the scratch buffer. -/
def rbxSave : MemOp := { base := .rcx, disp := 1016 }

/-- The spill slots the circuits may use. -/
def spills : Nat := 16

/-! ## S-boxes -/

def inRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5]
def outRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]
def freeRegs : List XReg := [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14]
def inReg (i : Nat) : XReg := inRegs.getD i .xmm0
def outReg (i : Nat) : XReg := outRegs.getD i .xmm0

/-- All ones, for the circuits' NOTs. -/
def ones : XReg := .xmm15
/-- The key bit mask. -/
def maskReg : XReg := .xmm14

def sboxCode (j : Nat) : List Instr :=
  compile (box j) ((List.range 6).map fun i => (i, inReg i))
    ((List.range 4).map fun i => ((outputs j).getD i 0, outReg i)) freeRegs (List.range spills) ones

/-- S-box `j`'s input `i`: the next key bit, as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx), .xop (.movq maskReg .rbx),
   xbin .punpcklqdq maskReg maskReg, xload (inReg i) (word (readWord ρ (eBit (inBit j i)))),
   xbin .pxor (inReg i) maskReg]

/-- S-box `j`'s inputs, from the most significant (whose key bit is next). -/
def inputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 6).reverse.flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [xload maskReg (word (writeWord ρ (outBit j i))), xbin .pxor (outReg i) maskReg,
     xstore (word (writeWord ρ (outBit j i))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds -/

/-- Load the round key into `rax`, its bit 47 at the top, and advance the
key pointer. -/
def keyLoad : List Instr :=
  [.mov .rax (.mem { base := .r8, disp := 0 }), .alu .add .r8 (.reg .r9), .shift .ror .rax 48]

def round (ρ : Role) : List Instr := keyLoad ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair : List Instr := round .ba ++ round .ab ++ [.alu .sub .r10 (.imm 1)]

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [xload .xmm0 (word (lWord q)), xload .xmm1 (word (rWord q)), xstore (word (lWord q)) .xmm1,
     xstore (word (rWord q)) .xmm0]

/-- Point at the pass's first key, with its step. -/
def passKeyCode (d : Direction) (p : Nat) : List Instr :=
  [.mov .r8 (.reg .rdi), .alu .add .r8 (.imm (BitVec.ofNat 32 (passKey d p).1)),
   .mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))]

/-- Choose the pass's first key and step by the pass count, and count 8 pairs. -/
def passStart (d : Direction) : Prog isa :=
  .seq (.block [.alu .cmp .r11 (.imm 3)])
    (.seq (.ite .e (.block (passKeyCode d 3))
      (.seq (.block [.alu .cmp .r11 (.imm 2)])
        (.ite .e (.block (passKeyCode d 2)) (.block (passKeyCode d 1)))))
    (.block [.mov .r10 (.imm 8)]))

def pass (d : Direction) : Prog isa :=
  .seq (passStart d) (.seq (.loop (.block roundPair) .ne)
    (.block (swapHalves ++ [.alu .sub .r11 (.imm 1)])))

/-! ## Transposition -/

/-- Broadcast a 64-bit constant to every quadword of `d`. -/
def bcast (d : XReg) (v : BitVec 64) : List Instr :=
  [.movImm64 .rbx v, .xop (.movq d .rbx), xbin .punpcklqdq d d]

/-- Exchange the bits `p + s` of `a` and `p` of `b` in every quadword lane
(`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : XReg) (s : Nat) : List Instr :=
  [xbin .movdqa t a, .xop (.shift .psrlq t (BitVec.ofNat 8 s)), xbin .pxor t b, xbin .pand t m,
   xbin .pxor b t, .xop (.shift .psllq t (BitVec.ofNat 8 s)), xbin .pxor a t]

def groupRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]
def groupReg (k : Nat) : XReg := groupRegs.getD k .xmm0

/-- Three stages on eight words, the state words `w k`: the stage of shift
`unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1. -/
def group (w : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => xload (groupReg k) (word (w k))) ++
  ([(4, XReg.xmm13), (2, .xmm14), (1, .xmm15)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .xmm8 m (unit * d)) ++
  (List.range 8).map (fun k => xstore (word (w k)) (groupReg k))

def masks (unit : Nat) : List Instr :=
  bcast .xmm13 (swapMask (4 * unit)) ++ bcast .xmm14 (swapMask (2 * unit)) ++
  bcast .xmm15 (swapMask unit)

/-- Transpose each quadword lane of the 64 state words in place: stages
32, 16, 8, then 4, 2, 1. -/
def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

/-- Three passes on 128 blocks, then the next 128. -/
def batch (d : Direction) : Prog isa :=
  .seq (.block (transpose ++ bcast ones (BitVec.allOnes 64) ++ [.mov .r11 (.imm 3)]))
    (.seq (.loop (pass d) .ne)
      (.block (transpose ++
        [.alu .add .rsi (.imm 1024), .alu .sub .rdx (.imm 128), .alu .cmp .rdx (.imm 128)])))

/-- Batches of 128 blocks while there are that many. -/
def wide (d : Direction) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 128)])
    (.ite .b (.block [])
      (.seq (.block [.store rbxSave .rbx])
        (.seq (.loop (batch d) .ae)
          (.block [.mov .rbx (.mem rbxSave)]))))

def ecb (d : Direction) : Prog isa := .seq (wide d) (Bitslice.ecb d)

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.BitsliceSse
