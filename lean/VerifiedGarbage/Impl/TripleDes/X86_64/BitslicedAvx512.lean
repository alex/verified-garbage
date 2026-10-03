import VerifiedGarbage.Impl.TripleDes.X86_64.Bitsliced
import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAllocZ

/-!
# Bitsliced Triple DES ECB on x86-64 with AVX-512

`vg_triple_des_ecb_{en,de}crypt_avx512(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`.

As `BitslicedAvx2`, but on 512 blocks at a time, in 512-bit words, while at
least 512 blocks are left; the blocks left after that go through the
64-block code (`Bitslice.ecb`).

* The state of 512 blocks (64 words of 64 bytes) is the 4096 bytes of the
  blocks themselves: the 64 bytes at `rsi + 64 i` hold blocks `8i … 8i + 7`,
  and each of the eight quadword lanes of the 64 words is transposed in
  place. Word `j`'s bit `64 q + i` is then bit `j` of block `8i + q`.
* The S-box circuits are fused into functions of up to three words
  (`BitsliceAllocZ`), most of them one `vpternlogd`.
* Everything the loops count is in registers, and `rbx` is saved in the
  scratch buffer, as in `BitslicedAvx2`.
-/

namespace VG.Impl.TripleDes.X86_64.BitsliceAvx512

open VG.X86_64 VG.Impl.TripleDes.Bitslice
open VG.Impl.TripleDes.X86_64.Bitslice (passKey swapMask)
open VG.Spec.TripleDes (Direction)

/-- State word `j`, at `rsi + 64 j`. -/
def word (j : Nat) : MemOp := { base := .rsi, disp := ((64 * j : Nat) : Int) }

def zload (d : XReg) (m : MemOp) : Instr := .vmovdqu32Load d m
def zstore (m : MemOp) (r : XReg) : Instr := .vmovdqu32Store m r

/-- Where `rbx` is saved: the last 8 bytes of the scratch buffer. -/
def rbxSave : MemOp := { base := .rcx, disp := 1016 }

/-- The spill slots the circuits may use. -/
def spills : Nat := 8

/-! ## S-boxes -/

def inRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5]
def outRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]
def freeRegs : List XReg :=
  [.xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]
def inReg (i : Nat) : XReg := inRegs.getD i .xmm0
def outReg (i : Nat) : XReg := outRegs.getD i .xmm0

/-- The key bit mask. -/
def maskReg : XReg := .xmm15

def sboxCode (j : Nat) : List Instr :=
  compile (box j) ((List.range 6).map fun i => (i, inReg i))
    ((List.range 4).map fun i => ((outputs j).getD i 0, outReg i)) freeRegs (List.range spills)

/-- S-box `j`'s input `i`: the next key bit, as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.alu .add .rax (.reg .rax), .alu .sbb .rbx (.reg .rbx), .vop (.vmovq maskReg .rbx),
   .zop (.vpbroadcastq maskReg maskReg), zload (inReg i) (word (readWord ρ (eBit (inBit j i)))),
   zbin .vpxord (inReg i) (inReg i) maskReg]

def inputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 6).reverse.flatMap (inputStep ρ j)

def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [zload maskReg (word (writeWord ρ (outBit j i))), zbin .vpxord (outReg i) (outReg i) maskReg,
     zstore (word (writeWord ρ (outBit j i))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds -/

def keyLoad : List Instr :=
  [.mov .rax (.mem { base := .r8, disp := 0 }), .alu .add .r8 (.reg .r9), .shift .ror .rax 48]

def round (ρ : Role) : List Instr := keyLoad ++ (List.range 8).flatMap (sboxStep ρ)

def roundPair : List Instr := round .ba ++ round .ab ++ [.alu .sub .r10 (.imm 1)]

def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [zload .xmm0 (word (lWord q)), zload .xmm1 (word (rWord q)), zstore (word (lWord q)) .xmm1,
     zstore (word (rWord q)) .xmm0]

def passKeyCode (d : Direction) (p : Nat) : List Instr :=
  [.mov .r8 (.reg .rdi), .alu .add .r8 (.imm (BitVec.ofNat 32 (passKey d p).1)),
   .mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))]

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

def bcast (d : XReg) (v : BitVec 64) : List Instr :=
  [.movImm64 .rbx v, .vop (.vmovq d .rbx), .zop (.vpbroadcastq d d)]

def swapBits (a b t m : XReg) (s : Nat) : List Instr :=
  [.zop (.vshift .vpsrlq t a (BitVec.ofNat 8 s)), zbin .vpxord t t b, zbin .vpandq t t m,
   zbin .vpxord b b t, .zop (.vshift .vpsllq t t (BitVec.ofNat 8 s)), zbin .vpxord a a t]

def groupRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]
def groupReg (k : Nat) : XReg := groupRegs.getD k .xmm0

def group (w : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => zload (groupReg k) (word (w k))) ++
  ([(4, XReg.xmm13), (2, .xmm14), (1, .xmm15)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .xmm8 m (unit * d)) ++
  (List.range 8).map (fun k => zstore (word (w k)) (groupReg k))

def masks (unit : Nat) : List Instr :=
  bcast .xmm13 (swapMask (4 * unit)) ++ bcast .xmm14 (swapMask (2 * unit)) ++
  bcast .xmm15 (swapMask unit)

def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

def batch (d : Direction) : Prog isa :=
  .seq (.block (transpose ++ [.mov .r11 (.imm 3)]))
    (.seq (.loop (pass d) .ne)
      (.block (transpose ++
        [.alu .add .rsi (.imm 4096), .alu .sub .rdx (.imm 512), .alu .cmp .rdx (.imm 512)])))

def wide (d : Direction) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 512)])
    (.ite .b (.block [])
      (.seq (.block [.store rbxSave .rbx])
        (.seq (.loop (batch d) .ae)
          (.block [.mov .rbx (.mem rbxSave), .vop .vzeroupper]))))

def ecb (d : Direction) : Prog isa := .seq (wide d) (Bitslice.ecb d)

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.BitsliceAvx512
