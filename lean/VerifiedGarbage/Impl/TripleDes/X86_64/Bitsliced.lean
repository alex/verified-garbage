import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Impl.TripleDes.X86_64.BitsliceAlloc

/-!
# Bitsliced Triple DES ECB on x86-64

`vg_triple_des_ecb_{en,de}crypt(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`.

Constant-time Triple DES on 64 blocks at a time, bitsliced in 64-bit words
(Biham's bitslicing; the S-box circuits are Rusakov's, `BitsliceCircuit`).
Everything lives in the 128 slots of the scratch buffer (`rcx`, which no
instruction writes): the circuits' spills in slots 0–5, the 64 state words
in slots 8–71 (`stSlot`), then the callee-saved registers, the arguments and
the loop state.

* Up to 64 blocks are copied into the state words and transposed in place,
  so that word `j` holds bit `j` of every block (`BitsliceLayout`); IP only
  renames words. The words of the other lanes hold whatever they held:
  their results are not stored.
* A round shifts the round key (in `r15`, its bit 47 at the top) out a bit
  at a time: `add r15, r15` moves the next key bit into CF and `sbb` makes
  an all-zero or all-one mask of it, which is XORed with the state word of
  `E` to give the next input of the S-box. Each S-box's circuit then runs
  and its four outputs are XORed into the state words of `L` that P sends
  them to. Rounds alternate between reading the words of `R` (`.ba`: the
  right half of IP) and of `L` (`.ab`), so no word moves; a pass of sixteen
  rounds, eight times both, ends by exchanging the halves, as DES's swap and
  the next pass's IP do.
* Three passes, in the order and key direction of the operation, choose
  their first key and its step by the pass count; then the state is
  transposed back and the blocks copied out.
* Every address and branch depends only on the pointers, `n` and the loop
  counters.
-/

namespace VG.Impl.TripleDes.X86_64.Bitslice

open VG.X86_64 VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)

/-- Slot `k` of the scratch buffer (`rcx`). -/
def at_ (k : Nat) : MemOp := { base := .rcx, disp := ((8 * k : Nat) : Int) }

def rr (d s : Reg) : Instr := .mov d (.reg s)
def ld (d : Reg) (k : Nat) : Instr := .mov d (.mem (at_ k))
def st (k : Nat) (r : Reg) : Instr := .store (at_ k) r

/-! ## Scratch slots -/

/-- The spill slots the circuits may use: slots `0 … spills - 1`. -/
def spills : Nat := 6

/-- State word `j`. -/
def stSlot (j : Nat) : Nat := 8 + j

def savedRegs : List (Reg × Nat) :=
  [(.rbx, 72), (.rbp, 73), (.r12, 74), (.r13, 75), (.r14, 76), (.r15, 77)]
def schedSlot : Nat := 78
def dataSlot : Nat := 79
def leftSlot : Nat := 80
def batchSlot : Nat := 81
def keySlot : Nat := 82
def stepSlot : Nat := 83
def roundSlot : Nat := 84
def passSlot : Nat := 85

/-! ## S-boxes -/

def inRegs : List Reg := [.rax, .rbx, .rdx, .rsi, .rdi, .rbp]
def outRegs : List Reg := [.rax, .rbx, .rdx, .rsi]
def freeRegs : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14]
def inReg (i : Nat) : Reg := inRegs.getD i .rax
def outReg (i : Nat) : Reg := outRegs.getD i .rax

def sboxCode (j : Nat) : List Instr :=
  compile (box j) ((List.range 6).map fun i => (i, inReg i))
    ((List.range 4).map fun i => ((outputs j).getD i 0, outReg i)) freeRegs (List.range spills)

/-- S-box `j`'s input `i`: the next key bit, as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.alu .add .r15 (.reg .r15), .alu .sbb (inReg i) (.reg (inReg i)),
   .alu .xor (inReg i) (.mem (at_ (stSlot (readWord ρ (eBit (inBit j i))))))]

/-- S-box `j`'s inputs, from the most significant (whose key bit is next). -/
def inputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 6).reverse.flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [.alu .xor (outReg i) (.mem (at_ (stSlot (writeWord ρ (outBit j i))))),
     st (stSlot (writeWord ρ (outBit j i))) (outReg i)]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds -/

/-- Load the round key into `r15`, its bit 47 at the top, and advance the
key pointer. -/
def keyLoad : List Instr :=
  [ld .rax keySlot, .mov .r15 (.mem { base := .rax, disp := 0 }), ld .rdx stepSlot,
   .alu .add .rax (.reg .rdx), st keySlot .rax, .shift .ror .r15 48]

def round (ρ : Role) : List Instr := keyLoad ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair : List Instr :=
  round .ba ++ round .ab ++ [ld .rax roundSlot, .alu .sub .rax (.imm 1), st roundSlot .rax]

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [ld .rax (stSlot (lWord q)), ld .rdx (stSlot (rWord q)), st (stSlot (lWord q)) .rdx,
     st (stSlot (rWord q)) .rax]

/-- The first key of each pass (an offset into the schedule) and its step,
for the passes counted down from 3. -/
def passKey : Direction → Nat → Nat × Int
  | .encrypt, 3 => (0, 8)
  | .encrypt, 2 => (8 * 31, -8)
  | .encrypt, _ => (8 * 32, 8)
  | .decrypt, 3 => (8 * 47, -8)
  | .decrypt, 2 => (8 * 16, 8)
  | .decrypt, _ => (8 * 15, -8)

/-- Point at the pass's first key, with its step. -/
def passKeyCode (d : Direction) (p : Nat) : List Instr :=
  [ld .rdx schedSlot, .alu .add .rdx (.imm (BitVec.ofNat 32 (passKey d p).1)), st keySlot .rdx,
   .mov .rdx (.imm (BitVec.ofInt 32 (passKey d p).2)), st stepSlot .rdx]

/-- Choose the pass's first key and step by the pass count, and count 8 pairs. -/
def passStart (d : Direction) : Prog isa :=
  .seq (.block [ld .rax passSlot, .alu .cmp .rax (.imm 3)])
    (.seq (.ite .e (.block (passKeyCode d 3))
      (.seq (.block [.alu .cmp .rax (.imm 2)])
        (.ite .e (.block (passKeyCode d 2)) (.block (passKeyCode d 1)))))
    (.block [.mov .rax (.imm 8), st roundSlot .rax]))

def passEnd : List Instr := [ld .rax passSlot, .alu .sub .rax (.imm 1), st passSlot .rax]

def pass (d : Direction) : Prog isa :=
  .seq (passStart d) (.seq (.loop (.block roundPair) .ne) (.block (swapHalves ++ passEnd)))

/-! ## Transposition -/

/-- The bits `p` with `p &&& s = 0`. -/
def swapMask (s : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).foldl (fun m p => if p &&& s = 0 then m ||| 2 ^ p else m) 0)

/-- Exchange the bits `p + s` of `a` and `p` of `b` (`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : Reg) (s : Nat) : List Instr :=
  [rr t a, .shift .shr t s, .alu .xor t (.reg b), .alu .and t (.reg m),
   .alu .xor b (.reg t), .shift .ror t (64 - s), .alu .xor a (.reg t)]

def groupRegs : List Reg := [.rax, .rbx, .rdx, .rsi, .rdi, .rbp, .r8, .r9]
def groupReg (k : Nat) : Reg := groupRegs.getD k .rax

/-- Three stages on eight words, the state words `word k`: the stage of
shift `unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1. -/
def group (word : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => ld (groupReg k) (stSlot (word k))) ++
  ([(4, Reg.r13), (2, .r14), (1, .r15)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .r10 m (unit * d)) ++
  (List.range 8).map (fun k => st (stSlot (word k)) (groupReg k))

def masks (unit : Nat) : List Instr :=
  [.movImm64 .r13 (swapMask (4 * unit)), .movImm64 .r14 (swapMask (2 * unit)),
   .movImm64 .r15 (swapMask unit)]

/-- Transpose the 64 state words in place: stages 32, 16, 8, then 4, 2, 1. -/
def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

/-- `k := min(n, 64)` blocks in this batch. -/
def batchSize : Prog isa :=
  .seq (.block [ld .rax leftSlot, .alu .cmp .rax (.imm 64)])
    (.seq (.ite .b (.block []) (.block [.mov .rax (.imm 64)])) (.block [st batchSlot .rax]))

/-- The public words the copies keep in registers: a store of the data to a
pointer that moves, or into the data buffer, does not keep the constant-time
analysis' knowledge that scratch slots hold public values. -/
def keepIn : List Instr :=
  [ld .r8 schedSlot, ld .r9 dataSlot, ld .r10 leftSlot, ld .r11 batchSlot]

def copyBody (src dst : Reg) : List Instr :=
  [.mov .rax (.mem { base := src, disp := 0 }), .store { base := dst, disp := 0 } .rax,
   .alu .add .rsi (.imm 8), .alu .add .rdi (.imm 8), .alu .sub .rdx (.imm 1)]

/-- Copy the batch's blocks into the state words. -/
def copyIn : Prog isa :=
  .seq (.block (keepIn ++ [rr .rsi .r9, rr .rdi .rcx, .alu .add .rdi (.imm 64), rr .rdx .r11]))
    (.seq (.loop (.block (copyBody .rsi .rdi)) .ne)
      (.block [st schedSlot .r8, st dataSlot .r9, st leftSlot .r10, st batchSlot .r11]))

/-- Copy the state words out to the batch's blocks. -/
def copyOut : Prog isa :=
  .seq (.block (keepIn ++ [rr .rsi .r9, rr .rdi .rcx, .alu .add .rdi (.imm 64), rr .rdx .r11]))
    (.loop (.block (copyBody .rdi .rsi)) .ne)

/-- Count three passes. -/
def passesStart : List Instr := [.mov .rax (.imm 3), st passSlot .rax]

/-- Advance the data pointer (`rsi`, after `copyOut`) and count the blocks left. -/
def batchEnd : List Instr :=
  [st schedSlot .r8, st dataSlot .rsi, rr .rax .r10, .alu .sub .rax (.reg .r11), st leftSlot .rax]

def batch (d : Direction) : Prog isa :=
  .seq batchSize (.seq copyIn (.seq (.block (transpose ++ passesStart))
    (.seq (.loop (pass d) .ne) (.seq (.block transpose) (.seq copyOut (.block batchEnd))))))

/-! ## The function -/

def setup : List Instr :=
  savedRegs.map (fun (r, k) => st k r) ++
  [st schedSlot .rdi, st dataSlot .rsi, st leftSlot .rdx, .alu .cmp .rdx (.imm 0)]

def restore : List Instr := savedRegs.map fun (r, k) => ld r k

def ecb (d : Direction) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop (batch d) .ne)) (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.X86_64.Bitslice
