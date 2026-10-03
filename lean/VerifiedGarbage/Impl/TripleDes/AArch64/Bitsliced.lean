import VerifiedGarbage.Impl.TripleDes.BitsliceLayout
import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc

/-!
# Bitsliced Triple DES ECB on AArch64 with AdvSIMD

`vg_triple_des_ecb_{en,de}crypt(schedule = x0, data = x1, n = x2, scratch = x3)`.

Constant-time Triple DES on 128 blocks at a time, bitsliced in 128-bit
words (Biham's bitslicing; the S-box circuits are Rusakov's,
`BitsliceCircuit`), as x86-64's SSE2 code does.

* The state of 128 blocks (64 words of 16 bytes, at `x4`) is the 1024 bytes
  of the blocks themselves: the 16 bytes at `x4 + 16 i` hold blocks `2i`
  and `2i + 1` as little-endian doublewords, and each doubleword lane `q` of
  the 64 words is transposed in place, so that word `j`'s bit `64 q + i` is
  bit `j` of block `2i + q` (`BitsliceLayout`); IP only renames words.
  While at least 128 blocks are left the state is the data itself; the last
  `n mod 128` blocks are copied into the scratch buffer, whose other bytes
  are whatever they were (their results are not stored), and back.
* A round loads its key into `x9` and broadcasts it to `v30`. S-box `j`'s
  input `i` is key bit `inBit j i` as a mask, `0 - ((key << (63 - b)) >> 63)`
  in each doubleword (`v31` is zero), XORed with the state word of `E`.
  Each S-box's circuit then runs in registers and its four outputs are
  XORed into the state words of `L` that P sends them to. Rounds alternate
  between reading the words of `R` (`.ba`) and of `L` (`.ab`), so no word
  moves; a pass of sixteen rounds, eight times both, ends by exchanging the
  halves, as DES's swap and the next pass's IP do.
* The three passes are unrolled, each with its schedule component and key
  direction; `x5` is the key pointer and `x7` counts pairs of rounds.
* Every address and branch depends only on the pointers, `n` and the loop
  counters. Only caller-saved registers are used.
-/

namespace VG.Impl.TripleDes.AArch64.BitsliceNeon

open VG.AArch64 VG.Impl.TripleDes.Bitslice
open VG.Spec.TripleDes (Direction)

/-- The state base. -/
def base : Reg := .x4

/-- Load and store state word `j`. -/
def ldw (d : VReg) (j : Nat) : Instr := .ldrq d base (16 * j)
def stw (j : Nat) (r : VReg) : Instr := .strq r base (16 * j)

def veor (d n m : VReg) : Instr := .vop (.logic .eor d n m)
def vand (d n m : VReg) : Instr := .vop (.logic .and d n m)

/-! ## S-boxes -/

def inRegs : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5]
def freeRegs : List VReg :=
  [.v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28]
def inReg (i : Nat) : VReg := inRegs.getD i .v0

/-- The broadcast round key. -/
def keyReg : VReg := .v30
/-- Zero. -/
def zeroReg : VReg := .v31
/-- A temporary for the state words. -/
def tmpReg : VReg := .v29

def sboxCompiled (j : Nat) : List Instr × List VReg :=
  compile (box j) ((List.range 6).map fun i => (i, inReg i)) (outputs j) freeRegs

def sboxCode (j : Nat) : List Instr := (sboxCompiled j).1

/-- The registers of each S-box's outputs. -/
def outRegsTable : List (List VReg) := (List.range 8).map fun j => (sboxCompiled j).2

/-- The register of S-box `j`'s output `i`. -/
def outReg (j i : Nat) : VReg := (outRegsTable.getD j []).getD i .v0

/-- S-box `j`'s input `i`: key bit `inBit j i` as a mask, ⊕ the word of `E`. -/
def inputStep (ρ : Role) (j i : Nat) : List Instr :=
  [.vop (.shift .shl .d2 (inReg i) keyReg (63 - inBit j i)),
   .vop (.shift .ushr .d2 (inReg i) (inReg i) 63),
   .vop (.sub .d2 (inReg i) zeroReg (inReg i)),
   ldw tmpReg (readWord ρ (eBit (inBit j i))),
   veor (inReg i) (inReg i) tmpReg]

def inputCode (ρ : Role) (j : Nat) : List Instr := (List.range 6).flatMap (inputStep ρ j)

/-- XOR S-box `j`'s outputs into their words. -/
def outputCode (ρ : Role) (j : Nat) : List Instr :=
  (List.range 4).flatMap fun i =>
    [ldw tmpReg (writeWord ρ (outBit j i)), veor tmpReg tmpReg (outReg j i),
     stw (writeWord ρ (outBit j i)) tmpReg]

def sboxStep (ρ : Role) (j : Nat) : List Instr := inputCode ρ j ++ sboxCode j ++ outputCode ρ j

/-! ## Rounds and passes -/

/-- Load the round key, broadcast it, and step the key pointer `x5`. -/
def keyLoad (d : Direction) : List Instr :=
  [.ldr .x .x9 .x5 0, .vop (.dup .d2 keyReg .x9),
   if d = .encrypt then .addImm .x .x5 .x5 8 else .subImm .x .x5 .x5 8]

def round (d : Direction) (ρ : Role) : List Instr :=
  keyLoad d ++ (List.range 8).flatMap (sboxStep ρ)

/-- Two rounds, and the count of pairs left. -/
def roundPair (d : Direction) : List Instr :=
  round d .ba ++ round d .ab ++ [.subImm .x .x7 .x7 1]

/-- Exchange the halves. -/
def swapHalves : List Instr :=
  (List.range 32).flatMap fun q =>
    [ldw .v0 (lWord q), ldw .v1 (rWord q), stw (lWord q) .v1, stw (rWord q) .v0]

/-- A DES pass with schedule component `c`, in direction `d`. -/
def pass (c : Nat) (d : Direction) : Prog isa :=
  .seq (.block [.addImm .x .x5 .x0 (128 * c + if d = .encrypt then 0 else 120),
      .movz .x .x7 8 0])
    (.seq (.loop (.block (roundPair d)) (.nonzero .x .x7)) (.block swapHalves))

/-- The three passes of the operation. -/
def passes : Direction → Prog isa
  | .encrypt => .seq (pass 0 .encrypt) (.seq (pass 1 .decrypt) (pass 2 .encrypt))
  | .decrypt => .seq (pass 2 .decrypt) (.seq (pass 1 .encrypt) (pass 0 .decrypt))

/-! ## Transposition -/

/-- The bits `p` with `p &&& s = 0`. -/
def swapMask (s : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 64).foldl (fun m p => if p &&& s = 0 then m ||| 2 ^ p else m) 0)

/-- Broadcast a 64-bit constant to both doublewords of `d`, through `x10`. -/
def bcast (d : VReg) (v : BitVec 64) : List Instr :=
  [.movz .x .x10 (v.extractLsb' 0 16) 0, .movk .x .x10 (v.extractLsb' 16 16) 1,
   .movk .x .x10 (v.extractLsb' 32 16) 2, .movk .x .x10 (v.extractLsb' 48 16) 3,
   .vop (.dup .d2 d .x10)]

/-- Exchange the bits `p + s` of `a` and `p` of `b` in every doubleword lane
(`p &&& s = 0`), masked by `m`. -/
def swapBits (a b t m : VReg) (s : Nat) : List Instr :=
  [.vop (.shift .ushr .d2 t a s), veor t t b, vand t t m, veor b b t,
   .vop (.shift .shl .d2 t t s), veor a a t]

def groupRegs : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7]
def groupReg (k : Nat) : VReg := groupRegs.getD k .v0

/-- Three stages on eight words, the state words `w k`: the stage of shift
`unit * d` pairs the words `k` and `k + d`, for `d` = 4, 2, 1. -/
def group (w : Nat → Nat) (unit : Nat) : List Instr :=
  (List.range 8).map (fun k => ldw (groupReg k) (w k)) ++
  ([(4, VReg.v16), (2, .v17), (1, .v18)].flatMap fun (d, m) =>
    ((List.range 8).filter (fun k => k &&& d = 0)).flatMap fun k =>
      swapBits (groupReg k) (groupReg (k + d)) .v19 m (unit * d)) ++
  (List.range 8).map (fun k => stw (w k) (groupReg k))

def masks (unit : Nat) : List Instr :=
  bcast .v16 (swapMask (4 * unit)) ++ bcast .v17 (swapMask (2 * unit)) ++
  bcast .v18 (swapMask unit)

/-- Transpose each doubleword lane of the 64 state words in place: stages
32, 16, 8, then 4, 2, 1. -/
def transpose : List Instr :=
  masks 8 ++ (List.range 8).flatMap (fun i => group (fun k => i + 8 * k) 8) ++
  masks 1 ++ (List.range 8).flatMap (fun g => group (fun k => 8 * g + k) 1)

/-! ## Batches -/

/-- Three passes on the 128 blocks at `x4`. -/
def batch (d : Direction) : Prog isa :=
  .seq (.block (transpose ++ [.vop (.movi0 zeroReg)])) (.seq (passes d) (.block transpose))

/-- `x10 := n / 128`, whether a whole batch is left. -/
def wholeLeft : Instr := .lsr .x .x10 .x2 7

/-- Batches of 128 blocks, in place, while there are that many. -/
def wide (d : Direction) : Prog isa :=
  .seq (.block [wholeLeft])
    (.ite (.zero .x .x10) (.block [])
      (.loop (.seq (.block [.addImm .x .x4 .x1 0])
          (.seq (batch d) (.block [.addImm .x .x1 .x1 1024, .subImm .x .x2 .x2 128, wholeLeft])))
        (.nonzero .x .x10)))

/-- Copy `x13` 8-byte blocks from `x11` to `x12`. -/
def copy : Prog isa :=
  .loop (.block [.ldr .x .x10 .x11 0, .str .x .x10 .x12 0, .addImm .x .x11 .x11 8,
      .addImm .x .x12 .x12 8, .subImm .x .x13 .x13 1]) (.nonzero .x .x13)

/-- The last `n < 128` blocks, through the scratch buffer. -/
def tail (d : Direction) : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block [.addImm .x .x11 .x1 0, .addImm .x .x12 .x3 0, .addImm .x .x13 .x2 0])
      (.seq copy
        (.seq (.block [.addImm .x .x4 .x3 0]) (.seq (batch d)
          (.seq (.block [.addImm .x .x11 .x3 0, .addImm .x .x12 .x1 0, .addImm .x .x13 .x2 0])
            copy)))))

def ecb (d : Direction) : Prog isa := .seq (wide d) (tail d)

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.AArch64.BitsliceNeon
