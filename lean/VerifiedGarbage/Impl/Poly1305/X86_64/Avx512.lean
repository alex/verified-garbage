import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2

/-!
# Poly1305 blocks: x86-64 implementation with AVX-512

`vg_poly1305_blocks_avx512(state = rdi, blocks = rsi, n = rdx)`, with the
contract of `vg_poly1305_blocks`, for CPUs with AVX-512F (and AVX2, whose
implementation it calls).

Fewer than `minBlocks` blocks are left to `vg_poly1305_blocks_avx2`.
Otherwise the first `8 ⌊n / 8⌋` blocks are absorbed eight at a time, as
`vg_poly1305_blocks_avx2` absorbs four at a time but in the eight quadwords
of `zmm` registers, and the rest (fewer than eight) by calling
`vg_poly1305_blocks`.

* Numbers modulo `p = 2¹³⁰ - 5` are kept in five 26-bit limbs, one per
  quadword, eight numbers to a set of five `zmm` registers: the
  accumulators `H` (`zmm0`–`zmm4`) of eight interleaved Horner evaluations.
  The 128 bytes of a group are loaded as two `zmm` registers and their
  low and high quadwords interleaved (`vpunpck{l,h}qdq`), lane by lane, so
  that quadword `k` holds block `π k = 4 (k mod 2) + ⌊k / 2⌋` of the group
  (blocks 0, 4, 1, 5, 2, 6, 3, 7). `H` is multiplied by `r⁸` after each
  group but the last, when quadword `k` is multiplied by `r^(8 - π k)`; the
  sum of the quadwords is then `h` after all the blocks.
* The product and its carry are those of `vg_poly1305_blocks_avx2`
  (`D` in `zmm5`–`zmm9`, the multipliers `Y` in `zmm11`–`zmm15`, `zmm10`
  scratch), on `zmm` registers.
* `Y` holds `r⁸` in the low doubleword of every quadword and `r^(8 - π k)`
  in the high doubleword of quadword `k`. They are computed on entry: `r²`
  by multiplying `r` (from the key) by itself, `(r⁴, r³)` in each lane by
  multiplying `(r², r)` by `r²`, then `(r^(4 - j), r^(4 - j))` in lane `j`
  (with `vpunpck{l,h}qdq` and `vshufi32x4`), multiplied by `(r⁴, 1)`.
* `vpmuludq` has MXCSR-configuration-dependent timing on some processors,
  so the code that uses it runs between Intel's prologue and epilogue, as in
  `vg_poly1305_blocks_avx2`.
* At the end the quadwords of `H` are summed into quadword 0
  (`vshufi32x4`, `vpunpckhqdq`), carried, and then reduced and stored by
  the code of `vg_poly1305_blocks_avx2`.

No callee-saved register is written, and `vzeroupper` precedes the calls and
the return. The branches are on `n` only, and every address is a pointer
plus a constant, so only the pointers and `n` can affect timing.
-/

namespace VG.Impl.Poly1305.X86_64.Avx512

open VG.X86_64
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)

/-- Below this many blocks, `vg_poly1305_blocks_avx2` is faster. -/
def minBlocks : Nat := 40

def z (op : ZBinOp) (d a b : XReg) : Instr := .zop (.zbin op d a b)
def srl (d a : XReg) (n : BitVec 8) : Instr := .zop (.vshift .vpsrlq d a n)
def sll (d a : XReg) (n : BitVec 8) : Instr := .zop (.vshift .vpsllq d a n)
def mov (d a : XReg) : Instr := .zop (.vmovdqa64 d a)
def shuf (d a b : XReg) (sel : BitVec 8) : Instr := .zop (.vshufi32x4 d a b sel)

/-- `r` into every quadword of `d`. -/
def bcast (d : XReg) (r : Reg) : List Instr := [.vop (.vmovq d r), .zop (.vpbroadcastq d d)]

/-- `d_j` as in `vg_poly1305_blocks_avx2` (`Avx2.prodJ`). -/
def prodJ (j : Nat) : List Instr :=
  if j < 4 then
    [z .vpmuludq (dreg j) (hreg (j + 1)) (yreg 4)] ++
    ((List.range (3 - j)).flatMap fun k =>
      [z .vpmuludq tP (hreg (j + 2 + k)) (yreg (3 - k)), z .vpaddq (dreg j) (dreg j) tP]) ++
    [sll tP (dreg j) 2, z .vpaddq (dreg j) (dreg j) tP] ++
    ((List.range (j + 1)).flatMap fun i =>
      [z .vpmuludq tP (hreg i) (yreg (j - i)), z .vpaddq (dreg j) (dreg j) tP])
  else
    [z .vpmuludq (dreg 4) (hreg 0) (yreg 4)] ++
    ((List.range 4).flatMap fun k =>
      [z .vpmuludq tP (hreg (k + 1)) (yreg (3 - k)), z .vpaddq (dreg 4) (dreg 4) tP])

def carryJ (j : Nat) : List Instr :=
  [srl tP (dreg j) 26, z .vpandq (hreg j) (dreg j) (hreg 4), z .vpaddq (dreg (j + 1)) (dreg (j + 1)) tP]

/-- The carry of `vg_poly1305_blocks_avx2` (`Avx2.carry`). -/
def carry : List Instr :=
  bcast (hreg 4) .r8 ++ carryJ 0 ++ carryJ 1 ++ carryJ 2 ++ carryJ 3 ++
  [srl tP (dreg 4) 26, mov (dreg 0) (hreg 4), z .vpandq (hreg 4) (dreg 4) (hreg 4),
   sll (dreg 1) tP 2, z .vpaddq tP tP (dreg 1), z .vpaddq (hreg 0) (hreg 0) tP,
   srl tP (hreg 0) 26, z .vpandq (hreg 0) (hreg 0) (dreg 0), z .vpaddq (hreg 1) (hreg 1) tP]

/-- `H = H · Y` (quadword by quadword, the low doublewords of `Y`). -/
def mul : List Instr :=
  prodJ 0 ++ prodJ 1 ++ prodJ 2 ++ prodJ 3 ++ prodJ 4 ++ carry

/-- The limbs of the 128-bit numbers `lo + 2⁶⁴ hi` into `d₀`–`d₄` (`Avx2.split`). -/
def split : List Instr := [
  srl (dreg 4) (dreg 1) 40, sll (dreg 3) (dreg 1) 24, srl (dreg 3) (dreg 3) 38,
  sll (dreg 2) (dreg 1) 50, srl (dreg 2) (dreg 2) 38, srl tP (dreg 0) 52, z .vporq (dreg 2) (dreg 2) tP,
  sll (dreg 1) (dreg 0) 12, srl (dreg 1) (dreg 1) 38,
  sll (dreg 0) (dreg 0) 38, srl (dreg 0) (dreg 0) 38]

/-- The eight blocks at `rsi` into `d` (block `π k` in quadword `k`), with
the pad bit (from `r9`), added to `H`. -/
def addGroup : List Instr :=
  [.vmovdqu32Load (dreg 2) (at_ .rsi 0), .vmovdqu32Load (dreg 3) (at_ .rsi 64),
   z .vpunpcklqdq (dreg 0) (dreg 2) (dreg 3), z .vpunpckhqdq (dreg 1) (dreg 2) (dreg 3)] ++ split ++
  bcast tP .r9 ++ [z .vporq (dreg 4) (dreg 4) tP] ++
  (List.range 5).map fun i => z .vpaddq (hreg i) (hreg i) (dreg i)

/-- `r` (clamped, in `r10` and `r11`) in every quadword of `D`. -/
def splitR : List Instr := bcast (dreg 0) .r10 ++ bcast (dreg 1) .r11 ++ split

/-- `r` (clamped, from the key) into `r10` and `r11`, and 1 into `rax` (for
`spread`). -/
def loadRg : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r10 (.mem (at_ .rdi 24)), .alu .and .r10 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r11 (.mem (at_ .rdi 32)), .alu .and .r11 (.reg .rax),
  .mov32 .rax (.imm 1)]

/-- `r` in every quadword of `H` (and of `D`). -/
def loadRv : List Instr := splitR ++ (List.range 5).map fun i => mov (hreg i) (dreg i)

/-- `Y = H` in both doublewords of each quadword. -/
def initY : List Instr :=
  (List.range 5).flatMap fun i => [sll tP (hreg i) 32, z .vporq (yreg i) (hreg i) tP]

/-- With `H = r²` and `Y = r` (in both doublewords): `Y = r²` and `H = (r²,
r)` in each lane. -/
def pairs : List Instr :=
  (List.range 5).flatMap fun i =>
    [srl (dreg i) (yreg i) 32, mov (yreg i) (hreg i), z .vpunpcklqdq (hreg i) (hreg i) (dreg i)]


/-- With `H = (r⁴, r³)` in each lane, `Y = r²` and `D = r`: `H = (r^(4 - j),
r^(4 - j))` in lane `j`, and `Y = (r⁴, 1)` in each lane. Limb by limb, `Y`
is first `(r², r)` in each lane, then the quadwords of `H` and `Y` are
duplicated and the lanes picked (`vshufi32x4`), and `r⁴` broadcast from
quadword 0 of `H` and interleaved with the limbs of 1 (in `tP`, from `rax`). -/
def spread : List Instr :=
  (List.range 5).flatMap (fun i =>
    [z .vpunpcklqdq (yreg i) (yreg i) (dreg i),
     z .vpunpcklqdq (dreg i) (hreg i) (hreg i), z .vpunpckhqdq tP (hreg i) (hreg i),
     shuf (hreg i) (dreg i) tP 0,
     z .vpunpcklqdq (dreg i) (yreg i) (yreg i), z .vpunpckhqdq tP (yreg i) (yreg i),
     shuf (yreg i) (dreg i) tP 0,
     shuf (hreg i) (hreg i) (yreg i) 0x88]) ++
  bcast tP .rax ++
  (List.range 5).flatMap fun i =>
    [.zop (.vpbroadcastq (yreg i) (hreg i)), z .vpunpcklqdq (yreg i) (yreg i) tP] ++
      (if i = 0 then [z .vpandnq tP tP tP] else [])

/-- With `H = r^(8 - π k)` in quadword `k`: `Y` with `r⁸` (quadword 0 of
`H`) in the low doublewords and `H` in the high ones. -/
def finishY : List Instr :=
  (List.range 5).flatMap fun i =>
    [.zop (.vpbroadcastq tP (hreg i)), sll (dreg i) (hreg i) 32, z .vporq (yreg i) (dreg i) tP]

/-- `Y`: `r⁸` in the low doublewords and `r^(8 - π k)` in the high
doubleword of quadword `k`. -/
def powers : List Instr :=
  loadRg ++ loadRv ++ initY ++ mul ++ pairs ++ mul ++ splitR ++ spread ++ mul ++ finishY

/-- The accumulator `h` (from the state) in quadword 0 of `H`, zeros
elsewhere: its words in `r10`, `r11` and `rax` (`Avx2.loadHw`), then limb 4
is `(h₁ >> 40) | (h₂ << 24)`. -/
def loadH : List Instr :=
  [.vop (.vmovq (dreg 0) .r10), .vop (.vmovq (dreg 1) .r11)] ++ split ++
  [.vop (.vmovq tP .rax), sll tP tP 24, z .vporq (dreg 4) (dreg 4) tP] ++
  (List.range 5).map fun i => mov (hreg i) (dreg i)

/-- One group of eight blocks, multiplied by `r⁸`. -/
def groupBody : Prog isa :=
  .block (addGroup ++ mul ++ [.alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)])

/-- The last group, multiplied quadword by quadword by the high doublewords of `Y`. -/
def last : List Instr :=
  addGroup ++ (List.range 5).map (fun i => srl (yreg i) (yreg i) 32) ++ mul

/-- The sum of the quadwords of `H` into quadword 0 of `d`, carried into `H`:
the upper lanes added to the lower (`vshufi32x4`), then lane 1 to lane 0,
then quadword 1 to quadword 0. -/
def sumLanes : List Instr :=
  (List.range 5).flatMap (fun i =>
    [shuf tP (hreg i) (hreg i) 0xee, z .vpaddq (dreg i) (hreg i) tP,
     shuf tP (dreg i) (dreg i) 0x01, z .vpaddq (dreg i) (dreg i) tP,
     z .vpunpckhqdq tP (dreg i) (dreg i), z .vpaddq (dreg i) (dreg i) tP]) ++ carry

/-- The first `8 ⌊n / 8⌋` blocks absorbed; `rsi` advanced past them,
`rdx = n mod 8`. The groups before the last are counted down in `rcx`. -/
def body : Prog isa :=
  .seq (.block (Avx2.consts ++ Avx2.mxcsrIn ++ powers ++ Avx2.loadHw ++ loadH ++
    [.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)]))
  (.seq (.loop groupBody .ne)
    (.block (Avx2.consts2 ++ last ++ sumLanes ++ Avx2.fullCarry ++ Avx2.reduce ++ Avx2.mxcsrOut ++
      Avx2.storeH ++
      [.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)])))

def scalar : Prog isa := .call "vg_poly1305_blocks" blocks
def avx2 : Prog isa := .call "vg_poly1305_blocks_avx2" Avx2.blocksAvx2

def blocksAvx512 : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))])
    (.ite .b avx2
      (.seq body
        (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) scalar))))

end VG.Impl.Poly1305.X86_64.Avx512
