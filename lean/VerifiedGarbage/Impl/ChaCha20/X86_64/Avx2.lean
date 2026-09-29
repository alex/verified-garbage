import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor

/-!
# ChaCha20 keystream XOR: x86-64 implementation with AVX2

`vg_chacha20_xor_avx2(state = rdi, data = rsi, len = rdx, buf = rcx)`, with
the contract of `vg_chacha20_xor`, for CPUs with AVX2.

While at least 512 bytes of data remain, eight blocks of keystream (the
counters `c, c + 1, …, c + 7` modulo 2³², `c` being word 12 of the state)
are computed at once and XORed into the next 512 bytes of the data, and
word 12 of the state is advanced by 8. The rest of the data (less than 512
bytes) is then XORed by calling `vg_chacha20_xor`.

* Each of the sixteen words of the eight states is kept in an AVX register,
  lane `j` (doubleword `j % 4` of 128-bit lane `j / 4`) holding it for block
  `j`. As in the scalar code, words 0–7 and 12–15 live in fixed registers
  (`vreg`), and words 8–11 share `ymm12` and `ymm13`: two of them are in the
  registers and the other two in their home slots in `buf`, swapped halfway
  through each column round and each diagonal round. `ymm14` is scratch and
  `ymm15` holds the `vpshufb` mask of the rotation by 16; the mask of the
  rotation by 8 is loaded into `ymm14` when needed.
* A rotation left by 16 or by 8 is a `vpshufb` of the bytes of each
  doubleword; one by 12 or by 7 is two shifts and an `vpor`.
* Each word of the input state is broadcast to all eight lanes with
  `vbroadcasti128` (a row of the state in each 128-bit lane) and `vpshufd`;
  word 12 then gets `0, 1, …, 7` added, lane by lane.
* At the end, the four registers holding a row of the eight states are
  transposed within each 128-bit lane (`vpunpck{l,h}{dq,qdq}`), so that each
  holds that row of block `i` in its low lane and of block `i + 4` in its
  high lane, and each 16 bytes are XORed into the data.
* `buf` holds the home slots of words 8–11 (32 bytes each, `[0, 128)`), the
  two masks and the counter increments (`[128, 224)`), written once on entry.
  No callee-saved register is written; `vzeroupper` precedes the call.

The branches are on the length only, and every address is a pointer plus a
constant, so only the pointers and the length can affect timing.
-/

namespace VG.Impl.ChaCha20.X86_64.Avx2

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- Offsets in `buf`: the home slot of word `k` (8–11), the masks of the
rotations by 16 and 8, and the counter increments `0, 1, …, 7`. -/
def slotOff (k : Nat) : Nat := 32 * (k - 8)
def rot16Off : Nat := 128
def rot8Off : Nat := 160
def incOff : Nat := 192

/-- The register holding word `k` whenever it is in a register. -/
def vreg : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm12 | 9 => .xmm13 | 10 => .xmm12 | 11 => .xmm13
  | 12 => .xmm8 | 13 => .xmm9 | 14 => .xmm10 | _ => .xmm11

/-- `op dst, a, b` on 256 bits. -/
def v (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- The quarter round (RFC 8439 §2.1) on each lane of `a, b, c, d`, with
`ymm14` as scratch and the mask of the rotation by 16 in `ymm15`. -/
def qr (a b c d : XReg) : List Instr := [
  v .vpaddd a a b, v .vpxor d d a, v .vpshufb d d .xmm15,
  v .vpaddd c c d, v .vpxor b b c,
  .vop (.vshift .pslld .l256 .xmm14 b 12), .vop (.vshift .psrld .l256 b b 20), v .vpor b b .xmm14,
  v .vpaddd a a b, v .vpxor d d a,
  .vmovdquLoad .l256 .xmm14 (at_ .rcx rot8Off), v .vpshufb d d .xmm14,
  v .vpaddd c c d, v .vpxor b b c,
  .vop (.vshift .pslld .l256 .xmm14 b 7), .vop (.vshift .psrld .l256 b b 25), v .vpor b b .xmm14]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2) on each lane. -/
def quarter (x y z w : Nat) : Prog isa := .block (qr (vreg x) (vreg y) (vreg z) (vreg w))

/-- Store words `i, i + 1` (in `ymm12, ymm13`) to their slots and load words `j, j + 1`. -/
def swap (i j : Nat) : Prog isa := .block [
  .vmovdquStore .l256 (at_ .rcx (slotOff i)) .xmm12,
  .vmovdquStore .l256 (at_ .rcx (slotOff (i + 1))) .xmm13,
  .vmovdquLoad .l256 .xmm12 (at_ .rcx (slotOff j)),
  .vmovdquLoad .l256 .xmm13 (at_ .rcx (slotOff (j + 1)))]

/-- `inner_block` (RFC 8439 §2.3.1) on each lane: a column round and a
diagonal round. Starts and ends with words 8 and 9 in registers. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (quarter 1 5 9 13) <| .seq (swap 8 10) <|
  .seq (quarter 2 6 10 14) <| .seq (quarter 3 7 11 15) <|
  .seq (quarter 0 5 10 15) <| .seq (quarter 1 6 11 12) <| .seq (swap 10 8) <|
  .seq (quarter 2 7 8 13) (quarter 3 4 9 14)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- The `vpshufb` masks of the rotations left by 16 and by 8 of each
doubleword, and the counter increments `0, 1, …, 7`, as the quadwords stored
in `buf` (each 128-bit mask twice, for the two lanes). -/
def rot16Q : List (BitVec 64) :=
  [0x0504070601000302, 0x0d0c0f0e09080b0a, 0x0504070601000302, 0x0d0c0f0e09080b0a]
def rot8Q : List (BitVec 64) :=
  [0x0605040702010003, 0x0e0d0c0f0a09080b, 0x0605040702010003, 0x0e0d0c0f0a09080b]
def incQ : List (BitVec 64) :=
  [0x0000000100000000, 0x0000000300000002, 0x0000000500000004, 0x0000000700000006]

/-- Store the quadwords `qs` at `buf + off`, through `rax`. -/
def storeQ (off : Nat) (qs : List (BitVec 64)) : List Instr :=
  (List.range qs.length).flatMap fun i =>
    [.movImm64 .rax (qs.getD i 0), .store (at_ .rcx (off + 8 * i)) .rax]

def consts : List Instr := storeQ rot16Off rot16Q ++ storeQ rot8Off rot8Q ++ storeQ incOff incQ

/-- Word `4 * row + i` of the state in every lane of `vreg (4 * row + i)`,
from row `row` broadcast into `src`. -/
def spread (row : Nat) (src : XReg) : List Instr :=
  (List.range 4).map fun i =>
    .vop (.vpshufd .l256 (vreg (4 * row + i)) src (BitVec.ofNat 8 (0x55 * i)))

/-- The eight states: rows 0, 1 and 3 in their registers (with the counter
increments added to word 12), words 8 and 9 in `ymm12, ymm13` and words 10
and 11 in their slots; then the rotation mask into `ymm15`. -/
def setup : List Instr :=
  [.vbroadcasti128 .xmm12 (at_ .rdi 0)] ++ spread 0 .xmm12 ++
  [.vbroadcasti128 .xmm12 (at_ .rdi 16)] ++ spread 1 .xmm12 ++
  [.vbroadcasti128 .xmm12 (at_ .rdi 48)] ++ spread 3 .xmm12 ++
  [.vmovdquLoad .l256 .xmm13 (at_ .rcx incOff), v .vpaddd .xmm8 .xmm8 .xmm13,
   .vbroadcasti128 .xmm14 (at_ .rdi 32),
   .vop (.vpshufd .l256 .xmm12 .xmm14 0x00), .vop (.vpshufd .l256 .xmm13 .xmm14 0x55),
   .vop (.vpshufd .l256 .xmm15 .xmm14 0xaa), .vmovdquStore .l256 (at_ .rcx (slotOff 10)) .xmm15,
   .vop (.vpshufd .l256 .xmm15 .xmm14 0xff), .vmovdquStore .l256 (at_ .rcx (slotOff 11)) .xmm15,
   .vmovdquLoad .l256 .xmm15 (at_ .rcx rot16Off)]

/-- Add row `row` of the input state (broadcast into `ymm14`, each word
spread into `ymm15`) to the registers `xs`. -/
def addRow (row : Nat) (xs : List XReg) : List Instr :=
  [.vbroadcasti128 .xmm14 (at_ .rdi (16 * row))] ++
  (List.range 4).flatMap fun i =>
    [.vop (.vpshufd .l256 .xmm15 .xmm14 (BitVec.ofNat 8 (0x55 * i))),
     v .vpaddd (xs.getD i .xmm0) (xs.getD i .xmm0) .xmm15]

/-- Transpose the doublewords of `x0 … x3` within each 128-bit lane, through
`ymm12 … ymm15`: afterwards `xᵢ` holds, in lane `l`, doubleword `i + 4l` of
each of `x0 … x3` (before). -/
def transpose (x0 x1 x2 x3 : XReg) : List Instr := [
  v .vpunpckldq .xmm12 x0 x1, v .vpunpckhdq .xmm13 x0 x1,
  v .vpunpckldq .xmm14 x2 x3, v .vpunpckhdq .xmm15 x2 x3,
  v .vpunpcklqdq x0 .xmm12 .xmm14, v .vpunpckhqdq x1 .xmm12 .xmm14,
  v .vpunpcklqdq x2 .xmm13 .xmm15, v .vpunpckhqdq x3 .xmm13 .xmm15]

/-- XOR the 16 bytes in lane 0 of `x` into the data at `rsi + off`, through `ymm12`. -/
def xor16 (x : XReg) (off : Nat) : List Instr :=
  [.vmovdquLoad .l128 .xmm12 (at_ .rsi off), .vop (.vbin .vpxor .l128 .xmm12 .xmm12 x),
   .vmovdquStore .l128 (at_ .rsi off) .xmm12]

/-- XOR row `row` of the eight blocks, transposed into `xs`, into the data:
`xs[i]` holds it for block `i` in lane 0 and for block `i + 4` in lane 1
(extracted into `ymm13`). -/
def xorRow (row : Nat) (xs : List XReg) : List Instr :=
  (List.range 4).flatMap fun i =>
    xor16 (xs.getD i .xmm0) (64 * i + 16 * row) ++
    [.vop (.vextracti128 .xmm13 (xs.getD i .xmm0) 1)] ++ xor16 .xmm13 (64 * (i + 4) + 16 * row)

/-- The rounds' result plus the input state, XORed into the next 512 bytes of
data. Words 8 and 9 are first stored to their slots, and the third row is
then loaded from the slots into `ymm0 … ymm3` (free once the first row is
done). -/
def finish : List Instr :=
  [.vmovdquStore .l256 (at_ .rcx (slotOff 8)) .xmm12,
   .vmovdquStore .l256 (at_ .rcx (slotOff 9)) .xmm13] ++
  addRow 0 [.xmm0, .xmm1, .xmm2, .xmm3] ++ transpose .xmm0 .xmm1 .xmm2 .xmm3 ++
    xorRow 0 [.xmm0, .xmm1, .xmm2, .xmm3] ++
  addRow 1 [.xmm4, .xmm5, .xmm6, .xmm7] ++ transpose .xmm4 .xmm5 .xmm6 .xmm7 ++
    xorRow 1 [.xmm4, .xmm5, .xmm6, .xmm7] ++
  addRow 3 [.xmm8, .xmm9, .xmm10, .xmm11] ++
    [.vmovdquLoad .l256 .xmm15 (at_ .rcx incOff), v .vpaddd .xmm8 .xmm8 .xmm15] ++
    transpose .xmm8 .xmm9 .xmm10 .xmm11 ++ xorRow 3 [.xmm8, .xmm9, .xmm10, .xmm11] ++
  [.vmovdquLoad .l256 .xmm0 (at_ .rcx (slotOff 8)), .vmovdquLoad .l256 .xmm1 (at_ .rcx (slotOff 9)),
   .vmovdquLoad .l256 .xmm2 (at_ .rcx (slotOff 10)),
   .vmovdquLoad .l256 .xmm3 (at_ .rcx (slotOff 11))] ++
  addRow 2 [.xmm0, .xmm1, .xmm2, .xmm3] ++ transpose .xmm0 .xmm1 .xmm2 .xmm3 ++
    xorRow 2 [.xmm0, .xmm1, .xmm2, .xmm3]

/-- Advance the counter by 8 and the data by 512 bytes; `CF` is clear if at
least 512 bytes remain. -/
def next : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
   .alu .add .rsi (.imm 512), .alu .sub .rdx (.imm 512), .alu .cmp .rdx (.imm 512)]

/-- Eight blocks. -/
def body : Prog isa := .seq (.block setup) (.seq (rounds 10) (.block (finish ++ next)))

def xor : Prog isa :=
  .seq (.block (consts ++ [.alu .cmp .rdx (.imm 512)]))
  (.seq (.ite .b (.block []) (.loop body .ae))
  (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Xor.xor)))

end VG.Impl.ChaCha20.X86_64.Avx2
