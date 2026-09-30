import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2

/-!
# ChaCha20 keystream XOR: x86-64 implementation with AVX-512

`vg_chacha20_xor_avx512(state = rdi, data = rsi, len = rdx, buf = rcx)`,
with the contract of `vg_chacha20_xor`, for CPUs with AVX-512F.

While at least 1024 bytes of data remain, sixteen blocks of keystream (the
counters `c, c + 1, …, c + 15` modulo 2³², `c` being word 12 of the state)
are computed at once and XORed into the next 1024 bytes of the data, and
word 12 of the state is advanced by 16. The rest of the data (less than 1024
bytes) is then XORed by calling `vg_chacha20_xor`, as `vg_chacha20_xor_avx2`
does, so that it uses no more stack than that implementation.

* Word `k` of the sixteen states is kept in `zmmk`, doubleword `j` holding it
  for block `j` (doubleword `j % 4` of 128-bit lane `j / 4`). With `vprold`
  every rotation is one instruction, and the rounds need no other register.
* Each word of the input state is broadcast to all sixteen doublewords with
  `vbroadcasti32x4` (a row of the state in each 128-bit lane) and `vpshufd`;
  word 12 then gets `0, 1, …, 15` added.
* At the end, the input state is added to each row of four registers, and
  the doublewords of the row are transposed within each 128-bit lane
  (`vpunpck{l,h}{dq,qdq}`), so that register `i` of row `r` holds row `r` of
  blocks `i, i + 4, i + 8, i + 12` in its four lanes. For each `i`, eight
  `vshufi32x4` gather these four registers of the four rows into the four
  blocks, each 64 bytes XORed into the data. Two registers at a time are
  saved to `buf` to make room: words 14 and 15 while the other rows are
  transposed, then two transposed registers of the first row while the last
  row is.
* `buf` holds the two saved registers (`[0, 128)`) and the counter
  increments (`[128, 192)`), written once on entry. No callee-saved register
  is written; `vzeroupper` precedes the call.

The branches are on the length only, and every address is a pointer plus a
constant, so only the pointers and the length can affect timing.
-/

namespace VG.Impl.ChaCha20.X86_64.Avx512

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- Offsets in `buf`: the two saved registers and the counter increments. -/
def save0Off : Nat := 0
def save1Off : Nat := 64
def incOff : Nat := 128

/-- The register holding word `k` during the rounds. -/
def zreg : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

/-- `op zmm d, zmm a, zmm b`. -/
def z (op : ZBinOp) (d a b : XReg) : Instr := .zop (.zbin op d a b)

/-- One half of the quarter round (RFC 8439 §2.1) on each doubleword of each of
the four quadruples `qs`, interleaved: `a += b; d ^= a; d <<<= r₁; c += d;
b ^= c; b <<<= r₂`. -/
def half (qs : List (XReg × XReg × XReg × XReg)) (r₁ r₂ : BitVec 8) : List Instr :=
  qs.map (fun (a, b, _, _) => z .vpaddd a a b) ++
  qs.map (fun (a, _, _, d) => z .vpxord d d a) ++
  qs.map (fun (_, _, _, d) => .zop (.vprold d d r₁)) ++
  qs.map (fun (_, _, c, d) => z .vpaddd c c d) ++
  qs.map (fun (_, b, c, _) => z .vpxord b b c) ++
  qs.map (fun (_, b, _, _) => .zop (.vprold b b r₂))

/-- `QUARTERROUND` (RFC 8439 §2.2) on the four quadruples of words `ws`, at once. -/
def quarters (ws : List (Nat × Nat × Nat × Nat)) : List Instr :=
  let qs := ws.map fun (a, b, c, d) => (zreg a, zreg b, zreg c, zreg d)
  half qs 16 12 ++ half qs 8 7

/-- `inner_block` (RFC 8439 §2.3.1) on each doubleword: a column round and a
diagonal round. -/
def doubleRound : List Instr :=
  quarters [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)] ++
  quarters [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block doubleRound)

/-- The counter increments `0, 1, …, 15`, as the quadwords stored in `buf`. -/
def incQ : List (BitVec 64) :=
  (List.range 8).map fun i => BitVec.ofNat 64 ((2 * i + 1) * 2 ^ 32 + 2 * i)

def consts : List Instr := Avx2.storeQ incOff incQ

/-- Row `row` of the input state, each word spread into all of `xs`,
broadcast through the last of them. -/
def spread (row : Nat) (xs : List XReg) : List Instr :=
  [.vbroadcasti32x4 (xs.getD 3 .xmm0) (at_ .rdi (16 * row))] ++
  (List.range 4).map fun i =>
    .zop (.vpshufd (xs.getD i .xmm0) (xs.getD 3 .xmm0) (BitVec.ofNat 8 (0x55 * i)))

/-- The sixteen states, word `k` in `zreg k`, with the counter increments
added to word 12. -/
def setup : List Instr :=
  spread 3 [.xmm12, .xmm13, .xmm14, .xmm15] ++
  [.vmovdqu32Load .xmm0 (at_ .rcx incOff), z .vpaddd .xmm12 .xmm12 .xmm0] ++
  spread 0 [.xmm0, .xmm1, .xmm2, .xmm3] ++ spread 1 [.xmm4, .xmm5, .xmm6, .xmm7] ++
  spread 2 [.xmm8, .xmm9, .xmm10, .xmm11]

/-- Add row `row` of the input state (broadcast into `t`, each word spread
into `u`) to the registers `xs`. -/
def addRow (row : Nat) (xs : List XReg) (t u : XReg) : List Instr :=
  [.vbroadcasti32x4 t (at_ .rdi (16 * row))] ++
  (List.range 4).flatMap fun i =>
    [.zop (.vpshufd u t (BitVec.ofNat 8 (0x55 * i))), z .vpaddd (xs.getD i .xmm0) (xs.getD i .xmm0) u]

/-- Transpose the doublewords of `x0 … x3` within each 128-bit lane, through
`t0, t1`: afterwards `x0, t0, x2, x3` hold, in each lane, doublewords 0, 1,
2 and 3 of `x0 … x3` (before), and `x1, t1` are free. -/
def transpose (x0 x1 x2 x3 t0 t1 : XReg) : List Instr := [
  z .vpunpckldq t0 x0 x1, z .vpunpckhdq x1 x0 x1,
  z .vpunpckldq t1 x2 x3, z .vpunpckhdq x3 x2 x3,
  z .vpunpcklqdq x0 t0 t1, z .vpunpckhqdq t0 t0 t1,
  z .vpunpcklqdq x2 x1 x3, z .vpunpckhqdq x3 x1 x3]

/-- XOR the 64 bytes in `x` into the data at `rsi + off`, through `t`. -/
def xor64 (x t : XReg) (off : Nat) : List Instr :=
  [.vmovdqu32Load t (at_ .rsi off), z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]

/-- Blocks `i, i + 4, i + 8, i + 12`, from rows 0–3 of them in the lanes of
`a, b, c, d` (see `transpose`), gathered through `t0, t1` and XORed into the
data (through `a`). -/
def gather (i : Nat) (a b c d t0 t1 : XReg) : List Instr :=
  [.zop (.vshufi32x4 t0 a b 0x44), .zop (.vshufi32x4 a a b 0xee),
   .zop (.vshufi32x4 t1 c d 0x44), .zop (.vshufi32x4 c c d 0xee),
   .zop (.vshufi32x4 b t0 t1 0x88), .zop (.vshufi32x4 d t0 t1 0xdd),
   .zop (.vshufi32x4 t0 a c 0x88), .zop (.vshufi32x4 t1 a c 0xdd)] ++
  xor64 b a (64 * i) ++ xor64 d a (64 * (i + 4)) ++
  xor64 t0 a (64 * (i + 8)) ++ xor64 t1 a (64 * (i + 12))

/-- The rounds' result plus the input state, XORed into the next 1024 bytes
of data. The registers holding row `r` after its transpose are, for
`i = 0 … 3`: row 0 `zmm0, zmm14, zmm2, zmm3` (`zmm2, zmm3` then saved to
`buf`), row 1 `zmm4, zmm1, zmm6, zmm7`, row 2 `zmm8, zmm5, zmm10, zmm11`,
row 3 `zmm12, zmm2, zmm9, zmm15`. -/
def finish : List Instr :=
  [.vmovdqu32Store (at_ .rcx save0Off) .xmm14, .vmovdqu32Store (at_ .rcx save1Off) .xmm15] ++
  addRow 0 [.xmm0, .xmm1, .xmm2, .xmm3] .xmm14 .xmm15 ++
    transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm14 .xmm15 ++
  addRow 1 [.xmm4, .xmm5, .xmm6, .xmm7] .xmm1 .xmm15 ++
    transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm1 .xmm15 ++
  addRow 2 [.xmm8, .xmm9, .xmm10, .xmm11] .xmm5 .xmm15 ++
    transpose .xmm8 .xmm9 .xmm10 .xmm11 .xmm5 .xmm15 ++
  [.vmovdqu32Load .xmm9 (at_ .rcx save0Off), .vmovdqu32Load .xmm15 (at_ .rcx save1Off),
   .vmovdqu32Store (at_ .rcx save0Off) .xmm2, .vmovdqu32Store (at_ .rcx save1Off) .xmm3] ++
  addRow 3 [.xmm12, .xmm13, .xmm9, .xmm15] .xmm2 .xmm3 ++
    [.vmovdqu32Load .xmm3 (at_ .rcx incOff), z .vpaddd .xmm12 .xmm12 .xmm3] ++
    transpose .xmm12 .xmm13 .xmm9 .xmm15 .xmm2 .xmm3 ++
  gather 0 .xmm0 .xmm4 .xmm8 .xmm12 .xmm13 .xmm3 ++
  gather 1 .xmm14 .xmm1 .xmm5 .xmm2 .xmm13 .xmm3 ++
  [.vmovdqu32Load .xmm0 (at_ .rcx save0Off)] ++ gather 2 .xmm0 .xmm6 .xmm10 .xmm9 .xmm13 .xmm3 ++
  [.vmovdqu32Load .xmm0 (at_ .rcx save1Off)] ++ gather 3 .xmm0 .xmm7 .xmm11 .xmm15 .xmm13 .xmm3

/-- Advance the counter by 16 and the data by 1024 bytes; `CF` is clear if at
least 1024 bytes remain. -/
def next : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 16), .store32 (at_ .rdi 48) .rax,
   .alu .add .rsi (.imm 1024), .alu .sub .rdx (.imm 1024), .alu .cmp .rdx (.imm 1024)]

/-- Sixteen blocks. -/
def body : Prog isa := .seq (.block setup) (.seq (rounds 10) (.block (finish ++ next)))

def xor : Prog isa :=
  .seq (.block (consts ++ [.alu .cmp .rdx (.imm 1024)]))
  (.seq (.ite .b (.block []) (.loop body .ae))
  (.seq (.block [.vop .vzeroupper]) (.call "vg_chacha20_xor" Xor.xor)))

end VG.Impl.ChaCha20.X86_64.Avx512
