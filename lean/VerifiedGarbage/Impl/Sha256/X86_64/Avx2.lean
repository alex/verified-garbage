import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SHA-256 compression function: x86-64 implementation with AVX2 and BMI

`vg_sha256_compress_avx2(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the contract of `vg_sha256_compress`, for CPUs with AVX, AVX2, BMI1 and
BMI2 (and without the SHA extensions, which `vg_sha256_compress_shani`
uses). This is the technique of OpenSSL's AVX2+BMI2 SHA-256
(`sha512-x86_64.pl`, by Andy Polyakov): two blocks at a time, their message
schedules computed together in the two 128-bit lanes of the `ymm`
registers, and the rounds in general-purpose registers.

* The message schedule of the two blocks is kept four words to a register,
  `W₄ᵢ … W₄ᵢ₊₃` of the first block in lane 0 and of the second in lane 1 of
  `msg i` (`ymm0 … ymm3`), and stored to `scratch[32i..32i+32)`, from which
  the rounds of each block read it (lane 0 at `32i`, lane 1 at `32i + 16`).
  Words `4i+16 … 4i+19` are computed during rounds `4i … 4i+3` of the first
  block, with `ymm4 … ymm7` as temporaries, and the `pshufb` masks in
  `ymm8` (`σ₁` into words 0 and 1), `ymm9` (into words 2 and 3) and `ymm10`
  (big-endian words).
* The working variables `a … h` are renamed by the unrolled rounds as in
  `vg_sha256_compress` (`var`); `Σ₀` and `Σ₁` are three `rorx`, `Ch(e, f, g)`
  is `(e ∧ f) + (¬e ∧ g)`, and `Maj(a, b, c)` is `((a ⊕ b) ∧ (b ⊕ c)) ⊕ b`,
  where `b ⊕ c` is the previous round's `a ⊕ b`, kept in `carry t`. `Kₜ` is
  an immediate, since the model has no constant pool.
* If only one block is left, it is loaded into both lanes and only the
  first block's rounds run.
* `rbx, rbp, r12–r15` are saved in `scratch[512..560)` and restored on exit;
  `vzeroupper` before returning avoids the penalty of dirty upper halves in
  the caller's SSE code.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sha256.X86_64.Avx2

open VG.X86_64
open VG.Spec.Sha256 (K)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## Rounds -/

/-- The registers holding the working variables. -/
def work : List Reg := [.rax, .rbx, .rbp, .r8, .r9, .r10, .r11, .r12]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .rax

/-- The register holding `b ⊕ c` at the start of round `t`; round `t` leaves
the next one's in `carry (t + 1)`. -/
def carry (t : Nat) : Reg := if t % 2 = 0 then .r13 else .r14

/-- The other temporary. -/
def T : Reg := .r15

/-- Where round `t` of block `j` (0 or 1) reads `Wₜ`. -/
def wSlot (j t : Nat) : MemOp := at_ .rcx (32 * (t / 4) + 16 * j + 4 * (t % 4))

/-- Round `t` of block `j`. The additions are in the order of the specification:
`T₁ = h + Σ₁(e) + Ch(e, f, g) + Kₜ + Wₜ`, `T₂ = Σ₀(a) + Maj(a, b, c)`. -/
def round (j t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  let x := carry t; let y := carry (t + 1)
  [ -- h := h + Σ₁(e)
    .rorx32 y e 6, .rorx32 T e 11, .alu32 .xor y (.reg T), .rorx32 T e 25, .alu32 .xor y (.reg T),
    .alu32 .add h (.reg y),
    -- h := h + Ch(e, f, g), as (e ∧ f) + (¬e ∧ g)
    .mov32 y (.reg e), .alu32 .and y (.reg f), .andn32 T e g, .alu32 .add y (.reg T),
    .alu32 .add h (.reg y),
    -- h := h + Kₜ + Wₜ, which is T₁
    .alu32 .add h (.imm (K t)),
    .alu32 .add h (.mem (wSlot j t)),
    -- e' := d + T₁
    .alu32 .add d (.reg h),
    -- h := h + Σ₀(a)
    .rorx32 y a 2, .rorx32 T a 13, .alu32 .xor y (.reg T), .rorx32 T a 22, .alu32 .xor y (.reg T),
    .alu32 .add h (.reg y),
    -- h := h + Maj(a, b, c), as ((a ⊕ b) ∧ (b ⊕ c)) ⊕ b, with b ⊕ c in x;
    -- a ⊕ b, in y, is the next round's b ⊕ c
    .mov32 y (.reg a), .alu32 .xor y (.reg b), .alu32 .and x (.reg y), .alu32 .xor x (.reg b),
    .alu32 .add h (.reg x)]

/-- Set up `carry 0 = b ⊕ c` for the rounds. -/
def initCarry : List Instr := [.mov32 (carry 0) (.reg (var 0 1)), .alu32 .xor (carry 0) (.reg (var 0 2))]

/-! ## Message schedule -/

/-- The register holding `W₄ᵢ … W₄ᵢ₊₃` of both blocks. -/
def msg (i : Nat) : XReg := [.xmm0, .xmm1, .xmm2, .xmm3].getD (i % 4) .xmm0

def t0 : XReg := .xmm4
def t1 : XReg := .xmm5
def t2 : XReg := .xmm6
def t3 : XReg := .xmm7
/-- `pshufb` mask: dwords 0 and 2 into dwords 0 and 1, zeros above. -/
def mBA : XReg := .xmm8
/-- `pshufb` mask: dwords 0 and 2 into dwords 2 and 3, zeros below. -/
def mDC : XReg := .xmm9
/-- `pshufb` mask: big-endian words. -/
def mBswap : XReg := .xmm10
def tmp : XReg := .xmm11

def vb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)
def vs (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Instr := .vop (.vshift op .l256 d a n)

/-- `W₄ᵢ … W₄ᵢ₊₃` of both blocks into `msg i` (for `i ≥ 4`), from the previous
sixteen words (whose register `msg i` held the oldest four), and stored. As
in OpenSSL: `σ₀` of four words at once, then `σ₁` of two at a time, from the
words doubled into quadwords (so that a quadword shift rotates them). -/
def schedule (i : Nat) : List Instr :=
  let x0 := msg i; let x1 := msg (i + 1); let x2 := msg (i + 2); let x3 := msg (i + 3)
  [ .vop (.vpalignr .l256 t0 x1 x0 4),      -- W₄ᵢ₋₁₅ … W₄ᵢ₋₁₂
    .vop (.vpalignr .l256 t3 x3 x2 4),      -- W₄ᵢ₋₇ … W₄ᵢ₋₄
    vs .psrld t2 t0 7,
    vb .vpaddd x0 x0 t3,                    -- W₄ᵢ₋₁₆ + W₄ᵢ₋₇ …
    vs .psrld t3 t0 3,
    vs .pslld t1 t0 14,
    vb .vpxor t0 t3 t2,
    .vop (.vpshufd .l256 t3 x3 0xfa),       -- W₄ᵢ₋₂, W₄ᵢ₋₂, W₄ᵢ₋₁, W₄ᵢ₋₁
    vs .psrld t2 t2 11,
    vb .vpxor t0 t0 t1,
    vs .pslld t1 t1 11,
    vb .vpxor t0 t0 t2,
    vs .psrld t2 t3 10,
    vb .vpxor t0 t0 t1,                     -- σ₀(W₄ᵢ₋₁₅ … W₄ᵢ₋₁₂)
    vs .psrlq t3 t3 17,
    vb .vpaddd x0 x0 t0,
    vb .vpxor t2 t2 t3,
    vs .psrlq t3 t3 2,
    vb .vpxor t2 t2 t3,
    vb .vpshufb t2 t2 mBA,                  -- σ₁(W₄ᵢ₋₂), σ₁(W₄ᵢ₋₁), 0, 0
    vb .vpaddd x0 x0 t2,                    -- W₄ᵢ, W₄ᵢ₊₁
    .vop (.vpshufd .l256 t3 x0 0x50),       -- W₄ᵢ, W₄ᵢ, W₄ᵢ₊₁, W₄ᵢ₊₁
    vs .psrld t2 t3 10,
    vs .psrlq t3 t3 17,
    vb .vpxor t2 t2 t3,
    vs .psrlq t3 t3 2,
    vb .vpxor t2 t2 t3,
    vb .vpshufb t2 t2 mDC,                  -- 0, 0, σ₁(W₄ᵢ), σ₁(W₄ᵢ₊₁)
    vb .vpaddd x0 x0 t2,                    -- W₄ᵢ₊₂, W₄ᵢ₊₃
    .vmovdquStore .l256 (at_ .rcx (32 * i)) x0]

/-- `W₄ᵢ … W₄ᵢ₊₃` (`i < 4`) of the blocks at `rsi` and `r15` into `msg i`, and stored. -/
def load (i : Nat) : List Instr :=
  [.vmovdquLoad .l128 (msg i) (at_ .rsi (16 * i)), .vmovdquLoad .l128 tmp (at_ T (16 * i)),
   .vop (.vinserti128 (msg i) (msg i) tmp 1), vb .vpshufb (msg i) (msg i) mBswap,
   .vmovdquStore .l256 (at_ .rcx (32 * i)) (msg i)]

/-- Rounds `4i … 4i+3` of the first block, computing words `4i+16 … 4i+19` meanwhile. -/
def group (i : Nat) : List Instr :=
  (if i < 12 then schedule (i + 4) else []) ++
    round 0 (4 * i) ++ round 0 (4 * i + 1) ++ round 0 (4 * i + 2) ++ round 0 (4 * i + 3)

/-- Groups `0 … n-1` of the first block. -/
def groups : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (groups n) (.block (group n))

/-- Rounds `0 … n-1` of the second block. -/
def rounds2 : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds2 n) (.block (round 1 n))

/-! ## The blocks -/

/-- The 128-bit constant `c` into both lanes of `x`, through `rax` and `tmp`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .vop (.vmovq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .vop (.vmovq tmp .rax),
   .vop (.vbin .vpunpcklqdq .l128 x x tmp), .vop (.vinserti128 x x x 1)]

def bswapMask : BitVec 128 := 0x0c0d0e0f08090a0b0405060700010203#128
def maskBA : BitVec 128 := 0xffffffffffffffff0b0a090803020100#128
def maskDC : BitVec 128 := 0x0b0a090803020100ffffffffffffffff#128

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 512), (.rbp, 520), (.r12, 528), (.r13, 536), (.r14, 544), (.r15, 552)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

/-- Load the hash value into the variables of round 0. -/
def loadState : List Instr := (List.range 8).map fun k => .mov32 (var 0 k) (.mem (at_ .rdi (4 * k)))

/-- Add the variables into the hash value (`64 % 8 = 0`, so after 64 rounds
they are in the registers of round 0), and leave the sum in them too. -/
def addState : List Instr :=
  (List.range 8).map (fun k => .alu32 .add (var 0 k) (.mem (at_ .rdi (4 * k)))) ++
  (List.range 8).map (fun k => .store32 (at_ .rdi (4 * k)) (var 0 k))

/-- One iteration: two blocks, or the last one. The second block is at
`rsi + 64` if there is one (`rdx ≥ 2`), and otherwise the first is loaded
twice; `r15` points at it while the words are loaded. -/
def body : Prog isa :=
  .seq (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)])
  (.seq (.ite .e (.block []) (.block [.alu .add T (.imm 64)]))
  (.seq (.block (load 0 ++ load 1 ++ load 2 ++ load 3 ++ loadState ++ initCarry))
  (.seq (groups 16)
  (.seq (.block addState)
  (.seq (.block [.alu .cmp .rdx (.imm 1)])
  (.ite .e
    (.block [.alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)])
    (.seq (.block initCarry)
    (.seq (rounds2 64)
      (.block (addState ++ [.alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 2)]))))))))))

def compress : Prog isa :=
  .seq (.block (save ++ const mBswap bswapMask ++ const mBA maskBA ++ const mDC maskDC ++
      [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block (restore ++ [.vop .vzeroupper])))

end VG.Impl.Sha256.X86_64.Avx2
