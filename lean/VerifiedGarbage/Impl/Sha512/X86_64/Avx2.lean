import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SHA-512 compression function: x86-64 implementation with AVX2 and BMI

`vg_sha512_compress_avx2(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the contract of `vg_sha512_compress`, for CPUs with AVX, AVX2, BMI1 and
BMI2. This is the technique of OpenSSL's AVX2+BMI2 SHA-512
(`sha512-x86_64.pl`, by Andy Polyakov): two blocks at a time, their message
schedules computed together in the two 128-bit lanes of the `ymm`
registers, and the rounds in general-purpose registers.

* The message schedule of the two blocks is kept two words to a register,
  `W₂ᵢ` and `W₂ᵢ₊₁` of the first block in lane 0 and of the second in lane 1
  of `msg i` (`ymm0 … ymm7`), and stored to `scratch[32i..32i+32)`, from
  which the rounds of each block read it (lane 0 at `32i`, lane 1 at
  `32i + 16`). Words `2i+16` and `2i+17` are computed during rounds `2i` and
  `2i+1` of the first block, with `ymm8 … ymm11` as temporaries; `ymm12`
  holds the `pshufb` mask that makes the words big-endian. AVX2 has no
  rotation, so `σ₀` and `σ₁` rotate by a shift each way.
* The working variables `a … h` are renamed by the unrolled rounds as in
  `vg_sha512_compress` (`var`); `Σ₀` and `Σ₁` are three `rorx`, `Ch(e, f, g)`
  is `(e ∧ f) + (¬e ∧ g)`, and `Maj(a, b, c)` is `((a ⊕ b) ∧ (b ⊕ c)) ⊕ b`,
  where `b ⊕ c` is the previous round's `a ⊕ b`, kept in `carry t`. `Kₜ` is
  loaded with `movabs`, since the model has no constant pool. `Kₜ + Wₜ` is
  added to `h` first, so that only `Σ₁(e)` and `Ch(e, f, g)` stand between
  `e` and the next round's.
* If only one block is left, it is loaded into both lanes and only the
  first block's rounds run.
* `rbx, rbp, r12–r15` are saved in `scratch[1280..1328)` and restored on
  exit; `vzeroupper` before returning avoids the penalty of dirty upper
  halves in the caller's SSE code.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sha512.X86_64.Avx2

open VG.X86_64
open VG.Spec.Sha512 (K)

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
def wSlot (j t : Nat) : MemOp := at_ .rcx (32 * (t / 2) + 16 * j + 8 * (t % 2))

/-- Round `t` of block `j`: `T₁ = h + Kₜ + Wₜ + Ch(e, f, g) + Σ₁(e)`,
`T₂ = Σ₀(a) + Maj(a, b, c)`. -/
def round (j t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  let x := carry t; let y := carry (t + 1)
  [ -- h := h + Kₜ + Wₜ
    .movImm64 y (K t), .alu .add h (.reg y),
    .alu .add h (.mem (wSlot j t)),
    -- h := h + Ch(e, f, g), as (e ∧ f) + (¬e ∧ g)
    .mov y (.reg e), .alu .and y (.reg f), .andn T e g, .alu .add y (.reg T),
    .alu .add h (.reg y),
    -- h := h + Σ₁(e), which is T₁
    .rorx y e 14, .rorx T e 18, .alu .xor y (.reg T), .rorx T e 41, .alu .xor y (.reg T),
    .alu .add h (.reg y),
    -- e' := d + T₁
    .alu .add d (.reg h),
    -- h := h + Σ₀(a)
    .rorx y a 28, .rorx T a 34, .alu .xor y (.reg T), .rorx T a 39, .alu .xor y (.reg T),
    .alu .add h (.reg y),
    -- h := h + Maj(a, b, c), as ((a ⊕ b) ∧ (b ⊕ c)) ⊕ b, with b ⊕ c in x;
    -- a ⊕ b, in y, is the next round's b ⊕ c
    .mov y (.reg a), .alu .xor y (.reg b), .alu .and x (.reg y), .alu .xor x (.reg b),
    .alu .add h (.reg x)]

/-- Set up `carry 0 = b ⊕ c` for the rounds. -/
def initCarry : List Instr := [.mov (carry 0) (.reg (var 0 1)), .alu .xor (carry 0) (.reg (var 0 2))]

/-! ## Message schedule -/

/-- The register holding `W₂ᵢ` and `W₂ᵢ₊₁` of both blocks. -/
def msg (i : Nat) : XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7].getD (i % 8) .xmm0

def t0 : XReg := .xmm8
def t1 : XReg := .xmm9
def t2 : XReg := .xmm10
def t3 : XReg := .xmm11
/-- `pshufb` mask: big-endian words. -/
def mBswap : XReg := .xmm12
def tmp : XReg := .xmm13

def vb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)
def vs (op : XShiftOp) (d a : XReg) (n : BitVec 8) : Instr := .vop (.vshift op .l256 d a n)

/-- `W₂ᵢ` and `W₂ᵢ₊₁` of both blocks into `msg i` (for `i ≥ 8`), from the
previous sixteen words (whose register `msg i` held the oldest two), and
stored. -/
def schedule (i : Nat) : List Instr :=
  let x0 := msg i; let x1 := msg (i + 1); let x4 := msg (i + 4); let x5 := msg (i + 5)
  let x7 := msg (i + 7)
  [ .vop (.vpalignr .l256 t0 x1 x0 8),      -- W₂ᵢ₋₁₅, W₂ᵢ₋₁₄
    .vop (.vpalignr .l256 t1 x5 x4 8),      -- W₂ᵢ₋₇, W₂ᵢ₋₆
    vb .vpaddq x0 x0 t1,                    -- W₂ᵢ₋₁₆ + W₂ᵢ₋₇, …
    -- σ₀(W₂ᵢ₋₁₅, W₂ᵢ₋₁₄): ror 1, ror 8, shr 7
    vs .psrlq t2 t0 1,
    vs .psllq t3 t0 63,
    vb .vpxor t2 t2 t3,
    vs .psrlq t3 t0 8,
    vb .vpxor t2 t2 t3,
    vs .psllq t3 t0 56,
    vb .vpxor t2 t2 t3,
    vs .psrlq t3 t0 7,
    vb .vpxor t2 t2 t3,
    vb .vpaddq x0 x0 t2,
    -- σ₁(W₂ᵢ₋₂, W₂ᵢ₋₁): ror 19, ror 61, shr 6
    vs .psrlq t2 x7 19,
    vs .psllq t3 x7 45,
    vb .vpxor t2 t2 t3,
    vs .psrlq t3 x7 61,
    vb .vpxor t2 t2 t3,
    vs .psllq t3 x7 3,
    vb .vpxor t2 t2 t3,
    vs .psrlq t3 x7 6,
    vb .vpxor t2 t2 t3,
    vb .vpaddq x0 x0 t2,                    -- W₂ᵢ, W₂ᵢ₊₁
    .vmovdquStore .l256 (at_ .rcx (32 * i)) x0]

/-- `W₂ᵢ` and `W₂ᵢ₊₁` (`i < 8`) of the blocks at `rsi` and `r15` into `msg i`, and stored. -/
def load (i : Nat) : List Instr :=
  [.vmovdquLoad .l128 (msg i) (at_ .rsi (16 * i)), .vmovdquLoad .l128 tmp (at_ T (16 * i)),
   .vop (.vinserti128 (msg i) (msg i) tmp 1), vb .vpshufb (msg i) (msg i) mBswap,
   .vmovdquStore .l256 (at_ .rcx (32 * i)) (msg i)]

/-- Rounds `2i` and `2i+1` of the first block, computing words `2i+16` and
`2i+17` meanwhile. -/
def group (i : Nat) : List Instr :=
  (if i < 32 then schedule (i + 8) else []) ++ round 0 (2 * i) ++ round 0 (2 * i + 1)

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

def bswapMask : BitVec 128 := 0x08090a0b0c0d0e0f0001020304050607#128

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 1280), (.rbp, 1288), (.r12, 1296), (.r13, 1304), (.r14, 1312), (.r15, 1320)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

/-- Load the hash value into the variables of round 0. -/
def loadState : List Instr := (List.range 8).map fun k => .mov (var 0 k) (.mem (at_ .rdi (8 * k)))

/-- Add the variables into the hash value (`80 % 8 = 0`, so after 80 rounds
they are in the registers of round 0), and leave the sum in them too. -/
def addState : List Instr :=
  (List.range 8).map (fun k => .alu .add (var 0 k) (.mem (at_ .rdi (8 * k)))) ++
  (List.range 8).map (fun k => .store (at_ .rdi (8 * k)) (var 0 k))

/-- One iteration: two blocks, or the last one. The second block is at
`rsi + 128` if there is one (`rdx ≥ 2`), and otherwise the first is loaded
twice; `r15` points at it while the words are loaded. -/
def body : Prog isa :=
  .seq (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)])
  (.seq (.ite .e (.block []) (.block [.alu .add T (.imm 128)]))
  (.seq (.block (load 0 ++ load 1 ++ load 2 ++ load 3 ++ load 4 ++ load 5 ++ load 6 ++ load 7 ++
    loadState ++ initCarry))
  (.seq (groups 40)
  (.seq (.block addState)
  (.seq (.block [.alu .cmp .rdx (.imm 1)])
  (.ite .e
    (.block [.alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)])
    (.seq (.block initCarry)
    (.seq (rounds2 80)
      (.block (addState ++ [.alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 2)]))))))))))

def compress : Prog isa :=
  .seq (.block (save ++ const mBswap bswapMask ++ [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block (restore ++ [.vop .vzeroupper])))

end VG.Impl.Sha512.X86_64.Avx2
