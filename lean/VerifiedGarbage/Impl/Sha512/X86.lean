import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86.Isa

/-!
# SHA-512 compression function: x86 (32-bit) implementation

`vg_sha512_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

* Each 64-bit word is a pair of 32-bit words, the low one first (as in
  memory: little-endian). `add` of the low halves and `adc` of the high
  halves add two words. The model has no left shift: the bits a 64-bit
  rotation or shift moves from one half into the other are the half rotated
  right with `ror`, the bits that wrapped around masked off with `and`.
* With only seven usable registers, everything lives in memory: the
  working variables `a … h` in `scratch[0..64)`, renamed between the fully
  unrolled rounds (in round `t`, variable `k` is at `vOff t k`); the 16-word
  message-schedule window in `scratch[64..192)` (word `Wₜ` for `t < 16` made
  from the block's big-endian bytes `8t … 8t + 7`: `bswap` of each half, and
  the halves swapped; `Wₜ` for `t ≥ 16` replaces `Wₜ₋₁₆`); the saved `ebx`,
  `esi`, `edi`, `ebp` in `scratch[192..208)`; and the count of blocks left in
  `scratch[208..212)`.
* `esi` points to the scratch buffer and `edi` to the current block; the
  hash value's address is read from its argument slot when needed. The
  temporaries are `eax` and the pairs `(ebx, ebp)` and `(ecx, edx)`.
* The pointers, the block count and `esp` are public; no address and no
  branch depends on anything else.
-/

namespace VG.Impl.Sha512.X86

open VG.X86
open VG.Spec.Sha512 (K)

/-- The low half of a 64-bit word. -/
def lo (x : BitVec 64) : BitVec 32 := x.extractLsb' 0 32

/-- The high half of a 64-bit word. -/
def hi (x : BitVec 64) : BitVec 32 := x.extractLsb' 32 32

/-- `++`, grouping to the right. The kernel evaluates the code (for the
constant-time analysis), and `(a ++ b) ++ c` has it copy `a` twice: for the
rounds, several times slower than `a ++ (b ++ c)`. -/
local infixr:65 " +++ " => HAppend.hAppend

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[esi + d]` -/
def sc (d : Nat) : Src := .mem (at_ .esi d)

/-- The temporary register, and the register pairs (low, high). -/
def T : Reg := .eax
def Y0 : Reg := .ebx
def Y1 : Reg := .ebp
def Z0 : Reg := .ecx
def Z1 : Reg := .edx

/-- The offset in the scratch buffer of `W[j mod 16]`. -/
def wOff (j : Nat) : Nat := 64 + 8 * (j % 16)

/-- The offset in the scratch buffer of working variable `k` (`a = 0, …, h = 7`)
at the start of round `t`. -/
def vOff (t k : Nat) : Nat := 8 * ((k + 8 - t % 8) % 8)

/-- Where the count of blocks left is. -/
def cntOff : Nat := 208

/-- Load the word at `[esi + off]` into `l` (low half) and `h`. -/
def ld (l h : Reg) (off : Nat) : List Instr := [.mov l (sc off), .mov h (sc (off + 4))]

/-- Store `l` (low half) and `h` as the word at `[esi + off]`. -/
def st (l h : Reg) (off : Nat) : List Instr := [.store (at_ .esi off) l, .store (at_ .esi (off + 4)) h]

/-- `(dl, dh) := (dl, dh) + (l, h)` -/
def add64 (dl dh l h : Reg) : List Instr := [.alu .add dl (.reg l), .alu .adc dh (.reg h)]

/-- `(dl, dh) := (dl, dh) +` the word at `[esi + off]` -/
def add64m (dl dh : Reg) (off : Nat) : List Instr := [.alu .add dl (sc off), .alu .adc dh (sc (off + 4))]

/-- `(dl, dh) := (dl, dh) + k` -/
def add64i (dl dh : Reg) (k : BitVec 64) : List Instr := [.alu .add dl (.imm (lo k)), .alu .adc dh (.imm (hi k))]

/-- A term of `Σ₀`, `Σ₁`, `σ₀` or `σ₁`. -/
inductive Op
  /-- `ROTRⁿ` (`0 < n < 64`, `n ≠ 32`) -/
  | rotr (n : Nat)
  /-- `SHRⁿ` (`0 < n < 32`) -/
  | shr (n : Nat)
  deriving DecidableEq, Repr

/-- A part of one half of a term: one half (the high one if `h`) of the word,
shifted right or left. -/
inductive Part
  /-- `half >>> n` (`0 < n < 32`) -/
  | shr (h : Bool) (n : Nat)
  /-- `half <<< n` (`0 < n < 32`) -/
  | shl (h : Bool) (n : Nat)
  deriving DecidableEq, Repr

/-- The low half of a term, as two parts (with no bits in common). -/
def Op.lo : Op → List Part
  | .rotr n => if n < 32 then [.shr false n, .shl true (32 - n)] else [.shr true (n - 32), .shl false (64 - n)]
  | .shr n => [.shr false n, .shl true (32 - n)]

/-- The high half of a term. -/
def Op.hi : Op → List Part
  | .rotr n => if n < 32 then [.shr true n, .shl false (32 - n)] else [.shr false (n - 32), .shl true (64 - n)]
  | .shr n => [.shr true n]

/-- `d :=` the part `p` of the word at `[esi + off]`. A left shift by `n` is a
rotation right by `32 - n` with the `32 - n` bits that wrapped around masked
off. -/
def Part.load (d : Reg) (off : Nat) : Part → List Instr
  | .shr h n => [.mov d (sc (if h then off + 4 else off)), .shift .shr d n]
  | .shl h n => [.mov d (sc (if h then off + 4 else off)), .shift .ror d (32 - n),
      .alu .and d (.imm (BitVec.allOnes 32 <<< n))]

/-- `d := p₀ ⊕ p₁ ⊕ …`, the parts of the word at `[esi + off]`, with `T` as a temporary. -/
def xorOf (d : Reg) (off : Nat) : List Part → List Instr
  | [] => []
  | p :: ps => p.load d off +++ ps.flatMap fun p => p.load T off +++ [.alu .xor d (.reg T)]

/-- `(dl, dh) :=` the exclusive or of the terms `ops` of the word at `[esi + off]`. -/
def sig (dl dh : Reg) (off : Nat) (ops : List Op) : List Instr :=
  xorOf dl off (ops.flatMap Op.lo) +++ xorOf dh off (ops.flatMap Op.hi)

/-- The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁`. -/
def bsig0 : List Op := [.rotr 28, .rotr 34, .rotr 39]
def bsig1 : List Op := [.rotr 14, .rotr 18, .rotr 41]
def ssig0 : List Op := [.rotr 1, .rotr 8, .shr 7]
def ssig1 : List Op := [.rotr 19, .rotr 61, .shr 6]

/-- One half of `Ch(e, f, g)` into `d`, the halves of `e`, `f`, `g` at
`[esi + e]`, `[esi + f]`, `[esi + g]`, as `((f ⊕ g) ∧ e) ⊕ g`. -/
def ch1 (d : Reg) (e f g : Nat) : List Instr :=
  [.mov d (sc f), .alu .xor d (sc g), .alu .and d (sc e), .alu .xor d (sc g)]

/-- `(Z0, Z1) := Ch(e, f, g)`. -/
def chW (e f g : Nat) : List Instr := ch1 Z0 e f g +++ ch1 Z1 (e + 4) (f + 4) (g + 4)

/-- One half of `Maj(a, b, c)` into `d`, as `((a ∨ b) ∧ c) ∨ (a ∧ b)`, with `T`
as a temporary. -/
def maj1 (d : Reg) (a b c : Nat) : List Instr :=
  [.mov d (sc a), .alu .or d (sc b), .alu .and d (sc c), .mov T (sc a), .alu .and T (sc b),
   .alu .or d (.reg T)]

/-- `(Z0, Z1) := Maj(a, b, c)`. -/
def majW (a b c : Nat) : List Instr := maj1 Z0 a b c +++ maj1 Z1 (a + 4) (b + 4) (c + 4)

/-- `Wₜ` for `t < 16`, from the block's bytes at `[edi + i]`, stored at `[esi + o]`. -/
def loadW (i o : Nat) : List Instr :=
  [.mov Z0 (.mem (at_ .edi (i + 4))), .mov Z1 (.mem (at_ .edi i)), .bswap Z0, .bswap Z1] +++ st Z0 Z1 o

/-- `Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆` for `t ≥ 16`, with `Wₜ₋ᵢ` at
`[esi + oᵢ]`, in place of `Wₜ₋₁₆`. The additions are in the order of the
specification. -/
def expandW (o2 o7 o15 o16 : Nat) : List Instr :=
  sig Y0 Y1 o2 ssig1 +++ add64m Y0 Y1 o7 +++ sig Z0 Z1 o15 ssig0 +++ add64 Y0 Y1 Z0 Z1 +++
  add64m Y0 Y1 o16 +++ st Y0 Y1 o16

/-- Store `Wₜ` in its slot. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then loadW (8 * t) (wOff t) else expandW (wOff (t + 14)) (wOff (t + 9)) (wOff (t + 1)) (wOff t)

/-- A round with the working variables at `[esi + a]`, …, `[esi + h]`, the
constant `k` and the message word at `[esi + w]`. The additions are in the
order of the specification: `T₁` is accumulated in `(Y0, Y1)`, `d + T₁` in
`(Z0, Z1)`, and then `T₁ + T₂` in `(Y0, Y1)`. -/
def roundW (a b c d e f g h : Nat) (k : BitVec 64) (w : Nat) : List Instr :=
  -- T₁ := h + Σ₁(e) + Ch(e, f, g) + Kₜ + Wₜ
  sig Z0 Z1 e bsig1 +++ ld Y0 Y1 h +++ add64 Y0 Y1 Z0 Z1 +++
  chW e f g +++ add64 Y0 Y1 Z0 Z1 +++ add64i Y0 Y1 k +++ add64m Y0 Y1 w +++
  -- e' := d + T₁
  ld Z0 Z1 d +++ add64 Z0 Z1 Y0 Y1 +++ st Z0 Z1 d +++
  -- a' := (T₁ + Σ₀(a)) + Maj(a, b, c)
  sig Z0 Z1 a bsig0 +++ add64 Y0 Y1 Z0 Z1 +++ majW a b c +++ add64 Y0 Y1 Z0 Z1 +++
  st Y0 Y1 h

/-- Round `t`. -/
def round (t : Nat) : List Instr :=
  roundW (vOff t 0) (vOff t 1) (vOff t 2) (vOff t 3) (vOff t 4) (vOff t 5) (vOff t 6) (vOff t 7)
    (K t) (wOff t)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- Copy word `k` of the hash value at `ecx` to the working variables (`vOff 0 k = 8k`). -/
def loadH (k : Nat) : List Instr :=
  [.mov T (.mem (at_ .ecx (8 * k))), .store (at_ .esi (8 * k)) T,
   .mov T (.mem (at_ .ecx (8 * k + 4))), .store (at_ .esi (8 * k + 4)) T]

/-- Add word `k` of the working variables (`80 % 8 = 0`, so at `vOff 80 k = 8k`)
into the hash value at `ecx`, as `a + H₀` etc. -/
def addH (k : Nat) : List Instr :=
  [.mov T (sc (8 * k)), .mov Z1 (sc (8 * k + 4)), .alu .add T (.mem (at_ .ecx (8 * k))),
   .alu .adc Z1 (.mem (at_ .ecx (8 * k + 4))), .store (at_ .ecx (8 * k)) T,
   .store (at_ .ecx (8 * k + 4)) Z1]

def load : List Instr := .mov .ecx (.mem (at_ .esp 4)) :: (List.range 8).flatMap loadH

def update : List Instr := .mov .ecx (.mem (at_ .esp 4)) :: (List.range 8).flatMap addH

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr :=
  [.alu .add .edi (.imm 128), .mov T (sc cntOff), .alu .sub T (.imm 1), .store (at_ .esi cntOff) T]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 192), (.esi, 196), (.edi, 200), (.ebp, 204)]

/-- Save the callee-saved registers, load the arguments, and set ZF if there
are no blocks. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 16))] ++
  saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)), .mov .eax (.mem (at_ .esp 12)),
   .store (at_ .esi cntOff) .eax, .alu .test .eax (.reg .eax)]

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (sc 192), .mov .edi (sc 200), .mov .ebp (sc 204), .mov .esi (sc 196)]

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Sha512.X86
