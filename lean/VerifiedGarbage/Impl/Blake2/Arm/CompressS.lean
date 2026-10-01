import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.Arm.Isa

/-!
# BLAKE2s compression function: 32-bit ARM implementation

`vg_blake2s_compress(state = r0, blocks = r1, n = r2, t = [sp]:[sp, #4],
last = [sp, #8], scratch = [sp, #12])` (AAPCS: the 64-bit `t` cannot take
`r3`, so it and the arguments after it are on the stack).

* There are only 14 registers, so `scratch` (in `r12`) holds what does not
  fit: `scratch[0, 64)` is a copy of the block (the message words), and
  `scratch[64, 80)` words 8–11 of the work vector `v` (the third row, `c` of
  every `G`), which each `G` loads into the temporary `lr` and stores back.
  Words 0–3 are in `r0`–`r3`, words 4–7 in `r4`–`r7` and words 12–15 in
  `r8`–`r11` (`wreg`).
* ARM's second operand can be rotated for free (`eor d, a, d, ror #8`), so
  the rotations of `G` are folded into the instructions that use their
  results: words 4–7 are kept rotated left by 7 (`v[k] = r ror 7`) and words
  12–15 rotated left by 8 (`v[k] = r ror 8`), which is what the last
  rotations of `G` leave, and the other rotations are applied as operands.
  `G` is then six additions and four exclusive-ors, two loads of message
  words and the load and store of its third-row word (`g`). The rows are
  rotated into this form as they are loaded, and out of it as the halves are
  added into the hash value.
* The rest of `scratch` holds `state` (80), the block pointer (84), the
  count of blocks left (88), the counter of the current block (92, 96), the
  final block flag word (100: all ones if `last ≠ 0`, computed without a
  branch), a zero word (104, so that each word of the fourth row is set up
  alike), and our caller's `r4`–`r11` and `lr` (108–140).
* The rounds are fully unrolled. The only branches are on `n`, and every
  address is `scratch`, `state` or a block pointer plus a constant, so only
  the pointers and `n` can affect timing.
-/

namespace VG.Impl.Blake2.Arm.S

open VG.Arm

/-- The scratch pointer and the temporary. -/
def S : Reg := .r12
def T : Reg := .lr

/-- The register holding word `k` (not 8–11) of the work vector. -/
def wreg (k : Nat) : Reg :=
  [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r0, .r0, .r0, .r0, .r8, .r9, .r10, .r11].getD k .r0

/-! ## The layout of `scratch` -/

/-- Word `k` (8–11) of the work vector. -/
def cOff (k : Nat) : Nat := 32 + 4 * k
def stOff : Nat := 80
def blkOff : Nat := 84
def nOff : Nat := 88
def tOff : Nat := 92
def fOff : Nat := 100
/-- What word `k` (12–15) of the work vector is XORed with: the counter's
low and high words, the flag word and zero. -/
def xOff (k : Nat) : Nat := 44 + 4 * k

/-- The callee-saved registers we use (and `lr`), and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 108), (.r5, 112), (.r6, 116), (.r7, 120), (.r8, 124), (.r9, 128), (.r10, 132), (.r11, 136),
    (.lr, 140)]

/-- `d := v`. -/
def movImm (d : Reg) (v : BitVec 32) : List Instr :=
  [.movw d (v.extractLsb' 0 16), .movt d (v.extractLsb' 16 16)]

/-! ## The rounds -/

/-- `G` (RFC 7693 §3.1) on `a` (in `a`), `b` (rotated left by 7, in `b`), `c`
(at `scratch + cOff c`) and `d` (rotated left by 8, in `d`), with the message
words `x` and `y`; it leaves `b` and `d` rotated likewise. -/
def g (a b d : Reg) (c x y : Nat) : List Instr := [
  .ldr T S (4 * x),
  .dp .add a a (.shifted b .ror 7), .dp .add a a (.reg T),
  .dp .eor d a (.shifted d .ror 8),
  .ldr T S (4 * y), .dp .add a a (.reg T),
  .ldr T S (cOff c), .dp .add T T (.shifted d .ror 16),
  .dp .eor b T (.shifted b .ror 7),
  .dp .add a a (.shifted b .ror 12),
  .dp .eor d a (.shifted d .ror 16),
  .dp .add T T (.shifted d .ror 8),
  .dp .eor b T (.shifted b .ror 12),
  .str T S (cOff c)]

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of the
round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g (wreg x) (wreg y) (wreg u) z (Spec.Blake2.sigmaAt r (2 * i)) (Spec.Blake2.sigmaAt r (2 * i + 1)))

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (gAt r 0 0 4 8 12) <| .seq (gAt r 1 1 5 9 13) <| .seq (gAt r 2 2 6 10 14) <|
  .seq (gAt r 3 3 7 11 15) <| .seq (gAt r 4 0 5 10 15) <| .seq (gAt r 5 1 6 11 12) <|
  .seq (gAt r 6 2 7 8 13) (gAt r 7 3 4 9 14)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

/-! ## One block -/

/-- Copy words `0 … n-1` of the block (at `r0`) to `scratch`. -/
def copyMsg : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (copyMsg n) (.block [.ldr T .r0 (4 * n), .str T S (4 * n)])

/-- Word `k` (0–7) of the state (at `r11`) into its register; words 4–7
rotated left by 7 (right by 25). -/
def ld (k : Nat) : List Instr :=
  .ldr (wreg k) .r11 (4 * k) :: if k < 4 then [] else [.mov (wreg k) (.shifted (wreg k) .ror 25)]

/-- Words `0 … n-1` of the state. -/
def lds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (lds n) (.block (ld n))

/-- Word `k` (8–11) of the work vector: `IV[k - 8]`. -/
def ivC (k : Nat) : List Instr :=
  movImm T (Spec.Blake2.s.IV.toList.getD (k - 8) 0) ++ [.str T S (cOff k)]

/-- Word `k` (12–15) of the work vector, rotated left by 8: `IV[k - 8]` XORed
with the word at `xOff k`. -/
def ivD (k : Nat) : List Instr :=
  movImm (wreg k) ((Spec.Blake2.s.IV.toList.getD (k - 8) 0).rotateLeft 8) ++
    [.ldr T S (xOff k), .dp .eor (wreg k) (wreg k) (.shifted T .ror 24)]

/-- Words `8 … n+7` of the work vector. -/
def ivCs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (ivCs n) (.block (ivC (n + 8)))

/-- Words `12 … n+11` of the work vector. -/
def ivDs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (ivDs n) (.block (ivD (n + 12)))

/-- Initialize the work vector (RFC 7693 §3.2): copy the block, advance the
block pointer, and set up the four rows. -/
def init : Prog isa :=
  .seq (.block [.ldr .r0 S blkOff]) <| .seq (copyMsg 16) <|
  .seq (.block [.dp .add .r0 .r0 (.imm 64), .str .r0 S blkOff, .ldr .r11 S stOff]) <|
  .seq (lds 8) <| .seq (ivCs 4) (ivDs 4)

/-- `h[k] ^= v[k] ^ v[k + 8]` for `k` = 4–7, first folding word `k + 8` into
word `k`: `b ^ (d ror 1)`, rotated right by 7, is `v[k] ^ v[k + 8]`. -/
def finX (k : Nat) : List Instr := [.dp .eor (wreg k) (wreg k) (.shifted (wreg (k + 8)) .ror 1)]

def finHi (k : Nat) : List Instr :=
  [.ldr T .r8 (4 * k), .dp .eor T T (.shifted (wreg k) .ror 7), .str T .r8 (4 * k)]

/-- `h[k] ^= v[k] ^ v[k + 8]` for `k` = 0–3, with the state at `r8`. -/
def finLo (k : Nat) : List Instr :=
  [.ldr T S (cOff (k + 8)), .dp .eor (wreg k) (wreg k) (.reg T), .ldr T .r8 (4 * k),
    .dp .eor T T (.reg (wreg k)), .str T .r8 (4 * k)]

/-- XOR the work vector into the state (at `r8`), with the block pointer and
the count of blocks left in `r9` and `r10` (see `advance`). -/
def fin : Prog isa :=
  .seq (.block (finX 4 ++ finX 5 ++ finX 6 ++ finX 7 ++ [.ldr .r8 S stOff, .ldr .r9 S blkOff, .ldr .r10 S nOff])) <|
  .seq (.block (finHi 4)) <| .seq (.block (finHi 5)) <| .seq (.block (finHi 6)) <|
  .seq (.block (finHi 7)) <| .seq (.block (finLo 0)) <| .seq (.block (finLo 1)) <|
  .seq (.block (finLo 2)) (.block (finLo 3))

/-- Advance the counter by the block size, store the state and block pointers
and count the block (setting Z when none are left). The pointers and the
count were loaded before the state was written (`fin`), and are stored again:
what the taint analysis knows of `scratch` does not survive stores of secrets
through a register that is not a known base of a region. -/
def advance : List Instr :=
  [.ldr .r0 S tOff, .ldr .r1 S (tOff + 4), .adds .r0 .r0 (.imm 64), .adc .r1 .r1 (.imm 0),
    .str .r0 S tOff, .str .r1 S (tOff + 4), .str .r8 S stOff, .str .r9 S blkOff, .subs .r10 .r10 (.imm 1),
    .str .r10 S nOff]

def body : Prog isa :=
  .seq init (.seq (rounds 10) (.seq fin (.block advance)))

/-! ## The whole function -/

def save : List Instr := saved.map fun (r, d) => .str r S d
def restore : List Instr := saved.map fun (r, d) => .ldr r S d

/-- Load `scratch`, keep the counter, the arguments and our caller's registers
in it, and the flag word: with `z` = `last`, `0 - ((0 - z | z) >> 31)`; and
a zero word. The stack arguments are read first, through `r3`. -/
def setup : List Instr :=
  [.ldrSp S 12, .ldrSp .r3 0, .str .r3 S tOff, .ldrSp .r3 4, .str .r3 S (tOff + 4), .ldrSp .r3 8] ++ save ++
  [.str .r0 S stOff, .str .r1 S blkOff, .str .r2 S nOff, .mov T (.imm 0), .dp .sub T T (.reg .r3),
    .dp .orr T T (.reg .r3), .mov T (.shifted T .lsr 31), .mov .r3 (.imm 0), .dp .sub T .r3 (.reg T),
    .str T S fOff, .str .r3 S (fOff + 4), .cmp .r2 (.imm 0)]

def compress : Prog isa :=
  .seq (.block setup) (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Blake2.Arm.S
