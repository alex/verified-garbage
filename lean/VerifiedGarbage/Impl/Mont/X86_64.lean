import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on x86-64

Arithmetic modulo an odd `m < 2^(64 n)`, `n` 64-bit words (`n ≤ 6`), on
numbers below `m` held in the working space as `n` little-endian words at a
constant offset from its base, which is in `rdi`. The modulus is in the
working space too, at `M.mo`; `M.minv` is `-m⁻¹ mod 2⁶⁴`. With
`R = 2^(64 n)`:

* `mul o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS): for each word `a_i` of `[a]`, the accumulator
  `t += a_i [b]`, then `t += u m` for `u = t₀ m' mod 2⁶⁴`, which makes the
  low word zero, and `t /= 2⁶⁴`. The `n + 2` accumulator words are
  registers (`acc n`); the division renames them (round `i`'s words are
  `win n i 0`, `win n i 1`, …), so it costs nothing. The accumulator stays
  below `2m`, and the result is reduced by `csub`.
* `add o a b`, `sub o a b`: `[a] ± [b] mod m`, with a conditional
  subtraction (`csub`) or addition of `m`.
* `csub`: a number below `2m` in `n` registers and a top word (0 or 1)
  reduced below `m`: the difference with `m` is computed into the
  temporary area `[M.tmp]`, and then selected with a mask if it did not
  borrow.

Every multiplication is `mul`, every selection a mask, and every address
`rdi` plus a constant: nothing but `rdi` may affect timing. The operations
use the registers `rax`, `rcx`, `rdx`, `rbp` and `acc n` (`r8`–`r13` for
`n = 4`), and write only `[o]` and `[M.tmp]`.
-/

namespace VG.Impl.Mont.X86_64

open VG.X86_64

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := { base := .rdi, disp := d }

/-- A modulus: its number of words `n`, where it is (`mo`, `n` words), the
working space's temporary area for `csub` (`tmp`, `n` words), and
`minv = -m⁻¹ mod 2⁶⁴`. -/
structure Mod where
  n : Nat
  mo : Nat
  tmp : Nat
  minv : BitVec 64

/-- The accumulator's registers: `n + 2` of `r8`–`r15`. -/
def acc (n : Nat) : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].take (n + 2)

/-- Word `j` of the accumulator in round `i`: the registers rotate by one
word each round. -/
def win (n i j : Nat) : Reg := (acc n).getD ((i + j) % (n + 2)) .r8

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). -/
def mulStep (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `ts, carry rbp += rcx · [d], …`: a multiply-accumulate step for each of
the words `ts` and the words at `d`, `d + 8`, …. -/
def mulSteps : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, d => mulStep t .rbp .rcx (.mem (sc d)) ++ mulSteps ts (d + 8)

/-- `ts += rcx · [d]`, its carry word in `rbp`. -/
def mulRow (ts : List Reg) (d : Nat) : List Instr := .mov32 .rbp (.imm 0) :: mulSteps ts d

/-- The carry word `rbp` added into `t_n` and its carry into `t_{n+1}`. -/
def carryUp (tn tn1 : Reg) : List Instr := [.alu .add tn (.reg .rbp), .alu .adc tn1 (.imm 0)]

/-- The words of round `i`'s accumulator, low to high. -/
def wins (n i : Nat) : List Reg := (List.range (n + 2)).map (win n i)

/-- Round `i` of `mul o a b`: `t += a_i [b]`, then `t += u m` with
`u = t₀ m' mod 2⁶⁴`, after which `t₀ = 0`. -/
def round (M : Mod) (a b i : Nat) : List Instr :=
  let t := win M.n i
  let low := (List.range M.n).map t
  [.mov .rcx (.mem (sc (a + 8 * i)))] ++ mulRow low b ++ carryUp (t M.n) (t (M.n + 1)) ++
  [.mov .rax (.reg (t 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] ++
    mulRow low M.mo ++ carryUp (t M.n) (t (M.n + 1))

/-- `[tmp + d] = ts - [mo + d]`, word by word, with `op` (`sub`, then
`sbb`) on the first word, through `rax`. -/
def diffs (op : AluOp) : List Reg → Nat → Nat → List Instr
  | [], _, _ => []
  | t :: ts, mo, tmp => [.mov .rax (.reg t), .alu op .rax (.mem (sc mo)), .store (sc tmp) .rax] ++
    diffs .sbb ts (mo + 8) (tmp + 8)

/-- `ts = [tmp]` where the mask `rax` is all ones, word by word. -/
def selects : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, tmp => [.mov .rdx (.mem (sc tmp)), .alu .xor .rdx (.reg t), .alu .and .rdx (.reg .rax),
      .alu .xor t (.reg .rdx)] ++ selects ts (tmp + 8)

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`: the
difference with `m` is computed into `[tmp]`; `rax` is all ones if it did not
borrow, and selects it. -/
def csub (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffs .sub ts M.mo M.tmp ++
  [.mov .rax (.reg top), .alu .sbb .rax (.imm 0), .alu .sbb .rax (.reg .rax),
    .alu .xor .rax (.imm (-1))] ++
  selects ts M.tmp

/-- `[o] = ts`. -/
def stores : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => .store (sc o) t :: stores ts (o + 8)

/-- `ts = [a]`. -/
def loads : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, a => .mov t (.mem (sc a)) :: loads ts (a + 8)

/-- `ts := 0`. -/
def zeros (ts : List Reg) : List Instr := ts.map fun t => .mov32 t (.imm 0)

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (o a b : Nat) : List Instr :=
  let low := (List.range M.n).map (win M.n M.n)
  zeros (acc M.n) ++ (List.range M.n).flatMap (round M a b) ++
    csub M low (win M.n M.n M.n) ++ stores low o

/-- `ts op= [b]`, word by word, with `op` on the first word and `op'` on the
others (`add` and `adc`, `sub` and `sbb`). -/
def chain (op op' : AluOp) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, b => .alu op t (.mem (sc b)) :: chain op' op' ts (b + 8)

/-- The low words and the top word of the sums and differences. -/
def low (n : Nat) : List Reg := (acc n).take n
def top (n : Nat) : Reg := (acc n).getD n .r8

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (o a b : Nat) : List Instr :=
  loads (low M.n) a ++ [.mov32 (top M.n) (.imm 0)] ++ chain .add .adc (low M.n) b ++
    [.alu .adc (top M.n) (.imm 0)] ++ csub M (low M.n) (top M.n) ++ stores (low M.n) o

/-- `[tmp] = [mo]` masked with `rax`, `n` words. -/
def masked : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, mo, tmp => [.mov .rdx (.mem (sc mo)), .alu .and .rdx (.reg .rax),
      .store (sc tmp) .rdx] ++ masked k (mo + 8) (tmp + 8)

/-- `[o] = [a] - [b] mod m`: the difference, and `m` added under the mask
`rax` of its borrow (through `[tmp]`). -/
def sub (M : Mod) (o a b : Nat) : List Instr :=
  loads (low M.n) a ++ chain .sub .sbb (low M.n) b ++ [.alu .sbb .rax (.reg .rax)] ++
    masked M.n M.mo M.tmp ++ chain .add .adc (low M.n) M.tmp ++ stores (low M.n) o

end VG.Impl.Mont.X86_64
