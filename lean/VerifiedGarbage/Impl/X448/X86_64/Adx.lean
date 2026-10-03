import VerifiedGarbage.Impl.X448.X86_64

/-!
# X448: x86-64 implementation with BMI2 and ADX

`vg_x448_adx`: the code of `vg_x448` (`Impl/X448/X86_64.lean`) with other
field multiplications (`adx`), using `mulx` (BMI2), which multiplies by `rdx`
without touching the flags, and `adcx` and `adox` (ADX), which add with a
carry in CF and in OF alone: each row of a product runs two carry chains at
once, the low halves of the products through OF and the high halves through
CF.

* `mulX`: the 896-bit product row by row (operand scanning): row `i` adds
  `b_i · a` into an eight-word window of `r8–r15`, whose lowest word is then
  word `i` of the product, stored at `ACC`, and whose register becomes the
  next window's top word; the last window is the product's high half, stored
  too; then `reduce`, as `mul`'s.
* `sqrX`: the cross products `a_i a_j` (`i < j`) once, by rows of the same
  kind (row `i` adds `a_i · (a_{i+1}, …, a_6)` into the words `2i + 1` to
  `i + 7`, of which the two lowest are then final and stored), then the
  words doubled (through CF) and the squares `a_i²` added (through OF), two
  words a step, and `reduce`.

The rest, including `mulSmall`, is `vg_x448`'s.
-/

namespace VG.Impl.X448.X86_64

open VG.X86_64

/-- `xor ebp, ebp`: `rbp = 0`, CF and OF clear. -/
def clear : Instr := .alu32 .xor .rbp (.reg .rbp)

/-- `mulx rcx, rax, src`, `adox x, rax`, `adcx y, rcx`: `rdx · src` added at
`x` and `y` (the next word), the low half through OF and the high half
through CF. -/
def madd (x y : Reg) (src : Src) : List Instr :=
  [.mulx .rcx .rax src, .adox x (.reg .rax), .adcx y (.reg .rcx)]

/-- `madd` along the registers `xs`, by the sources `ss`. -/
def madds : List Reg → List Src → List Instr
  | x :: y :: xs, s :: ss => madd x y s ++ madds (y :: xs) ss
  | _, _ => []

/-- The window's registers in row `i`: they rotate, the lowest word of one
row becoming the top word of the next once stored. -/
def win (i k : Nat) : Reg := [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].getD ((i + k) % 8) .r8

/-- The lowest `n` words of row `i`'s window. -/
def wins (i n : Nat) : List Reg := (List.range n).map (win i)

/-- Row `i` of `[a] · [b]`: `win i 0..7 = win i 0..6 + b_i · a` (the top word
cleared first, the last carry through OF added to it), then `win i 0` (word
`i` of the product) stored. -/
def rowX (a b i : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (b + 8 * i))), .mov32 (win i 7) (.imm 0), clear] ++
    madds (wins i 8) ((List.range 7).map fun j => .mem (sc (a + 8 * j))) ++
    [.adox (win i 7) (.reg .rbp), .store (sc (h i)) (win i 0)]

/-- `[o] = [a] · [b]`: the window cleared, seven rows, the high half stored,
and `reduce`. -/
def mulX (o a b : Nat) : List Instr :=
  ((wins 0 7).map fun r => .mov32 r (.imm 0)) ++ (List.range 7).flatMap (rowX a b) ++
    stores (h 7) (wins 7 7) ++ reduce o

/-- Row `i` of the cross products of `[a]²`: the words `2i + 1, …, i + 7`
(word `k` in `win 0 k`, the top one cleared first) plus `a_i · (a_{i+1}, …,
a_6)`, then the two lowest stored. -/
def sqRow (a i : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 8 * i))), .mov32 (win (2 * i + 1) (6 - i)) (.imm 0), clear] ++
    madds (wins (2 * i + 1) (7 - i))
      ((List.range (6 - i)).map fun j => .mem (sc (a + 8 * (i + 1) + 8 * j))) ++
    [.adox (win (2 * i + 1) (6 - i)) (.reg .rbp), .store (sc (h (2 * i + 1))) (win (2 * i + 1) 0),
      .store (sc (h (2 * i + 2))) (win (2 * i + 1) 1)]

/-- Words `2i` and `2i + 1` of `[a]²`: those of the cross products doubled
(`adcx`), plus `a_i²` (`adox`). -/
def dblRow (a i : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 8 * i))), .mulx .rcx .rax (.reg .rdx),
    .mov .r8 (.mem (sc (h (2 * i)))), .adcx .r8 (.reg .r8), .adox .r8 (.reg .rax),
    .mov .r9 (.mem (sc (h (2 * i + 1)))), .adcx .r9 (.reg .r9), .adox .r9 (.reg .rcx),
    .store (sc (h (2 * i))) .r8, .store (sc (h (2 * i + 1))) .r9]

/-- `[o] = [a]²`: the window and the cross products' words 0 and 13 cleared,
six rows of cross products, the doubling and the squares, and `reduce`. -/
def sqrX (o a : Nat) : List Instr :=
  ((wins 1 6).map fun r => .mov32 r (.imm 0)) ++
    [.store (sc (h 0)) (win 1 0), .store (sc (h 13)) (win 1 0)] ++
    (List.range 6).flatMap (sqRow a) ++ [clear] ++ (List.range 7).flatMap (dblRow a) ++ reduce o

/-- The field multiplications with BMI2 and ADX. -/
def adx : Field where
  mul := mulX
  sqr := sqrX
  a24 o a := mulSmall o a a24

def x448Adx : Prog isa := x448With adx

end VG.Impl.X448.X86_64
