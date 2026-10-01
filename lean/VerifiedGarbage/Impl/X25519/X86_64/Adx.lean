import VerifiedGarbage.Impl.X25519.X86_64

/-!
# X25519: x86-64 implementation with BMI2 and ADX

`vg_x25519_adx`: the code of `vg_x25519` (`Impl/X25519/X86_64.lean`) with
other field multiplications (`adx`), using `mulx` (BMI2), which multiplies
by `rdx` without touching the flags, and `adcx` and `adox` (ADX), which add
with a carry in CF and in OF alone: each row of a product runs two carry
chains at once, the low halves of the products through OF and the high
halves through CF.

* `mulX`: the 512-bit product, row by row into `r8–r15` (row 0 with one
  chain), then `lo + 38 hi` with both chains, and its carry word folded as
  in `mul`;
* `sqrX`: the products `a_i a_j` (`i < j`) into `r9–r14`, then doubled
  through CF while the squares `a_i²` are added through OF, and reduced as
  in `mulX`.

Both use the registers `rax`, `rcx`, `rdx`, `rbp` (zero, for the chains'
last carries) and `r8–r15`, and address memory only as `vg_x25519` does.
-/

namespace VG.Impl.X25519.X86_64

open VG.X86_64

/-- `xor ebp, ebp`: `rbp = 0`, CF and OF clear. -/
def clear : Instr := .alu32 .xor .rbp (.reg .rbp)

/-- `mulx y, rax, src`, `adcx x, rax`: `rdx · src` added at `x` through CF,
its high half into `y`. -/
def mulAcc (x y : Reg) (src : Src) : List Instr := [.mulx y .rax src, .adcx x (.reg .rax)]

/-- `mulx rcx, rax, src`, `adox x, rax`, `adcx y, rcx`: `rdx · src` added at
`x` and `y` (the next word), the low half through OF and the high half
through CF. -/
def madd (x y : Reg) (src : Src) : List Instr :=
  [.mulx .rcx .rax src, .adox x (.reg .rax), .adcx y (.reg .rcx)]

/-- `mulx y, rax, src`, `adox x, rax`, then both carries into `y`: `rdx · src`
added at `x`, its high half and the carries into `y`. -/
def maddLast (x y : Reg) (src : Src) : List Instr :=
  [.mulx y .rax src, .adox x (.reg .rax), .adcx y (.reg .rbp), .adox y (.reg .rbp)]

/-- `adcx x, x`, `adox x, s`: `x` doubled through CF, and `s` added through OF. -/
def dblAdd (x s : Reg) : List Instr := [.adcx x (.reg x), .adox x (.reg s)]

/-- Row 0 of a product: `r8–r12 = a · b₀`, through CF. -/
def rowX0 (a b : Nat) : List Instr :=
  [.mov .rdx (.mem (sc b)), clear, .mulx .r9 .r8 (.mem (sc a))] ++
    mulAcc .r9 .r10 (.mem (sc (a + 8))) ++ mulAcc .r10 .r11 (.mem (sc (a + 16))) ++
    mulAcc .r11 .r12 (.mem (sc (a + 24))) ++ [.adcx .r12 (.reg .rbp)]

/-- Row `i ≥ 1` of a product: `t[i..i+4] += a · b_i` (`t[i+4]` fresh), the
low halves through OF and the high halves through CF. -/
def rowX (a b i : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (b + 8 * i))), clear] ++
    madd (t i) (t (i + 1)) (.mem (sc a)) ++ madd (t (i + 1)) (t (i + 2)) (.mem (sc (a + 8))) ++
    madd (t (i + 2)) (t (i + 3)) (.mem (sc (a + 16))) ++
    maddLast (t (i + 3)) (t (i + 4)) (.mem (sc (a + 24)))

/-- `r8–r11 + 2²⁵⁶ r12 = r8–r11 + 38 · r12–r15` (with `rdx = 38`), then
`r8–r11 += 38 r12`, folded. -/
def reduceX : List Instr :=
  [.mov32 .rdx (.imm 38), clear] ++ madd .r8 .r9 (.reg .r12) ++ madd .r9 .r10 (.reg .r13) ++
    madd .r10 .r11 (.reg .r14) ++ maddLast .r11 .r12 (.reg .r15) ++
    [.mulx .rcx .rax (.reg .r12)] ++ carry38

/-- `[o] = [a] · [b]`. -/
def mulX (o a b : Nat) : List Instr :=
  rowX0 a b ++ rowX a b 1 ++ rowX a b 2 ++ rowX a b 3 ++ reduceX ++ store4 o

/-- The products `a₀ a_j` (`j > 0`) into `r9–r12`, through CF. -/
def sqrA (a : Nat) : List Instr :=
  [.mov .rdx (.mem (sc a)), clear, .mulx .r10 .r9 (.mem (sc (a + 8)))] ++
    mulAcc .r10 .r11 (.mem (sc (a + 16))) ++ mulAcc .r11 .r12 (.mem (sc (a + 24))) ++
    [.adcx .r12 (.reg .rbp)]

/-- The products `a₁ a₂` and `a₁ a₃` added into `r11–r13`. -/
def sqrB (a : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 8))), clear] ++ madd .r11 .r12 (.mem (sc (a + 16))) ++
    maddLast .r12 .r13 (.mem (sc (a + 24)))

/-- The product `a₂ a₃` added into `r13–r14`. -/
def sqrC (a : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 16))), clear] ++ mulAcc .r13 .r14 (.mem (sc (a + 24))) ++
    [.adcx .r14 (.reg .rbp)]

/-- The square of the word at `d` into `hi:lo`. -/
def sqWord (d : Nat) (hi lo : Reg) : List Instr := [.mov .rdx (.mem (sc d)), .mulx hi lo (.reg .rdx)]

/-- `r9–r14` doubled through CF while the squares `a_i²` are added through
OF: `r8–r15 = 2 · r9–r14 + Σ a_i²`. -/
def sqrD (a : Nat) : List Instr :=
  [clear] ++ sqWord a .rax .r8 ++ dblAdd .r9 .rax ++
    sqWord (a + 8) .rcx .rax ++ dblAdd .r10 .rax ++ dblAdd .r11 .rcx ++
    sqWord (a + 16) .rcx .rax ++ dblAdd .r12 .rax ++ dblAdd .r13 .rcx ++
    sqWord (a + 24) .r15 .rax ++ dblAdd .r14 .rax ++ [.adcx .r15 (.reg .rbp), .adox .r15 (.reg .rbp)]

/-- `[o] = [a]²`: the products `a_i a_j` (`i < j`) into `r9–r14`, then
doubled while the squares are added, and reduced. -/
def sqrX (o a : Nat) : List Instr := sqrA a ++ sqrB a ++ sqrC a ++ sqrD a ++ reduceX ++ store4 o

/-- `[o] = a24 · [a]`: `r8–r12 = a24 · [a]` through CF, then `r12` folded as
38. -/
def a24X (o a : Nat) : List Instr :=
  [.mov32 .rdx (.imm a24), clear, .mulx .r9 .r8 (.mem (sc a))] ++
    mulAcc .r9 .r10 (.mem (sc (a + 8))) ++ mulAcc .r10 .r11 (.mem (sc (a + 16))) ++
    mulAcc .r11 .r12 (.mem (sc (a + 24))) ++
    [.adcx .r12 (.reg .rbp), .mov32 .rdx (.imm 38), .mulx .rcx .rax (.reg .r12)] ++ carry38 ++
    store4 o

/-- The field multiplications with BMI2 and ADX. -/
def adx : Field where
  mul := mulX
  sqr := sqrX
  a24 := a24X

def x25519Adx : Prog isa := x25519With adx

end VG.Impl.X25519.X86_64
