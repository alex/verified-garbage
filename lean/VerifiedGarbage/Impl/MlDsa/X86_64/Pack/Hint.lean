import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream

/-!
# ML-DSA on x86-64: `vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`

Both follow Algorithms 20 and 21 (the spec's `hintBitPack` and
`hintBitUnpack`) step by step. They may leak the hint, and branch and index
memory on it; each first zeroes its output, whose contents are then a
function of the hint alone.

* `hintBitPack(h = rdi, hlen = rsi, omega = edx, y = rcx, len = r8)`: zeroes
  the `len` bytes of `y`; then, with the index in `rax`, for each of the `k`
  polynomials (`r10` counting down; `r9` pointing at `y[ω + i]`) and each of
  their 256 coefficients (`r11` = `j`, `rdi` walking the words), stores `j` to
  `y[index]` and increments the index if the coefficient is not 0, and then
  stores the index to `y[ω + i]`.
* `hintBitUnpack(y = rdi, len = rsi, omega = edx, h = rcx, hlen = r8)`:
  zeroes the `hlen` words of `h`; then, with the index in `rax`, for each of
  the `k` polynomials (`r10` counting down; `r9` pointing at `y[ω + i]`, and
  `rcx` at polynomial `i` of `h`), checks the bound `y[ω + i]` (in `r11`)
  against the index and `ω`, and sets the coefficients `y[index]` of the
  polynomial up to it (in `rsi`), each but the first after checking that it
  is greater than the previous one (in `r8`); then checks that the bytes
  from the index up to `ω` are zero. A failed check sets the index to 256
  (more than `ω`, and than any byte), which ends the loop it is in and skips
  the rest; the return value is 1 if the index is at most `ω`, 0 otherwise.
-/

namespace VG.Impl.MlDsa.X86_64.Pack

open VG.X86_64

/-- `[b + i + d]`. -/
def atIdx (b i : Reg) (scale : Nat := 1) (d : Int := 0) : MemOp := { base := b, index := some i, scale, disp := d }

/-! ## `vg_mldsa_hint_bit_pack` -/

/-- Zero the `len` bytes of `y`; `rax` is then 0. -/
def hbpZero : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov32 .rax (.imm 0), .mov .r9 (.reg .rcx), .mov .r10 (.reg .r8)])
    (.loop (.block [.store8 (at_ .r9 0) .rax, .alu .add .r9 (.imm 1), .alu .sub .r10 (.imm 1)]) .ne)

/-- Coefficient `j = r11` of the polynomial, the word at `rdi`: if it is not
0, `y[index] ← j` and the index is incremented. -/
def hbpCoef : Prog isa :=
  .seq (.block [.mov32 .rsi (.mem (at_ .rdi 0)), .alu32 .cmp .rsi (.imm 0)])
    (.seq (.ite .ne (.block [.store8 (atIdx .rcx .rax) .r11, .alu .add .rax (.imm 1)]) (.block []))
      (.block [.alu .add .rdi (.imm 4), .alu .add .r11 (.imm 1), .alu32 .cmp .r11 (.imm 256)]))

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hbpPoly : Prog isa :=
  .seq (.block [.mov32 .r11 (.imm 0)])
    (.seq (.loop hbpCoef .ne) (.block [.store8 (at_ .r9 0) .rax, .alu .add .r9 (.imm 1), .alu .sub .r10 (.imm 1)]))

/-- The `k = len - ω` polynomials, from `r9 = y + ω`. -/
def hbpMain : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rcx), .alu .add .r9 (.reg .rdx), .mov .r10 (.reg .r8), .alu .sub .r10 (.reg .rdx)])
    (.loop hbpPoly .ne)

def hintBitPack : Prog isa := .seq hbpZero hbpMain

/-! ## `vg_mldsa_hint_bit_unpack` -/

/-- Zero the `hlen` words of `h`; `rax` is then 0. -/
def hbuZero : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov32 .rax (.imm 0), .mov .r9 (.reg .rcx), .mov .r10 (.reg .r8)])
    (.loop (.block [.store32 (at_ .r9 0) .rax, .alu .add .r9 (.imm 4), .alu .sub .r10 (.imm 1)]) .ne)

/-- A failed check: the index becomes 256. -/
def hbuFail : Prog isa := .block [.mov32 .rax (.imm 256)]

/-- Set coefficient `y[index]` (in `rsi`) of the polynomial at `rcx`, and
increment the index. -/
def hbuSet : List Instr :=
  [.mov32 .r8 (.imm 1), .store32 (atIdx .rcx .rsi 4) .r8, .alu .add .rax (.imm 1)]

/-- A coefficient after the first: `y[index - 1] < y[index]`, or fail. -/
def hbuNext : Prog isa :=
  .seq (.block [.movzx8 .r8 (atIdx .rdi .rax 1 (-1)), .movzx8 .rsi (atIdx .rdi .rax), .alu .cmp .r8 (.reg .rsi)])
    (.seq (.ite .b (.block hbuSet) hbuFail) (.block [.alu .cmp .rax (.reg .r11)]))

/-- The coefficients of the polynomial, while the index is less than the
bound `r11`: the first, then the others. -/
def hbuCoefs : Prog isa :=
  .seq (.block [.alu .cmp .rax (.reg .r11)])
    (.ite .b
      (.seq (.block ([.movzx8 .rsi (atIdx .rdi .rax)] ++ hbuSet ++ [.alu .cmp .rax (.reg .r11)]))
        (.ite .b (.loop hbuNext .b) (.block [])))
      (.block []))

/-- Polynomial `i`, unless a check failed: the bound `y[ω + i]`, checked, and
the coefficients up to it. -/
def hbuPoly : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.reg .rax)])
    (.ite .ae
      (.seq (.block [.movzx8 .r11 (at_ .r9 0), .alu .cmp .r11 (.reg .rax)])
        (.ite .b hbuFail (.seq (.block [.alu .cmp .rdx (.reg .r11)]) (.ite .b hbuFail hbuCoefs))))
      (.block []))

/-- The `k = len - ω` polynomials, from `r9 = y + ω`. -/
def hbuMain : Prog isa :=
  .seq (.block [.mov .r9 (.reg .rdi), .alu .add .r9 (.reg .rdx), .mov .r10 (.reg .rsi), .alu .sub .r10 (.reg .rdx)])
    (.loop (.seq hbuPoly (.block [.alu .add .r9 (.imm 1), .alu .add .rcx (.imm 1024), .alu .sub .r10 (.imm 1)])) .ne)

/-- The bytes from the index up to `ω` are zero, or fail. -/
def hbuTrail : Prog isa :=
  .seq (.block [.alu .cmp .rax (.reg .rdx)])
    (.ite .b
      (.loop (.seq (.block [.movzx8 .r8 (atIdx .rdi .rax), .alu32 .cmp .r8 (.imm 0)])
        (.seq (.ite .ne hbuFail (.block [.alu .add .rax (.imm 1)])) (.block [.alu .cmp .rax (.reg .rdx)]))) .b)
      (.block []))

/-- `eax ← 1` if the index is at most `ω`, 0 otherwise. -/
def hbuRet : List Instr := [.alu .cmp .rdx (.reg .rax), .mov32 .rax (.imm 1), .alu32 .sbb .rax (.imm 0)]

def hintBitUnpack : Prog isa := .seq hbuZero (.seq hbuMain (.seq hbuTrail (.block hbuRet)))

end VG.Impl.MlDsa.X86_64.Pack
