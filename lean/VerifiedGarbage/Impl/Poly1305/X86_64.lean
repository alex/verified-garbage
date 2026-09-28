import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Poly1305: x86-64 implementation

The state (`rdi`, 128 bytes, see `VG.Spec.Poly1305.Repr`):

* `[0, 24)`: the accumulator `h = h0 + 2⁶⁴ h1 + 2¹²⁸ h2`, fully reduced
  (`h < p`) between calls;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 104)`: the saved `rbx, rbp, r12–r15`;
* `[104, 120)`: the last block, padded, in `finalize`.

Each call clamps `r = r0 + 2⁶⁴ r1` into `r8, r9` and computes `s1 = r1 + r1 / 4
= 5 r1 / 4` into `r10` (as `r1` is a multiple of 4), and keeps `h` in `r11,
rbx, rbp`. A block is absorbed as in OpenSSL's `poly1305_blocks`, with the
product `(h + m) r` reduced partially (modulo `p = 2¹³⁰ - 5`, using `2¹³⁰ ≡ 5`),
to `h < 5 · 2¹²⁸`:

* `x = h0 r0 + h1 s1` in `r12, r13`, `y = h0 r1 + h1 r0 + h2 s1` in `r14,
  r15`, and `h2 r0` in `rax`;
* `h = x + 2⁶⁴ y + 2¹²⁸ h2 r0 ≡ (h + m) r`, whose top word `t` (bits 128 and
  up) is replaced by `t mod 4`, adding `5 ⌊t / 4⌋` to the bottom.

Before `h` is stored, it is reduced fully: `h - p` is selected, without a
branch, if `h + 5 ≥ 2¹³⁰`.

The only branches are on the block count and the length of the last block,
and every address is a pointer plus a constant or a count, so only the
pointers and lengths can affect timing.
-/

namespace VG.Impl.Poly1305.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## `init(state = rdi, key = rsi)` -/

def init : Prog isa := .block [
  .mov .rax (.mem (at_ .rsi 0)), .mov .rcx (.mem (at_ .rsi 8)), .mov .rdx (.mem (at_ .rsi 16)),
  .mov .r8 (.mem (at_ .rsi 24)),
  .store (at_ .rdi 24) .rax, .store (at_ .rdi 32) .rcx, .store (at_ .rdi 40) .rdx,
  .store (at_ .rdi 48) .r8,
  .mov32 .rax (.imm 0), .store (at_ .rdi 0) .rax, .store (at_ .rdi 8) .rax,
  .store (at_ .rdi 16) .rax]

/-! ## Common parts of `blocks` and `finalize` -/

/-- The callee-saved registers we use, and where they are saved in the state. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 56), (.rbp, 64), (.r12, 72), (.r13, 80), (.r14, 88), (.r15, 96)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rdi d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rdi d))

/-- The clamped `r0, r1` into `r8, r9`, `s1 = r1 + r1 / 4` into `r10`, and `h`
into `r11, rbx, rbp`. -/
def setup : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r8 (.mem (at_ .rdi 24)), .alu .and .r8 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r9 (.mem (at_ .rdi 32)), .alu .and .r9 (.reg .rax),
  .mov .r10 (.reg .r9), .shift .shr .r10 2, .alu .add .r10 (.reg .r9),
  .mov .r11 (.mem (at_ .rdi 0)), .mov .rbx (.mem (at_ .rdi 8)), .mov .rbp (.mem (at_ .rdi 16))]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `rsi`. -/
def addBlock (pad : BitVec 32) : List Instr :=
  [.alu .add .r11 (.mem (at_ .rsi 0)), .alu .adc .rbx (.mem (at_ .rsi 8)), .alu .adc .rbp (.imm pad)]

/-- `lo:hi = a · b`. -/
def mulTo (lo hi a b : Reg) : List Instr :=
  [.mov .rax (.reg a), .mul b, .mov lo (.reg .rax), .mov hi (.reg .rdx)]

/-- `lo:hi += a · b`. -/
def mulAdd (lo hi a b : Reg) : List Instr :=
  [.mov .rax (.reg a), .mul b, .alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx)]

/-- `x = h0 r0 + h1 s1`, `y = h0 r1 + h1 r0 + h2 s1`, `rax = h2 r0`. -/
def products : List Instr :=
  mulTo .r12 .r13 .r11 .r8 ++ mulAdd .r12 .r13 .rbx .r10 ++
  mulTo .r14 .r15 .r11 .r9 ++ mulAdd .r14 .r15 .rbx .r8 ++ mulAdd .r14 .r15 .rbp .r10 ++
  [.mov .rax (.reg .rbp), .mul .r8]

/-- `h = x + 2⁶⁴ y + 2¹²⁸ h2 r0`, with its top word `t` replaced by `t mod 4`
and `5 ⌊t / 4⌋` added to the bottom. -/
def carry : List Instr := [
  .alu .add .r14 (.reg .r13), .alu .adc .r15 (.reg .rax),
  .mov .r11 (.reg .r12), .mov .rbx (.reg .r14),
  .mov .rbp (.reg .r15), .alu .and .rbp (.imm 3),
  .mov .rax (.reg .r15), .alu .sub .rax (.reg .rbp), .shift .shr .r15 2,
  .alu .add .rax (.reg .r15),
  .alu .add .r11 (.reg .rax), .alu .adc .rbx (.imm 0), .alu .adc .rbp (.imm 0)]

/-- Absorbing the block at `rsi`, with `pad = 1` for a whole block (the `0x01`
byte appended to it is `2¹²⁸`) and `pad = 0` for a padded last block (whose
`0x01` byte is inside it). -/
def absorb (pad : BitVec 32) : List Instr := addBlock pad ++ products ++ carry

/-- `h` reduced fully: `h + 5 - 2¹³⁰` if that is not negative, else `h`
(selected with the mask `-(⌊(h + 5) / 2¹³⁰⌋)` in `r14`). -/
def reduce : List Instr := [
  .mov .rax (.reg .r11), .alu .add .rax (.imm 5),
  .mov .rdx (.reg .rbx), .alu .adc .rdx (.imm 0),
  .mov .r12 (.reg .rbp), .alu .adc .r12 (.imm 0),
  .mov .r13 (.reg .r12), .shift .shr .r13 2,
  .mov32 .r14 (.imm 0), .alu .sub .r14 (.reg .r13),
  .alu .and .r12 (.imm 3),
  .alu .xor .rax (.reg .r11), .alu .and .rax (.reg .r14), .alu .xor .r11 (.reg .rax),
  .alu .xor .rdx (.reg .rbx), .alu .and .rdx (.reg .r14), .alu .xor .rbx (.reg .rdx),
  .alu .xor .r12 (.reg .rbp), .alu .and .r12 (.reg .r14), .alu .xor .rbp (.reg .r12)]

/-! ## `blocks(state = rdi, blocks = rsi, n = rdx)` -/

def body : Prog isa :=
  .block (absorb 1 ++ [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)])

def blocks : Prog isa :=
  .seq (.block (save ++ [.mov .rcx (.reg .rdx)] ++ setup ++ [.alu .test .rcx (.reg .rcx)]))
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (reduce ++ [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] ++ restore)))

/-! ## `finalize(state = rdi, tail = rsi, len = rdx, out = rcx)`

A non-empty tail is copied to `[104, 120)`, padded with `0x01` and zeros, and
absorbed with `pad = 0`. Then `h` is reduced and `s` added modulo `2¹²⁸`. -/

/-- `[rdi + r12 + 104]`: byte `r12` of the padded block. -/
def padAt (i : Reg) : MemOp := { base := .rdi, index := some i, disp := 104 }

def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax { base := .rsi, index := some .r12 }, .store8 (padAt .r12) .rax,
    .alu .add .r12 (.imm 1), .alu .cmp .r12 (.reg .rdx)]) .ne

def lastBlock : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (at_ .rdi 104) .rax, .store (at_ .rdi 112) .rax,
    .mov32 .r12 (.imm 0)])
  (.seq copyLoop
    (.block ([.mov32 .rax (.imm 1), .store8 (padAt .rdx) .rax, .mov .rsi (.reg .rdi),
      .alu .add .rsi (.imm 104)] ++ absorb 0)))

def finalize : Prog isa :=
  .seq (.block (save ++ setup ++ [.alu .test .rdx (.reg .rdx)]))
  (.seq (.ite .e (.block []) lastBlock)
    (.block (reduce ++ [.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore)))

end VG.Impl.Poly1305.X86_64
