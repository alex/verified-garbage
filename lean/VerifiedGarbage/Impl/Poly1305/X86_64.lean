import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Poly1305: x86-64 implementation

The state (`rdi`, 128 bytes, see `VG.Spec.Poly1305.Buffered`):

* `[0, 24)`: the accumulator `h = h0 + 2⁶⁴ h1 + 2¹²⁸ h2`, fully reduced
  (`h < p`) between calls;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the buffer: the message's last bytes that do not fill a block,
  padded in place in `finalize`;
* `[72, 120)`: the saved `rbx, rbp, r12–r15`.

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

The only branches are on the block count, the number of bytes buffered
(`count mod 16`) and the lengths, and every address is a pointer plus a
constant or a count, so only the pointers, `count` and the lengths can affect
timing.
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

/-! ## Common parts -/

/-- The callee-saved registers we use, and where they are saved in the state. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 72), (.rbp, 80), (.r12, 88), (.r13, 96), (.r14, 104), (.r15, 112)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rdi d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rdi d))

/-- The clamped `r0, r1` into `r8, r9`, `s1 = r1 + r1 / 4` into `r10`, and `h`
into `r11, rbx, rbp`. -/
def setup : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r8 (.mem (at_ .rdi 24)), .alu .and .r8 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r9 (.mem (at_ .rdi 32)), .alu .and .r9 (.reg .rax),
  .mov .r10 (.reg .r9), .shift .shr .r10 2, .alu .add .r10 (.reg .r9),
  .mov .r11 (.mem (at_ .rdi 0)), .mov .rbx (.mem (at_ .rdi 8)), .mov .rbp (.mem (at_ .rdi 16))]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`. -/
def addBlockAt (b : Reg) (d : Nat) (pad : BitVec 32) : List Instr :=
  [.alu .add .r11 (.mem (at_ b d)), .alu .adc .rbx (.mem (at_ b (d + 8))), .alu .adc .rbp (.imm pad)]

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

/-- Absorbing the block at `b + d`, with `pad = 1` for a whole block (the
`0x01` byte appended to it is `2¹²⁸`) and `pad = 0` for a padded last block
(whose `0x01` byte is inside it). -/
def absorbAt (b : Reg) (d : Nat) (pad : BitVec 32) : List Instr :=
  addBlockAt b d pad ++ products ++ carry

/-- Absorbing the block at `rsi`. -/
def absorb (pad : BitVec 32) : List Instr := absorbAt .rsi 0 pad

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

/-- `[rdi + i + 56]`: byte `i` of the buffer. -/
def bufAt (i : Reg) : MemOp := { base := .rdi, index := some i, disp := 56 }

/-! ## `blocks(state = rdi, blocks = rsi, n = rdx)` -/

def body : Prog isa :=
  .block (absorb 1 ++ [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)])

def blocks : Prog isa :=
  .seq (.block (save ++ [.mov .rcx (.reg .rdx)] ++ setup ++ [.alu .test .rcx (.reg .rcx)]))
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (reduce ++ [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] ++ restore)))

/-! ## `update(state = rdi, count = rsi, data = rdx, len = rcx)`

With `rsi` = the data not yet consumed, `rcx` = its length, and `r12` = the
number of bytes in the buffer (`count mod 16`): a non-empty buffer is filled
from the data (as far as it goes) and, once full, absorbed; then the whole
blocks of the data are absorbed, and the rest is copied into the buffer. -/

/-- Copies the `rax > 0` bytes at `rsi` to the buffer from byte `r12` on,
advancing `rsi` and `r12`. -/
def copyIn : Prog isa :=
  .loop (.block [.movzx8 .r13 (at_ .rsi 0), .store8 (bufAt .r12) .r13, .alu .add .rsi (.imm 1),
    .alu .add .r12 (.imm 1), .alu .sub .rax (.imm 1)]) .ne

/-- The number of bytes to copy into the buffer, `min(16 - r12, rcx)`, into
`rax`, and subtracted from `rcx`. -/
def count : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 16), .alu .sub .rax (.reg .r12), .alu .cmp .rcx (.reg .rax)])
  (.seq (.ite .b (.block [.mov .rax (.reg .rcx)]) (.block []))
    (.block [.alu .sub .rcx (.reg .rax), .alu .test .rax (.reg .rax)]))

/-- Fills the buffer with `min(16 - r12, rcx)` bytes of the data, and absorbs
it if that fills it. -/
def fill : Prog isa :=
  .seq count
  (.seq (.ite .e (.block []) copyIn)
  (.seq (.block [.alu .cmp .r12 (.imm 16)])
    (.ite .e (.block (absorbAt .rdi 56 1)) (.block []))))

/-- Absorbs the whole blocks of the data. -/
def whole : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.imm 16)])
    (.ite .b (.block [])
      (.loop (.block (absorb 1 ++ [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 16),
        .alu .cmp .rcx (.imm 16)])) .ae))

/-- Copies the rest of the data into the (empty) buffer. -/
def rest : Prog isa :=
  .seq (.block [.alu .test .rcx (.reg .rcx)])
    (.ite .e (.block []) (.seq (.block [.mov32 .r12 (.imm 0), .mov .rax (.reg .rcx)]) copyIn))

def update : Prog isa :=
  .seq (.block (save ++ setup ++ [.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15),
    .mov .rsi (.reg .rdx), .alu .test .r12 (.reg .r12)]))
  (.seq (.ite .e (.block []) fill)
  (.seq whole
  (.seq rest
    (.block (reduce ++ [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] ++ restore)))))

/-! ## `finalize(state = rdi, count = rsi, out = rdx)`

`out` is moved to `rcx`, which is not written again, and `count mod 16`, the
number of bytes in the buffer, to `rdx`. A non-empty buffer is padded in
place with `0x01` and zeros and absorbed with `pad = 0`. Then `h` is reduced
and `s` added modulo `2¹²⁸`. -/

/-- Zeros the buffer from byte `r12 < 16` on. -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (bufAt .r12) .rax, .alu .add .r12 (.imm 1), .alu .cmp .r12 (.imm 16)]) .ne

def lastBlock : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov .r12 (.reg .rdx)])
  (.seq zeroLoop
    (.block ([.mov32 .rax (.imm 1), .store8 (bufAt .rdx) .rax] ++ absorbAt .rdi 56 0)))

def finalize : Prog isa :=
  .seq (.block ([.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] ++ save ++
    setup ++ [.alu .test .rdx (.reg .rdx)]))
  (.seq (.ite .e (.block []) lastBlock)
    (.block (reduce ++ [.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore)))

end VG.Impl.Poly1305.X86_64
