import VerifiedGarbage.TCB.X86_64.Isa

/-!
# The Salsa20/8 Core: x86-64 implementation

`vg_salsa20_8(b = rdi, scratch = rsi)`: replaces the 64 bytes at `b` by their
Salsa20/8 Core (RFC 7914 §3).

The input stays in `b` until the final addition. `scratch` (64 bytes) holds:

* `[0, 16)`: the home slots of words 12–15, word `k` at `4(k - 12)`;
* `[16, 64)`: the saved `rbx, rbp, r12–r15`.

Words 0–11 live in fixed registers (`wreg`) throughout, and `eax` is the
temporary of every line `x[i] ^= R(x[j] + x[k], n)` (a rotation left by `n`
is a rotation right by `32 - n`). A word in a slot is read as a memory
operand; a line whose destination is in a slot xors the slot into `eax` and
stores it back. The four double rounds are fully unrolled.

Every address is `rdi` or `rsi` plus a constant, and there are no branches,
so only the pointers can affect timing.
-/

namespace VG.Impl.Scrypt.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The offset in `scratch` of the home slot of word `k` (12–15). -/
def slotOff (k : Nat) : Nat := 4 * (k - 12)

/-- The register holding word `k` (0–11). -/
def wreg : Nat → Reg
  | 0 => .rcx | 1 => .rdx | 2 => .r8 | 3 => .r9
  | 4 => .r10 | 5 => .r11 | 6 => .rbx | 7 => .rbp
  | 8 => .r12 | 9 => .r13 | 10 => .r14 | _ => .r15

/-- Word `k` as a source operand: its register, or its slot. -/
def src (k : Nat) : Src := if k < 12 then .reg (wreg k) else .mem (at_ .rsi (slotOff k))

/-- `x[i] ^= R(x[j] + x[k], n)`. -/
def line (i j k n : Nat) : List Instr :=
  [.mov32 .rax (src j), .alu32 .add .rax (src k), .shift32 .ror .rax (32 - n)] ++
  if i < 12 then [.alu32 .xor (wreg i) (.reg .rax)]
  else [.alu32 .xor .rax (.mem (at_ .rsi (slotOff i))), .store32 (at_ .rsi (slotOff i)) .rax]

/-- The lines `(i, j, k, n)` of a double round (a column round and a row
round), in the order of RFC 7914 §3. -/
def lines : List (Nat × Nat × Nat × Nat) := [
  (4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18),
  (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18),
  (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18),
  (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18),
  (1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18),
  (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18),
  (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18),
  (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

def doubleRound : Prog isa := .block (lines.flatMap fun (i, j, k, n) => line i j k n)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- The callee-saved registers we use, and where in `scratch` they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 16), (.rbp, 24), (.r12, 32), (.r13, 40), (.r14, 48), (.r15, 56)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rsi d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rsi d))

/-- Load word `k` of `b` into its register, or copy it to its slot. -/
def loadWord (k : Nat) : List Instr :=
  if k < 12 then [.mov32 (wreg k) (.mem (at_ .rdi (4 * k)))]
  else [.mov32 .rax (.mem (at_ .rdi (4 * k))), .store32 (at_ .rsi (slotOff k)) .rax]

def load : List Instr := (List.range 16).flatMap loadWord

/-- Add word `k` of the input (still in `b`) to word `k` of the rounds'
result, and store the sum to `b`. -/
def finishWord (k : Nat) : List Instr :=
  if k < 12 then
    [.alu32 .add (wreg k) (.mem (at_ .rdi (4 * k))), .store32 (at_ .rdi (4 * k)) (wreg k)]
  else
    [.mov32 .rax (.mem (at_ .rsi (slotOff k))), .alu32 .add .rax (.mem (at_ .rdi (4 * k))),
     .store32 (at_ .rdi (4 * k)) .rax]

def finish : List Instr := (List.range 16).flatMap finishWord

def salsa : Prog isa :=
  .seq (.block (save ++ load)) (.seq (rounds 4) (.block (finish ++ restore)))

end VG.Impl.Scrypt.X86_64
