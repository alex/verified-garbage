import VerifiedGarbage.TCB.X86_64.Isa

/-!
# ChaCha20 block function: x86-64 implementation

`vg_chacha20_block(state = rdi, buf = rsi)`.

`buf` (256 bytes) is laid out as:

* `[0, 64)`: the output, word `k` at `4k` (the rounds' result is stored
  there, and then the input state is added to it);
* `[64, 128)`: a copy of the input state, word `k` at `64 + 4k`;
* `[128, 144)`: home slots for words 8–11, word `k` at `128 + 4(k - 8)`;
* `[144, 192)`: the saved `rbx, rbp, r12–r15`.

During the rounds, words 0–7 and 12–15 live in fixed registers (`wreg`).
Words 8–11 (the third row) share `r14` and `r15`: two of them are in the
registers and the other two in their home slots, and the pair is swapped
halfway through each column round and each diagonal round, as in OpenSSL's
scalar ChaCha20. The ten double rounds are fully unrolled.

Every address is `rsi` (or, while copying the state, `rdi`) plus a constant,
and there are no branches, so only the pointers can affect timing.
-/

namespace VG.Impl.ChaCha20.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Offsets in `buf`: output word `k`, input word `k`, home slot of word `k` (8–11). -/
def outOff (k : Nat) : Nat := 4 * k
def inOff (k : Nat) : Nat := 64 + 4 * k
def slotOff (k : Nat) : Nat := 128 + 4 * (k - 8)

/-- The register holding word `k` whenever it is in a register. -/
def wreg : Nat → Reg
  | 0 => .rax | 1 => .rbx | 2 => .rcx | 3 => .rdx
  | 4 => .rdi | 5 => .rbp | 6 => .r8 | 7 => .r9
  | 8 => .r14 | 9 => .r15 | 10 => .r14 | 11 => .r15
  | 12 => .r10 | 13 => .r11 | 14 => .r12 | _ => .r13

/-- The quarter round (RFC 8439 §2.1) on the low 32 bits of `a, b, c, d`.
A rotation left by `k` is a rotation right by `32 - k`. -/
def qr (a b c d : Reg) : List Instr := [
  .alu32 .add a (.reg b), .alu32 .xor d (.reg a), .shift32 .ror d 16,
  .alu32 .add c (.reg d), .alu32 .xor b (.reg c), .shift32 .ror b 20,
  .alu32 .add a (.reg b), .alu32 .xor d (.reg a), .shift32 .ror d 24,
  .alu32 .add c (.reg d), .alu32 .xor b (.reg c), .shift32 .ror b 25]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2). -/
def quarter (x y z w : Nat) : Prog isa := .block (qr (wreg x) (wreg y) (wreg z) (wreg w))

/-- Store words `i, i + 1` (in `r14, r15`) to their slots and load words `j, j + 1`. -/
def swap (i j : Nat) : Prog isa := .block [
  .store32 (at_ .rsi (slotOff i)) .r14, .store32 (at_ .rsi (slotOff (i + 1))) .r15,
  .mov32 .r14 (.mem (at_ .rsi (slotOff j))), .mov32 .r15 (.mem (at_ .rsi (slotOff (j + 1))))]

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round.
Starts and ends with words 8 and 9 in registers. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (quarter 1 5 9 13) <| .seq (swap 8 10) <|
  .seq (quarter 2 6 10 14) <| .seq (quarter 3 7 11 15) <|
  .seq (quarter 0 5 10 15) <| .seq (quarter 1 6 11 12) <| .seq (swap 10 8) <|
  .seq (quarter 2 7 8 13) (quarter 3 4 9 14)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 144), (.rbp, 152), (.r12, 160), (.r13, 168), (.r14, 176), (.r15, 184)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rsi d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rsi d))

/-- Copy word `k` of the input state to `buf` (words 10 and 11 also to their slots). -/
def copyWord (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi (4 * k))), .store32 (at_ .rsi (inOff k)) .rax] ++
  if k = 10 ∨ k = 11 then [.store32 (at_ .rsi (slotOff k)) .rax] else []

def copy : List Instr := (List.range 16).flatMap copyWord

/-- The words that live in `wreg` from the start (words 10 and 11 start in their slots). -/
def regWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15]

def load : List Instr := regWords.map fun k => .mov32 (wreg k) (.mem (at_ .rsi (inOff k)))

/-- Store word `k` of the rounds' result to the output (words 10 and 11 from
their slots, via `rax`, which is free once word 0 has been stored). -/
def storeWord (k : Nat) : List Instr :=
  if k = 10 ∨ k = 11 then
    [.mov32 .rax (.mem (at_ .rsi (slotOff k))), .store32 (at_ .rsi (outOff k)) .rax]
  else [.store32 (at_ .rsi (outOff k)) (wreg k)]

/-- Add word `k` of the input state into the output. -/
def addWord (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi (outOff k))), .alu32 .add .rax (.mem (at_ .rsi (inOff k))),
   .store32 (at_ .rsi (outOff k)) .rax]

def finish : List Instr := (List.range 16).flatMap storeWord ++ (List.range 16).flatMap addWord

def block : Prog isa :=
  .seq (.block (save ++ copy ++ load)) (.seq (rounds 10) (.block (finish ++ restore)))

end VG.Impl.ChaCha20.X86_64
