import VerifiedGarbage.TCB.Arm.Isa

/-!
# ChaCha20 block function: 32-bit ARM implementation

`vg_chacha20_block(state = r0, buf = r1)`.

`buf` (256 bytes) is laid out as:

* `[0, 64)`: the output, word `k` at `4k` (the rounds' result is stored
  there, and then the input state is added to it);
* `[64, 128)`: a copy of the input state, word `k` at `64 + 4k`;
* `[128, 144)`: home slots for words 8–11, word `k` at `128 + 4(k - 8)`;
* `[144, 180)`: the saved `r4`–`r11` and `lr`.

There are only 13 registers besides `buf`'s, so during the rounds words 0–7
and 12–15 live in fixed registers (`wreg`) and words 8–11 (the third row)
take turns in `lr`: before each quarter round the word it needs is swapped
in from its slot. The ten double rounds are fully unrolled.

Every address is `r1` (or, while copying the state, `r0`) plus a constant,
and there are no branches, so only the pointers can affect timing.
-/

namespace VG.Impl.ChaCha20.Arm

open VG.Arm

/-- Offsets in `buf`: output word `k`, input word `k`, home slot of word `k` (8–11). -/
def outOff (k : Nat) : Nat := 4 * k
def inOff (k : Nat) : Nat := 64 + 4 * k
def slotOff (k : Nat) : Nat := 128 + 4 * (k - 8)

/-- The register holding word `k` whenever it is in a register. -/
def wreg : Nat → Reg
  | 0 => .r0 | 1 => .r2 | 2 => .r3 | 3 => .r4
  | 4 => .r5 | 5 => .r6 | 6 => .r7 | 7 => .r8
  | 8 => .lr | 9 => .lr | 10 => .lr | 11 => .lr
  | 12 => .r9 | 13 => .r10 | 14 => .r11 | _ => .r12

/-- The quarter round (RFC 8439 §2.1) on `a, b, c, d`. A rotation left by `k`
is a rotation right by `32 - k`. -/
def qr (a b c d : Reg) : List Instr := [
  .dp .add a a (.reg b), .dp .eor d d (.reg a), .mov d (.shifted d .ror 16),
  .dp .add c c (.reg d), .dp .eor b b (.reg c), .mov b (.shifted b .ror 20),
  .dp .add a a (.reg b), .dp .eor d d (.reg a), .mov d (.shifted d .ror 24),
  .dp .add c c (.reg d), .dp .eor b b (.reg c), .mov b (.shifted b .ror 25)]

/-- `QUARTERROUND(x, y, z, w)` (RFC 8439 §2.2). -/
def quarter (x y z w : Nat) : Prog isa := .block (qr (wreg x) (wreg y) (wreg z) (wreg w))

/-- Store word `i` (in `lr`) to its slot and load word `j`. -/
def swap (i j : Nat) : Prog isa := .block [.str .lr .r1 (slotOff i), .ldr .lr .r1 (slotOff j)]

/-- `inner_block` (RFC 8439 §2.3.1): a column round and a diagonal round.
Starts and ends with word 8 in `lr`. -/
def doubleRound : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (swap 8 9) <| .seq (quarter 1 5 9 13) <| .seq (swap 9 10) <|
  .seq (quarter 2 6 10 14) <| .seq (swap 10 11) <| .seq (quarter 3 7 11 15) <|
  .seq (swap 11 10) <| .seq (quarter 0 5 10 15) <| .seq (swap 10 11) <|
  .seq (quarter 1 6 11 12) <| .seq (swap 11 8) <| .seq (quarter 2 7 8 13) <|
  .seq (swap 8 9) <| .seq (quarter 3 4 9 14) (swap 9 8)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- The callee-saved registers we use (`r4`–`r11` and `lr`), and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 144), (.r5, 148), (.r6, 152), (.r7, 156), (.r8, 160), (.r9, 164), (.r10, 168),
   (.r11, 172), (.lr, 176)]

def save : List Instr := saved.map fun (r, d) => .str r .r1 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

/-- Copy word `k` of the input state to `buf` (words 9–11 also to their slots). -/
def copyWord (k : Nat) : List Instr :=
  [.ldr .r2 .r0 (4 * k), .str .r2 .r1 (inOff k)] ++
  if 9 ≤ k ∧ k ≤ 11 then [.str .r2 .r1 (slotOff k)] else []

def copy : List Instr := (List.range 16).flatMap copyWord

/-- Load word `k` into its register (words 9–11 start in their slots instead). -/
def loadWord (k : Nat) : List Instr :=
  if 9 ≤ k ∧ k ≤ 11 then [] else [.ldr (wreg k) .r1 (inOff k)]

def load : List Instr := (List.range 16).flatMap loadWord

/-- Store word `k` of the rounds' result to the output (words 9–11 from their
slots, via `r0`, which is free once word 0 has been stored). -/
def storeWord (k : Nat) : List Instr :=
  if 9 ≤ k ∧ k ≤ 11 then [.ldr .r0 .r1 (slotOff k), .str .r0 .r1 (outOff k)]
  else [.str (wreg k) .r1 (outOff k)]

/-- Add word `k` of the input state into the output. -/
def addWord (k : Nat) : List Instr :=
  [.ldr .r0 .r1 (outOff k), .ldr .r2 .r1 (inOff k), .dp .add .r0 .r0 (.reg .r2),
   .str .r0 .r1 (outOff k)]

def finish : List Instr := (List.range 16).flatMap storeWord ++ (List.range 16).flatMap addWord

def block : Prog isa :=
  .seq (.block (save ++ copy ++ load)) (.seq (rounds 10) (.block (finish ++ restore)))

end VG.Impl.ChaCha20.Arm
