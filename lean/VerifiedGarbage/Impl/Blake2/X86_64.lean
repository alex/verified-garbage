import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# BLAKE2 compression function: x86-64 implementation

`vg_blake2{b,s}_compress(state = rdi, blocks = rsi, n = rdx, t = rcx, last = r8, scratch = r9)`,
for words of `w` bits (64 for BLAKE2b, 32 for BLAKE2s, in the low half of the
registers, with the 32-bit forms of the instructions) and the parameters `P`
(`Spec.Blake2.b` or `Spec.Blake2.s`).

`rdi` (`state`) and `r9` (`scratch`) are never written, so every store is
through one of them at a constant offset. `scratch` is laid out as:

* `[0, 128)`: a copy of the current block (word `j` at `(w/8)·j`), so that the
  rounds address everything through `r9`;
* `[128, 256)`: word `k` of the work vector `v` at `128 + 8k` (its low `w`
  bits): the home slots of words 8–11 during the rounds, and of words 9 and
  12–15 after them;
* `[256, 296)`: the current block's address, the blocks left, the offset
  counter (low word; and for BLAKE2b the high word), and the final block flag
  as all-zero or all-one bits;
* `[296, 344)`: the saved `rbx, rbp, r12–r15`.

During the rounds, words 0–7 and 12–15 live in fixed registers (`wreg`), and
words 8–11 (the third row) share `r14`: one of them is in `r14` and the other
three in their home slots. Before each `G` whose third-row word is not the one
in `r14`, the word in `r14` is stored to its slot and the next one loaded.
Between rounds `r14` holds word 9 (each round's last `G` uses it), so each round
starts by swapping it for word 8. The rounds are fully unrolled; each `G` adds
its message words straight from the copy of the block.

Every address is `r9`, `rdi` or the block's address plus a constant, and
the only branches are on `last` and on the count of blocks, so only the
pointers, `n`, `t` and `last` can affect timing.
-/

namespace VG.Impl.Blake2.X86_64

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

section
variable (w : Nat)

/-- The size of a word in bytes. -/
def ws : Nat := w / 8

/-! ## Instructions at the word size -/

def add (d : Reg) (s : Src) : Instr := if w = 64 then .alu .add d s else .alu32 .add d s
def xor (d : Reg) (s : Src) : Instr := if w = 64 then .alu .xor d s else .alu32 .xor d s
def ror (d : Reg) (n : Nat) : Instr := if w = 64 then .shift .ror d n else .shift32 .ror d n
def ld (d : Reg) (m : MemOp) : Instr := if w = 64 then .mov d (.mem m) else .mov32 d (.mem m)
def st (m : MemOp) (r : Reg) : Instr := if w = 64 then .store m r else .store32 m r
/-- Load a word-sized constant. -/
def imm (d : Reg) (v : BitVec w) : Instr :=
  if w = 64 then .movImm64 d (v.setWidth 64) else .mov32 d (.imm (v.setWidth 32))

end

/-! ## The layout of `scratch` -/

/-- Word `j` of the copy of the block. -/
def msgOff (w j : Nat) : Nat := ws w * j
/-- Word `k` of the work vector. -/
def vOff (k : Nat) : Nat := 128 + 8 * k
def blOff : Nat := 256
def nOff : Nat := 264
def tloOff : Nat := 272
def thiOff : Nat := 280
def fOff : Nat := 288

/-- The register holding word `k` whenever it is in a register. -/
def wreg : Nat → Reg
  | 0 => .rax | 1 => .rbx | 2 => .rcx | 3 => .rdx
  | 4 => .rsi | 5 => .r15 | 6 => .rbp | 7 => .r8
  | 8 => .r14 | 9 => .r14 | 10 => .r14 | 11 => .r14
  | 12 => .r10 | 13 => .r11 | 14 => .r12 | _ => .r13

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-! ## The rounds -/

/-- `G` (RFC 7693 §3.1) on the words in `a, b, c, d`, with the message words
`j` and `k` of the copy of the block. -/
def g (a b c d : Reg) (j k : Nat) : List Instr := [
  add w a (.reg b), add w a (.mem (at_ .r9 (msgOff w j))), xor w d (.reg a), ror w d P.R1,
  add w c (.reg d), xor w b (.reg c), ror w b P.R2,
  add w a (.reg b), add w a (.mem (at_ .r9 (msgOff w k))), xor w d (.reg a), ror w d P.R3,
  add w c (.reg d), xor w b (.reg c), ror w b P.R4]

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of the
round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g P (wreg x) (wreg y) (wreg z) (wreg u) (Spec.Blake2.sigmaAt r (2 * i))
    (Spec.Blake2.sigmaAt r (2 * i + 1)))

/-- Store third-row word `i` (in `r14`) to its slot and load word `j`. -/
def swap (i j : Nat) : Prog isa := .block [st w (at_ .r9 (vOff i)) .r14, ld w .r14 (at_ .r9 (vOff j))]

/-- Round `r` (RFC 7693 §3.2). Starts and ends with word 9 in `r14`. -/
def round (r : Nat) : Prog isa :=
  .seq (swap (w := w) 9 8) <| .seq (gAt P r 0 0 4 8 12) <|
  .seq (swap (w := w) 8 9) <| .seq (gAt P r 1 1 5 9 13) <|
  .seq (swap (w := w) 9 10) <| .seq (gAt P r 2 2 6 10 14) <|
  .seq (swap (w := w) 10 11) <| .seq (gAt P r 3 3 7 11 15) <|
  .seq (swap (w := w) 11 10) <| .seq (gAt P r 4 0 5 10 15) <|
  .seq (swap (w := w) 10 11) <| .seq (gAt P r 5 1 6 11 12) <|
  .seq (swap (w := w) 11 8) <| .seq (gAt P r 6 2 7 8 13) <|
  .seq (swap (w := w) 8 9) (gAt P r 7 3 4 9 14)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round P n)

/-! ## One block -/

/-- Copy the block at `blocks` (loaded into `rsi`) to `scratch[0..bb)`. -/
def copy : List Instr :=
  ld 64 .rsi (at_ .r9 blOff) :: (List.range 16).flatMap fun j =>
    [ld w .rax (at_ .rsi (ws w * j)), st w (at_ .r9 (msgOff w j)) .rax]

/-- Initialize the work vector (RFC 7693 §3.2): words 8, 10 and 11 in their
slots, the others in their registers (word 9 in `r14`). -/
def init : List Instr :=
  [imm w .rax P.IV[0], st w (at_ .r9 (vOff 8)) .rax, imm w .rax P.IV[2],
    st w (at_ .r9 (vOff 10)) .rax, imm w .rax P.IV[3], st w (at_ .r9 (vOff 11)) .rax] ++
  (List.range 8).map (fun k => ld w (wreg k) (at_ .rdi (ws w * k))) ++
  [imm w .r14 P.IV[1],
    imm w .r10 P.IV[4], xor w .r10 (.mem (at_ .r9 tloOff)),
    imm w .r11 P.IV[5], xor w .r11 (.mem (at_ .r9 (if w = 64 then thiOff else tloOff + 4))),
    imm w .r12 P.IV[6], xor w .r12 (.mem (at_ .r9 fOff)),
    imm w .r13 P.IV[7]]

/-- The words of the second half in registers at the end of the rounds. -/
def spillWords : List Nat := [9, 12, 13, 14, 15]

/-- Store the words of the second half that are in registers to their slots. -/
def spill : List Instr := spillWords.map fun k => st w (at_ .r9 (vOff k)) (wreg k)

/-- XOR the two halves of the work vector into the state:
`h[i] := h[i] ^ v[i] ^ v[i + 8]`, with `v[i]` in its register. -/
def finish : List Instr :=
  (List.range 8).flatMap fun i =>
    [xor w (wreg i) (.mem (at_ .r9 (vOff (i + 8)))), xor w (wreg i) (.mem (at_ .rdi (ws w * i))),
      st w (at_ .rdi (ws w * i)) (wreg i)]

/-- Advance to the next block and its offset counter, and decrement the count
of blocks (setting ZF when it hits 0), in their slots. BLAKE2b's counter is
128 bits: the carry goes to its high word. -/
def advance : List Instr :=
  [.mov .rsi (.mem (at_ .r9 blOff)), .alu .add .rsi (.imm (BitVec.ofNat 32 (16 * ws w))),
    .store (at_ .r9 blOff) .rsi,
    .mov .rcx (.mem (at_ .r9 tloOff)), .alu .add .rcx (.imm (BitVec.ofNat 32 (16 * ws w))),
    .store (at_ .r9 tloOff) .rcx] ++
  (if w = 64 then [.mov .r8 (.mem (at_ .r9 thiOff)), .alu .adc .r8 (.imm 0),
    .store (at_ .r9 thiOff) .r8] else []) ++
  [.mov .rdx (.mem (at_ .r9 nOff)), .alu .sub .rdx (.imm 1), .store (at_ .r9 nOff) .rdx]

def body : Prog isa :=
  .seq (.block (copy (w := w) ++ init P)) (.seq (rounds P P.r) (.block (spill (w := w) ++ finish (w := w) ++ advance (w := w))))

/-! ## The whole function -/

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 296), (.rbp, 304), (.r12, 312), (.r13, 320), (.r14, 328), (.r15, 336)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r9 d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r9 d))

/-- Keep the arguments in `scratch` (the high word of BLAKE2b's counter
starts at 0), and test `last` (a 32-bit argument, whose upper half is
unspecified). -/
def setup : List Instr :=
  [.mov32 .r8 (.reg .r8), .store (at_ .r9 blOff) .rsi,
    .store (at_ .r9 nOff) .rdx, .store (at_ .r9 tloOff) .rcx, .mov32 .rax (.imm 0),
    .store (at_ .r9 thiOff) .rax, .alu .test .r8 (.reg .r8)]

/-- The final block flag: all one bits if `last ≠ 0`. -/
def flag : Prog isa :=
  .seq (.ite .e (.block []) (.block [.mov .rax (.imm 0xffffffff)]))
    (.block [.store (at_ .r9 fOff) .rax, .alu .test .rdx (.reg .rdx)])

def compress : Prog isa :=
  .seq (.block (save ++ setup)) (.seq flag
    (.seq (.ite .e (.block []) (.loop (body P) .ne)) (.block restore)))

end

end VG.Impl.Blake2.X86_64
