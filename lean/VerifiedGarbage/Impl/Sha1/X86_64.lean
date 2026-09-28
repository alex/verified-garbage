import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SHA-1 compression function: x86-64 implementation

`vg_sha1_compress(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`.

* The working variables `a … e` live in the low 32 bits of five registers.
  Rather than moving them at the end of every round, the fully unrolled
  rounds rename them: in round `t`, variable `k` is in `var t k`.
* The message schedule is kept as a 16-word window `W[t mod 16]` in
  `scratch[0..64)`.
* `rbx, rbp, r12–r15` are saved in `scratch[64..112)` and restored on exit.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sha1.X86_64

open VG.X86_64
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.rax, .rbx, .rbp, .r8, .r9]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .rax

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .r13
def T1 : Reg := .r14
def T2 : Reg := .r15

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : MemOp := at_ .rcx (4 * (i % 16))

/-- Leave `Wₜ` in `T0` and in its slot. The operations are in the order of
the specification; `ROTL¹` is a rotation right by 31. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .mov32 T0 (.mem (at_ .rsi (4 * t))),
    .bswap32 T0,
    .store32 (slot t) T0]
  else [
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    .mov32 T0 (.mem (slot (t + 13))),
    .alu32 .xor T0 (.mem (slot (t + 8))),
    .alu32 .xor T0 (.mem (slot (t + 2))),
    .alu32 .xor T0 (.mem (slot t)),
    .shift32 .ror T0 31,
    .store32 (slot t) T0]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `T1 := f(b, c, d)` (using `T2` as well for `Maj`). -/
def fcode (f : Fn) (b c d : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.mov32 T1 (.reg c), .alu32 .xor T1 (.reg d), .alu32 .and T1 (.reg b), .alu32 .xor T1 (.reg d)]
  | .parity => [.mov32 T1 (.reg b), .alu32 .xor T1 (.reg c), .alu32 .xor T1 (.reg d)]
  | .maj => -- `Maj(b, c, d)`, as `((b ∨ c) ∧ d) ∨ (b ∧ c)`
    [.mov32 T1 (.reg b), .alu32 .or T1 (.reg c), .alu32 .and T1 (.reg d),
      .mov32 T2 (.reg b), .alu32 .and T2 (.reg c), .alu32 .or T1 (.reg T2)]

/-- The rest of round `t`, with `f(b, c, d)` in `T1` and `Wₜ` in `T0`:
`T = ROTL⁵(a) + f + e + Kₜ + Wₜ`, with the additions in the order of the
specification, goes into `e`'s register (the new `a`), and `b` becomes
`ROTL³⁰(b)`. `ROTLⁿ` is a rotation right by `32 - n`. -/
def sum (t : Nat) (a b e : Reg) : List Instr := [
  .mov32 T2 (.reg a),
  .shift32 .ror T2 27,
  .alu32 .add T2 (.reg T1),
  .alu32 .add T2 (.reg e),
  .alu32 .add T2 (.imm (K t)),
  .alu32 .add T2 (.reg T0),
  .mov32 e (.reg T2),
  .shift32 .ror b 2]

/-- Round `t`, with `Wₜ` in `T0`. -/
def round (t : Nat) : List Instr :=
  fcode (fn t) (var t 1) (var t 2) (var t 3) ++ sum t (var t 0) (var t 1) (var t 4)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.rbx, 64), (.rbp, 72), (.r12, 80), (.r13, 88), (.r14, 96), (.r15, 104)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 5).map fun k => .mov32 (var 0 k) (.mem (at_ .rdi (4 * k)))

/-- Add the working variables into the hash value. -/
def update : List Instr :=
  (List.range 5).map (fun k => .alu32 .add (var 0 k) (.mem (at_ .rdi (4 * k)))) ++
  (List.range 5).map (fun k => .store32 (at_ .rdi (4 * k)) (var 0 k))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha1.X86_64
