import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.X86.Isa

/-!
# SHA-1 compression function: x86 (32-bit) implementation

`vg_sha1_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

The same structure as the x86-64 implementation, with fewer registers:
* The working variables `a … e` live in `eax`, `ebx`, `ecx`, `edx`, `esi`;
  the fully unrolled rounds rename them: in round `t`, variable `k` is in
  `var t k`. `edi` is the one temporary, and `ebp` points to the scratch
  buffer.
* The message schedule is a 16-word window in `scratch[0..64)`; the block
  pointer and the count of blocks left are kept in `scratch[80..88)`, and the
  state pointer is read from its argument slot when needed.
* Each round adds `Wₜ`, `fₜ(b, c, d)` (as one or two terms), `ROTL⁵(a)` and
  `Kₜ` into `e`'s register, which becomes the new `a`: the same sum as the
  specification's, in another order. `Maj(b, c, d)` is the sum of the
  disjoint `b ∧ c` and `(b ⊕ c) ∧ d`, so it needs no second temporary.
* `ebx`, `esi`, `edi` and `ebp` are saved in `scratch[64..80)` and restored
  on exit.
* `esp` and the arguments (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sha1.X86

open VG.X86
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.eax, .ebx, .ecx, .edx, .esi]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .eax

/-- The temporary; it holds `Wₜ` after the schedule of round `t`. -/
def T : Reg := .edi

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : MemOp := at_ .ebp (4 * (i % 16))

/-- Where the block pointer and the count of blocks left are kept in the scratch buffer. -/
def bpOff : Nat := 80
def nOff : Nat := 84

/-- Leave `Wₜ` in `T` and in its slot. The operations are in the order of
the specification; `ROTL¹` is a rotation right by 31. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .mov T (.mem (at_ .ebp bpOff)),
    .mov T (.mem (at_ T (4 * t))),
    .bswap T,
    .store (slot t) T]
  else [
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    .mov T (.mem (slot (t + 13))),
    .alu .xor T (.mem (slot (t + 8))),
    .alu .xor T (.mem (slot (t + 2))),
    .alu .xor T (.mem (slot t)),
    .shift .ror T 31,
    .store (slot t) T]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `e := e + f(b, c, d)`, through `T`. -/
def fcode (f : Fn) (b c d e : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.mov T (.reg c), .alu .xor T (.reg d), .alu .and T (.reg b), .alu .xor T (.reg d), .alu .add e (.reg T)]
  | .parity => [.mov T (.reg b), .alu .xor T (.reg c), .alu .xor T (.reg d), .alu .add e (.reg T)]
  | .maj => -- `Maj(b, c, d)`, as `(b ∧ c) + ((b ⊕ c) ∧ d)`
    [.mov T (.reg b), .alu .and T (.reg c), .alu .add e (.reg T),
      .mov T (.reg b), .alu .xor T (.reg c), .alu .and T (.reg d), .alu .add e (.reg T)]

/-- The rest of round `t`: `e := e + ROTL⁵(a) + Kₜ`, and `b` becomes
`ROTL³⁰(b)`. `ROTLⁿ` is a rotation right by `32 - n`. -/
def sum (t : Nat) (a b e : Reg) : List Instr := [
  .mov T (.reg a),
  .shift .ror T 27,
  .alu .add e (.reg T),
  .alu .add e (.imm (K t)),
  .shift .ror b 2]

/-- Round `t`, with `Wₜ` in `T`: `e`'s register becomes `e + Wₜ + fₜ(b, c, d) +
ROTL⁵(a) + Kₜ`, the new `a`. -/
def round (t : Nat) : List Instr :=
  .alu .add (var t 4) (.reg T) :: (fcode (fn t) (var t 1) (var t 2) (var t 3) (var t 4) ++
    sum t (var t 0) (var t 1) (var t 4))

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 64), (.esi, 68), (.edi, 72), (.ebp, 76)]

/-- Save the callee-saved registers, point `ebp` at the scratch buffer, keep
the block pointer and count there, and set ZF if there are no blocks. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 16))] ++
  saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .ebp (.reg .eax),
   .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp bpOff) .ecx,
   .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp nOff) .ecx,
   .alu .test .ecx (.reg .ecx)]

/-- Restore the callee-saved registers (`ebp`, the base, last). -/
def epilogue : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .ebp d))

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr :=
  .mov T (.mem (at_ .esp 4)) :: (List.range 5).map fun k => .mov (var 0 k) (.mem (at_ T (4 * k)))

/-- Add the working variables into the hash value. -/
def update : List Instr :=
  .mov T (.mem (at_ .esp 4)) ::
  ((List.range 5).map (fun k => .alu .add (var 0 k) (.mem (at_ T (4 * k)))) ++
    (List.range 5).map (fun k => .store (at_ T (4 * k)) (var 0 k)))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr :=
  [.mov .eax (.mem (at_ .ebp bpOff)), .alu .add .eax (.imm 64), .store (at_ .ebp bpOff) .eax,
   .mov .eax (.mem (at_ .ebp nOff)), .alu .sub .eax (.imm 1), .store (at_ .ebp nOff) .eax]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Sha1.X86
