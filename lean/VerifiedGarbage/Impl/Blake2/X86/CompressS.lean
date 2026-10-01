import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.TCB.X86.Isa

/-!
# BLAKE2s compression function: x86 (32-bit) implementation

`vg_blake2s_compress(state, blocks, n, t, last, scratch)`, cdecl: the
arguments are at `[esp + 4]` (`state`), `[esp + 8]` (`blocks`), `[esp + 12]`
(`n`), `[esp + 16]` and `[esp + 20]` (the low and high words of `t`),
`[esp + 24]` (`last`) and `[esp + 28]` (`scratch`).

With seven usable registers, the sixteen words of the work vector `v` live
in `scratch`, word `k` at `[esi + 4k]`, and each `G` loads its four words
into `eax`, `ebx`, `ecx` and `edx`, computes, and stores them back: every
`G` is the same code, at other offsets. Its message words are added straight
from the block, at `[edi + 4j]`. The rounds are fully unrolled.

`scratch` is laid out as:

* `[0, 64)`: the work vector;
* `[64, 72)`: the offset counter of the current block (low word, then high);
* `[72, 76)`: the final block flag, as all-zero or all-one bits;
* `[76, 80)`: the number of blocks left;
* `[80, 92)`: the saved `ebx`, `esi` and `edi` (`ebp` is not used).

`esi` points to `scratch` and `edi` to the current block; the hash value's
address is read from its argument slot when needed. Every address is `esp`,
`esi`, `edi` or the state's address plus a constant, and the only branches
are on `last` and on the count of blocks, so only the pointers, `n`, `t` and
`last` can affect timing.
-/

namespace VG.Impl.Blake2.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

namespace CompressS

/-! ## The layout of `scratch` -/

/-- Word `k` of the work vector. -/
def vOff (k : Nat) : Nat := 4 * k
def tloOff : Nat := 64
def thiOff : Nat := 68
def fOff : Nat := 72
def nOff : Nat := 76

/-! ## The rounds -/

/-- `G` (RFC 7693 §3.1) on words `a, b, c, d` of the work vector, with words
`j` and `k` of the block: BLAKE2s's rotations are by 16, 12, 8 and 7. -/
def g (a b c d j k : Nat) : List Instr := [
  .mov .eax (.mem (at_ .esi (vOff a))), .mov .ebx (.mem (at_ .esi (vOff b))),
  .mov .ecx (.mem (at_ .esi (vOff c))), .mov .edx (.mem (at_ .esi (vOff d))),
  .alu .add .eax (.reg .ebx), .alu .add .eax (.mem (at_ .edi (4 * j))), .alu .xor .edx (.reg .eax),
  .shift .ror .edx 16, .alu .add .ecx (.reg .edx), .alu .xor .ebx (.reg .ecx), .shift .ror .ebx 12,
  .alu .add .eax (.reg .ebx), .alu .add .eax (.mem (at_ .edi (4 * k))), .alu .xor .edx (.reg .eax),
  .shift .ror .edx 8, .alu .add .ecx (.reg .edx), .alu .xor .ebx (.reg .ecx), .shift .ror .ebx 7,
  .store (at_ .esi (vOff a)) .eax, .store (at_ .esi (vOff b)) .ebx,
  .store (at_ .esi (vOff c)) .ecx, .store (at_ .esi (vOff d)) .edx]

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of
the round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g x y z u (Spec.Blake2.sigmaAt r (2 * i)) (Spec.Blake2.sigmaAt r (2 * i + 1)))

/-- Round `r` (RFC 7693 §3.2). -/
def round (r : Nat) : Prog isa :=
  .seq (gAt r 0 0 4 8 12) <| .seq (gAt r 1 1 5 9 13) <| .seq (gAt r 2 2 6 10 14) <|
  .seq (gAt r 3 3 7 11 15) <| .seq (gAt r 4 0 5 10 15) <| .seq (gAt r 5 1 6 11 12) <|
  .seq (gAt r 6 2 7 8 13) (gAt r 7 3 4 9 14)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round n)

/-! ## One block -/

/-- Initialize the work vector (RFC 7693 §3.2): the hash value (at `eax`,
loaded from its argument slot), then the IV, with the offset counter and the
final block flag XORed into words 12 to 14. -/
def load : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) ::
  (List.range 8).flatMap (fun k => [.mov .ecx (.mem (at_ .eax (4 * k))), .store (at_ .esi (vOff k)) .ecx]) ++
  [.mov .ecx (.imm Spec.Blake2.s.IV[0]), .store (at_ .esi (vOff 8)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[1]), .store (at_ .esi (vOff 9)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[2]), .store (at_ .esi (vOff 10)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[3]), .store (at_ .esi (vOff 11)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[4]), .alu .xor .ecx (.mem (at_ .esi tloOff)),
   .store (at_ .esi (vOff 12)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[5]), .alu .xor .ecx (.mem (at_ .esi thiOff)),
   .store (at_ .esi (vOff 13)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[6]), .alu .xor .ecx (.mem (at_ .esi fOff)),
   .store (at_ .esi (vOff 14)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[7]), .store (at_ .esi (vOff 15)) .ecx]

/-- XOR the two halves of the work vector into the hash value (at `eax`):
`h[i] := v[i] ^ v[i + 8] ^ h[i]`. -/
def finish : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) :: (List.range 8).flatMap fun i =>
    [.mov .ecx (.mem (at_ .esi (vOff i))), .alu .xor .ecx (.mem (at_ .esi (vOff (i + 8)))),
     .alu .xor .ecx (.mem (at_ .eax (4 * i))), .store (at_ .eax (4 * i)) .ecx]

/-- Advance to the next block and its offset counter (a 64-bit integer: the
carry goes to the high word), and decrement the count of blocks (setting ZF
when it hits 0). -/
def advance : List Instr :=
  [.alu .add .edi (.imm 64),
   .mov .eax (.mem (at_ .esi tloOff)), .alu .add .eax (.imm 64), .store (at_ .esi tloOff) .eax,
   .mov .eax (.mem (at_ .esi thiOff)), .alu .adc .eax (.imm 0), .store (at_ .esi thiOff) .eax,
   .mov .eax (.mem (at_ .esi nOff)), .alu .sub .eax (.imm 1), .store (at_ .esi nOff) .eax]

def body : Prog isa := .seq (.block load) (.seq (rounds 10) (.block (finish ++ advance)))

/-! ## The whole function -/

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 80), (.esi, 84), (.edi, 88)]

/-- Save the callee-saved registers (with `scratch` in `eax`), keep the
offset counter in `scratch`, and test `last`. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 28))] ++ saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)),
   .mov .eax (.mem (at_ .esp 16)), .store (at_ .esi tloOff) .eax,
   .mov .eax (.mem (at_ .esp 20)), .store (at_ .esi thiOff) .eax,
   .mov .ecx (.imm 0), .mov .eax (.mem (at_ .esp 24)), .alu .test .eax (.reg .eax)]

/-- The final block flag (all one bits if `last ≠ 0`), and the count of
blocks, setting ZF if it is 0. -/
def flag : Prog isa :=
  .seq (.ite .e (.block []) (.block [.mov .ecx (.imm 0xffffffff)]))
    (.block [.store (at_ .esi fOff) .ecx, .mov .eax (.mem (at_ .esp 12)), .store (at_ .esi nOff) .eax,
      .alu .test .eax (.reg .eax)])

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (.mem (at_ .esi 80)), .mov .edi (.mem (at_ .esi 88)), .mov .esi (.mem (at_ .esi 84))]

def compress : Prog isa :=
  .seq (.block prologue) (.seq flag (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue)))

end CompressS

end VG.Impl.Blake2.X86
