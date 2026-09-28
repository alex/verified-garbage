import VerifiedGarbage.TCB.X86.Isa

/-!
# Poly1305: x86 (32-bit) implementation

Every argument is on the stack (cdecl): `[esp + 4]`, `[esp + 8]`, … on entry.

The arithmetic is in radix `2³²`, as in OpenSSL's 32-bit x86 code without
SSE2: the accumulator `h = h0 + 2³² h1 + 2⁶⁴ h2 + 2⁹⁶ h3 + 2¹²⁸ h4` is five
32-bit words, which are the words it is stored as, and the clamped `r = r0 +
2³² r1 + 2⁶⁴ r2 + 2⁹⁶ r3` four, with `rj < 2²⁸` and `r1, r2, r3` multiples
of 4. `mul` multiplies 32-bit words into 64 bits, so a product term `hi rj`
of weight `2^(32 (i + j))` with `i + j ≥ 4` and `j ≥ 1` is folded into weight
`2^(32 (i + j - 4))` as `hi sj`, where `sj = rj + rj / 4 = 5 rj / 4` (as
`2¹²⁸ rj = 2¹³⁰ (rj / 4) ≡ 5 (rj / 4)` modulo `p = 2¹³⁰ - 5`).

The state (`state`, 128 bytes, see `VG.Spec.Poly1305.Repr`):

* `[0, 24)`: the accumulator: `h` in `[0, 20)`, fully reduced (`h < p`)
  between calls, and a zero word;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the clamped `r0, …, r3`, and `[72, 84)`: `s1, s2, s3`,
  computed on entry;
* `[84, 100)`: the low words of a product, and of `h + 5`;
* `[100, 116)`: the saved `ebx, esi, edi, ebp`;
* `[116, 120)`: the number of blocks left, in `blocks`.

`edi` holds `state`. A block (at `esi`) is added to `h` in place; then each
`dk = Σ hi · c(k, i)` (`c` being an `rj` or an `sj`) is summed into `ebx`
(low word) and `ebp`, starting from the carry out of `d(k-1)`, one product
`eax · ecx` at a time, and its low word stored. `d4 = h4 r0` (plus the carry)
fits a word; its bits from 2 up are folded, times 5, into the bottom
(`5 ⌊d4 / 4⌋`, which fits a word too). Between blocks, `h4 ≤ 4`.

Before `h` is stored, it is reduced fully: `h + 5 - 2¹³⁰` (`h - p`) is
selected, with a mask and without a branch, if `h + 5 ≥ 2¹³⁰`.

The only branches are on the block count and the length of the last block,
and every address is `esp`, a pointer or a pointer plus a constant or a
count, so only the pointers and lengths can affect timing.
-/

namespace VG.Impl.Poly1305.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## Offsets in the state -/

/-- `hi`, `rj`, `sj` and the low words `tk` of a product. -/
def hOff (i : Nat) : Nat := 4 * i
def rOff (j : Nat) : Nat := 56 + 4 * j
def sOff (j : Nat) : Nat := 68 + 4 * j
def tOff (k : Nat) : Nat := 84 + 4 * k
/-- Where the callee-saved registers are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 100), (.esi, 104), (.edi, 108), (.ebp, 112)]
/-- The number of blocks left. -/
def cntOff : Nat := 116

/-! ## `init(state, key)` -/

def init : Prog isa := .block (
  [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8))] ++
  (List.range 8).flatMap (fun j => [.mov .edx (.mem (at_ .ecx (4 * j))), .store (at_ .eax (24 + 4 * j)) .edx]) ++
  [.mov .edx (.imm 0)] ++ (List.range 6).map fun j => .store (at_ .eax (4 * j)) .edx)

/-! ## Common parts of `blocks` and `finalize` -/

/-- `state` into `edi`, saving `ebx, esi, edi, ebp` in it (via `eax`). -/
def save : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) :: saved.map (fun (r, d) => .store (at_ .eax d) r) ++ [.mov .edi (.reg .eax)]

/-- Restore them (via `eax`, from `edi`). -/
def restore : List Instr := .mov .eax (.reg .edi) :: saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- `r0` clamped. -/
def clamp0 : List Instr :=
  [.mov .eax (.mem (at_ .edi 24)), .alu .and .eax (.imm 0x0fffffff), .store (at_ .edi (rOff 0)) .eax]

/-- `rj` clamped and `sj = rj + rj / 4`, for `j = 1, 2, 3`. -/
def clampS (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (24 + 4 * j))), .alu .and .eax (.imm 0x0ffffffc),
    .store (at_ .edi (rOff j)) .eax, .mov .ecx (.reg .eax), .shift .shr .ecx 2,
    .alu .add .eax (.reg .ecx), .store (at_ .edi (sOff j)) .eax]

/-- Everything `blocks` and `finalize` do first. -/
def setup : List Instr := save ++ clamp0 ++ clampS 1 ++ clampS 2 ++ clampS 3

/-! ## Absorbing a block -/

/-- Word `i` of `h` plus word `i` of the block at `esi`, with the carry in
unless `i = 0`. -/
def addWord (i : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff i))), .alu (if i = 0 then .add else .adc) .eax (.mem (at_ .esi (4 * i))),
    .store (at_ .edi (hOff i)) .eax]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `esi`. -/
def addBlock (pad : BitVec 32) : List Instr :=
  addWord 0 ++ addWord 1 ++ addWord 2 ++ addWord 3 ++
  [.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm pad), .store (at_ .edi (hOff 4)) .eax]

/-- `ebx:ebp += hi · c`, the coefficient `c` at `[edi + off]`. -/
def mac (i off : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff i))), .mov .ecx (.mem (at_ .edi off)), .mul .ecx,
    .alu .add .ebx (.reg .eax), .alu .adc .ebp (.reg .edx)]

/-- The offset of the coefficient of `hi` in `dk` (`k < 4`): `r(k-i)`, or
`s(k+4-i)`. -/
def coef (k i : Nat) : Nat := if i ≤ k then rOff (k - i) else sOff (k + 4 - i)

/-- The number of terms of `dk`: `h4 r0` is not folded into `d0`. -/
def nterms (k : Nat) : Nat := if k = 0 then 4 else 5

/-- `dk` (`k < 4`) added to `ebx:ebp`, its low word stored, and its high word
moved to `ebx` as the carry into `d(k+1)`. -/
def dsum (k : Nat) : List Instr :=
  (List.range (nterms k)).flatMap (fun i => mac i (coef k i)) ++
  [.store (at_ .edi (tOff k)) .ebx, .mov .ebx (.reg .ebp), .mov .ebp (.imm 0)]

/-- `d0, …, d3`, then `d4 = h4 r0` plus the carry, in `ebx`. -/
def products : List Instr :=
  [.mov .ebx (.imm 0), .mov .ebp (.imm 0)] ++ (List.range 4).flatMap dsum ++ mac 4 (rOff 0)

/-- `h = t0 + 2³² t1 + 2⁶⁴ t2 + 2⁹⁶ t3 + 2¹²⁸ (d4 mod 4) + 5 ⌊d4 / 4⌋`. -/
def carry : List Instr :=
  [.mov .eax (.reg .ebx), .shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx), .alu .and .ebx (.imm 3),
    .alu .add .eax (.mem (at_ .edi (tOff 0))), .store (at_ .edi (hOff 0)) .eax] ++
  (List.range 3).flatMap (fun k => [.mov .eax (.mem (at_ .edi (tOff (k + 1)))), .alu .adc .eax (.imm 0),
    .store (at_ .edi (hOff (k + 1))) .eax]) ++
  [.alu .adc .ebx (.imm 0), .store (at_ .edi (hOff 4)) .ebx]

/-- Absorbing the block at `esi`, with `pad = 1` for a whole block (the
`0x01` byte appended to it is `2¹²⁸`) and `pad = 0` for a padded last block
(whose `0x01` byte is inside it). -/
def absorb (pad : BitVec 32) : List Instr := addBlock pad ++ products ++ carry

/-! ## The final reduction -/

/-- `g = h + 5`: its low words stored at `tOff`, its top word in `edx`, and
the mask `-⌊g / 2¹³⁰⌋` in `ebp`. -/
def plus5 : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff 0))), .alu .add .eax (.imm 5), .store (at_ .edi (tOff 0)) .eax] ++
  (List.range 3).flatMap (fun k => [.mov .eax (.mem (at_ .edi (hOff (k + 1)))), .alu .adc .eax (.imm 0),
    .store (at_ .edi (tOff (k + 1))) .eax]) ++
  [.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm 0), .mov .edx (.reg .eax),
    .shift .shr .eax 2, .mov .ebp (.imm 0), .alu .sub .ebp (.reg .eax)]

/-- Word `k < 4` of `h` replaced by that of `g` where the mask is set. -/
def selectWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff k))), .mov .ecx (.mem (at_ .edi (tOff k))), .alu .xor .ecx (.reg .eax),
    .alu .and .ecx (.reg .ebp), .alu .xor .eax (.reg .ecx), .store (at_ .edi (hOff k)) .eax]

/-- The top word: that of `g` minus 4 (`g - 2¹³⁰`), or that of `h`. -/
def selectTop : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff 4))), .alu .xor .edx (.reg .eax), .alu .and .edx (.reg .ebp),
    .alu .xor .eax (.reg .edx), .alu .and .eax (.imm 3), .store (at_ .edi (hOff 4)) .eax]

/-- `h` reduced fully, in place. -/
def reduce : List Instr :=
  plus5 ++ (List.range 4).flatMap selectWord ++ selectTop

/-! ## `blocks(state, blocks, n)` -/

def body : Prog isa :=
  .block (absorb 1 ++ [.alu .add .esi (.imm 16), .mov .ecx (.mem (at_ .edi cntOff)),
    .alu .sub .ecx (.imm 1), .store (at_ .edi cntOff) .ecx])

def blocks : Prog isa :=
  .seq (.block (setup ++ [.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
    .store (at_ .edi cntOff) .ecx, .alu .test .ecx (.reg .ecx)]))
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (reduce ++ [.mov .eax (.imm 0), .store (at_ .edi 20) .eax] ++ restore)))

/-! ## `finalize(state, tail, len, out)`

A non-empty tail is copied to `out` (by `ebx`, counting down `ecx`), padded
with `0x01` and zeros, and absorbed from there with `pad = 0`. Then `h` is
reduced and `s` added modulo `2¹²⁸`, into `out`. -/

def zeroOut : List Instr :=
  [.mov .ebx (.mem (at_ .esp 16)), .mov .eax (.imm 0), .store (at_ .ebx 0) .eax,
    .store (at_ .ebx 4) .eax, .store (at_ .ebx 8) .eax, .store (at_ .ebx 12) .eax,
    .mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12))]

def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ebx 0) .al, .alu .add .esi (.imm 1),
    .alu .add .ebx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne

def lastBlock : Prog isa :=
  .seq (.block zeroOut)
  (.seq copyLoop
    (.block ([.mov .eax (.imm 1), .store8 (at_ .ebx 0) .al, .mov .esi (.mem (at_ .esp 16))] ++
      absorb 0)))

/-- The tag, `h + s` modulo `2¹²⁸`, into `out`. -/
def addS : List Instr :=
  .mov .esi (.mem (at_ .esp 16)) ::
  (List.range 4).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))),
    .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))), .store (at_ .esi (4 * k)) .eax]

def finalize : Prog isa :=
  .seq (.block (setup ++ [.mov .ecx (.mem (at_ .esp 12)), .alu .test .ecx (.reg .ecx)]))
  (.seq (.ite .e (.block []) lastBlock)
    (.block (reduce ++ addS ++ restore)))

end VG.Impl.Poly1305.X86
