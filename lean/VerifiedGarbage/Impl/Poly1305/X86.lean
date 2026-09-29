import VerifiedGarbage.TCB.X86.Isa

/-!
# Poly1305: x86 (32-bit) implementation

Every argument is on the stack (cdecl): `[esp + 4]`, `[esp + 8]`, … on entry,
and no code here moves `esp`, so they stay there.

The arithmetic is in radix `2³²`, as in OpenSSL's 32-bit x86 code without
SSE2: the accumulator `h = h0 + 2³² h1 + 2⁶⁴ h2 + 2⁹⁶ h3 + 2¹²⁸ h4` is five
32-bit words, which are the words it is stored as, and the clamped `r = r0 +
2³² r1 + 2⁶⁴ r2 + 2⁹⁶ r3` four, with `rj < 2²⁸` and `r1, r2, r3` multiples
of 4. `mul` multiplies 32-bit words into 64 bits, so a product term `hi rj`
of weight `2^(32 (i + j))` with `i + j ≥ 4` and `j ≥ 1` is folded into weight
`2^(32 (i + j - 4))` as `hi sj`, where `sj = rj + rj / 4 = 5 rj / 4` (as
`2¹²⁸ rj = 2¹³⁰ (rj / 4) ≡ 5 (rj / 4)` modulo `p = 2¹³⁰ - 5`).

The state (`state`, 128 bytes, see `VG.Spec.Poly1305.Buffered`):

* `[0, 24)`: the accumulator: `h` in `[0, 20)`, fully reduced (`h < p`)
  between calls, and a word that is zero between calls and holds the saved
  `ebp` during one;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the buffer: the message's last bytes that do not fill a block,
  padded in place in `finalize`;
* `[72, 88)`: the clamped `r0, …, r3`, and `[88, 100)`: `s1, s2, s3`,
  computed on entry;
* `[100, 116)`: the low words of a product, and of `h + 5`;
* `[116, 128)`: the saved `ebx, esi, edi`.

`update` and `finalize` do not need their `scratch`.

`edi` holds `state`. A block (at `esi`, or the buffer) is added to `h` in
place; then each `dk = Σ hi · c(k, i)` (`c` being an `rj` or an `sj`) is
summed into `ebx` (low word) and `ebp`, starting from the carry out of
`d(k-1)`, one product `eax · ecx` at a time, and its low word stored.
`d4 = h4 r0` (plus the carry) fits a word; its bits from 2 up are folded,
times 5, into the bottom (`5 ⌊d4 / 4⌋`, which fits a word too). Between
blocks, `h4 ≤ 4`.

Before `h` is stored, it is reduced fully: `h + 5 - 2¹³⁰` (`h - p`) is
selected, with a mask and without a branch, if `h + 5 ≥ 2¹³⁰`.

The only branches are on the block count, `count mod 16` (the number of
bytes buffered) and the lengths, and every address is `esp`, a pointer or a
pointer plus a constant, a count or `count mod 16`, so only the pointers,
`count` and the lengths can affect timing.
-/

namespace VG.Impl.Poly1305.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-! ## Offsets in the state -/

/-- `hi`, `rj`, `sj` and the low words `tk` of a product. -/
def hOff (i : Nat) : Nat := 4 * i
def rOff (j : Nat) : Nat := 72 + 4 * j
def sOff (j : Nat) : Nat := 84 + 4 * j
def tOff (k : Nat) : Nat := 100 + 4 * k
/-- Where the callee-saved registers are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 116), (.esi, 120), (.edi, 124), (.ebp, 20)]

/-! ## `init(state, key)` -/

def init : Prog isa := .block (
  [.mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 8))] ++
  (List.range 8).flatMap (fun j => [.mov .edx (.mem (at_ .ecx (4 * j))), .store (at_ .eax (24 + 4 * j)) .edx]) ++
  [.mov .edx (.imm 0)] ++ (List.range 6).map fun j => .store (at_ .eax (4 * j)) .edx)

/-! ## Common parts -/

/-- `state` into `edi`, saving `ebx, esi, edi, ebp` in it (via `eax`). -/
def save : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) :: saved.map (fun (r, d) => .store (at_ .eax d) r) ++ [.mov .edi (.reg .eax)]

/-- Restore them (via `eax`, from `edi`), and zero the word that held `ebp`. -/
def restore : List Instr :=
  .mov .eax (.reg .edi) :: saved.map (fun (r, d) => .mov r (.mem (at_ .eax d))) ++
    [.mov .ecx (.imm 0), .store (at_ .eax 20) .ecx]

/-- `r0` clamped. -/
def clamp0 : List Instr :=
  [.mov .eax (.mem (at_ .edi 24)), .alu .and .eax (.imm 0x0fffffff), .store (at_ .edi (rOff 0)) .eax]

/-- `rj` clamped and `sj = rj + rj / 4`, for `j = 1, 2, 3`. -/
def clampS (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (24 + 4 * j))), .alu .and .eax (.imm 0x0ffffffc),
    .store (at_ .edi (rOff j)) .eax, .mov .ecx (.reg .eax), .shift .shr .ecx 2,
    .alu .add .eax (.reg .ecx), .store (at_ .edi (sOff j)) .eax]

/-- Everything each function but `init` does first. -/
def setup : List Instr := save ++ clamp0 ++ clampS 1 ++ clampS 2 ++ clampS 3

/-! ## Absorbing a block -/

/-- Word `i` of `h` plus word `i` of the block at `b + d`, with the carry in
unless `i = 0`. -/
def addWord (b : Reg) (d i : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .edi (hOff i))), .alu (if i = 0 then .add else .adc) .eax (.mem (at_ b (d + 4 * i))),
    .store (at_ .edi (hOff i)) .eax]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`. -/
def addBlock (b : Reg) (d : Nat) (pad : BitVec 32) : List Instr :=
  addWord b d 0 ++ addWord b d 1 ++ addWord b d 2 ++ addWord b d 3 ++
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

/-- Absorbing the block at `b + d`, with `pad = 1` for a whole block (the
`0x01` byte appended to it is `2¹²⁸`) and `pad = 0` for a padded last block
(whose `0x01` byte is inside it). -/
def absorbAt (b : Reg) (d : Nat) (pad : BitVec 32) : List Instr := addBlock b d pad ++ products ++ carry

/-- Absorbing the block at `esi`. -/
def absorb (pad : BitVec 32) : List Instr := absorbAt .esi 0 pad

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

/-! ## `blocks(state, blocks, n)`

`esi` walks the blocks; the loop ends where it reaches `blocks + 16 n`,
recomputed from the arguments after each block. -/

/-- `blocks + 16 n`, compared with `esi`. -/
def atEnd : List Instr :=
  [.mov .eax (.mem (at_ .esp 12)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .ecx (.mem (at_ .esp 8)),
    .alu .add .eax (.reg .ecx), .alu .cmp .eax (.reg .esi)]

def body : Prog isa :=
  .block (absorb 1 ++ [.alu .add .esi (.imm 16)] ++ atEnd)

def blocks : Prog isa :=
  .seq (.block (setup ++ [.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
    .alu .test .ecx (.reg .ecx)]))
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block (reduce ++ restore)))

/-! ## `update(state, count, data, len, scratch)`

With `esi` = the data not yet consumed (from `data = [esp + 16]`), whose
length is `data + len - esi` (`len = [esp + 20]`), recomputed when needed,
and `edx` = the number of bytes in the buffer (`count mod 16`, from `count`'s
low word `[esp + 8]`): a non-empty buffer is filled from the data (as far as
it goes) and, once full, absorbed; then the whole blocks of the data are
absorbed, and the rest is copied into the buffer. -/

/-- The length of the data not yet consumed, `data + len - esi`, into `eax`
(via `ecx`). -/
def left : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.mem (at_ .esp 20)), .alu .add .eax (.reg .ecx),
    .alu .sub .eax (.reg .esi)]

/-- Copies the `eax > 0` bytes at `esi` to `edx + 56`, advancing `esi` and
`edx`. -/
def copyIn : Prog isa :=
  .loop (.block [.movzx8 .ecx (at_ .esi 0), .store8 (at_ .edx 56) .cl, .alu .add .esi (.imm 1),
    .alu .add .edx (.imm 1), .alu .sub .eax (.imm 1)]) .ne

/-- The number of bytes to copy into the buffer, `min(16 - edx, len)`, into
`eax`, and `edx` made the address `state + edx`. -/
def count : Prog isa :=
  .seq (.block [.mov .eax (.imm 16), .alu .sub .eax (.reg .edx), .mov .ecx (.mem (at_ .esp 20)),
    .alu .cmp .ecx (.reg .eax)])
  (.seq (.ite .b (.block [.mov .eax (.reg .ecx)]) (.block []))
    (.block [.alu .add .edx (.reg .edi), .alu .test .eax (.reg .eax)]))

/-- Fills the buffer with `min(16 - edx, len)` bytes of the data, and absorbs
it if that fills it. -/
def fill : Prog isa :=
  .seq count
  (.seq (.ite .e (.block []) copyIn)
  (.seq (.block [.alu .sub .edx (.reg .edi), .alu .cmp .edx (.imm 16)])
    (.ite .e (.block (absorbAt .edi 56 1)) (.block []))))

/-- Absorbs the whole blocks of the data. -/
def whole : Prog isa :=
  .seq (.block (left ++ [.alu .cmp .eax (.imm 16)]))
    (.ite .b (.block [])
      (.loop (.block (absorb 1 ++ [.alu .add .esi (.imm 16)] ++ left ++ [.alu .cmp .eax (.imm 16)])) .ae))

/-- Copies the rest of the data into the (empty) buffer. -/
def rest : Prog isa :=
  .seq (.block (left ++ [.alu .test .eax (.reg .eax)]))
    (.ite .e (.block []) (.seq (.block [.mov .edx (.reg .edi)]) copyIn))

def update : Prog isa :=
  .seq (.block (setup ++ [.mov .esi (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 8)),
    .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)]))
  (.seq (.ite .e (.block []) fill)
  (.seq whole
  (.seq rest
    (.block (reduce ++ restore)))))

/-! ## `finalize(state, count, out, scratch)`

`edx` = `count mod 16`, the number of bytes in the buffer. A non-empty
buffer is padded in place with zeros and then the `0x01` byte, and absorbed
with `pad = 0`. Then `h` is reduced and `s` added modulo `2¹²⁸`, into
`out = [esp + 16]`. -/

/-- Zeros the buffer from byte `edx < 16` on, at `ecx + 56 = state + edx + 56`. -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (at_ .ecx 56) .al, .alu .add .ecx (.imm 1), .alu .add .edx (.imm 1),
    .alu .cmp .edx (.imm 16)]) .ne

def lastBlock : Prog isa :=
  .seq (.block [.mov .eax (.imm 0), .mov .ecx (.reg .edx), .alu .add .ecx (.reg .edi)])
  (.seq zeroLoop
    (.block ([.mov .eax (.imm 1), .mov .ecx (.mem (at_ .esp 8)), .alu .and .ecx (.imm 15),
      .alu .add .ecx (.reg .edi), .store8 (at_ .ecx 56) .al] ++ absorbAt .edi 56 0)))

/-- The tag, `h + s` modulo `2¹²⁸`, into `out`. -/
def addS : List Instr :=
  .mov .esi (.mem (at_ .esp 16)) ::
  (List.range 4).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))),
    .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))), .store (at_ .esi (4 * k)) .eax]

def finalize : Prog isa :=
  .seq (.block (setup ++ [.mov .edx (.mem (at_ .esp 8)), .alu .and .edx (.imm 15),
    .alu .test .edx (.reg .edx)]))
  (.seq (.ite .e (.block []) lastBlock)
    (.block (reduce ++ addS ++ restore)))

end VG.Impl.Poly1305.X86
