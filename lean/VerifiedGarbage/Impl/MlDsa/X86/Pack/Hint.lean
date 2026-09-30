import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`

Both follow Algorithms 20 and 21 (the spec's `hintBitPack` and
`hintBitUnpack`) step by step, as on x86-64. They may leak the hint, and
branch and index memory on it; each first zeroes its output, whose contents
are then a function of the hint alone. Both save the caller's `ebx`, `esi`,
`edi` and `ebp` (`leaf`), so their arguments are at `[esp + 20]`, `[esp + 24]`, …

* `hintBitPack(h, hlen, omega, y, len)`: zeroes the `len` bytes of `y`; then,
  with the index in `eax`, `edi = y`, for each of the `k = len - ω`
  polynomials (`ebp` counting down; `ecx` pointing at `y[ω + i]`) and each of
  their 256 coefficients (`ebx` = `j`, `esi` walking the words of `h`),
  stores `j` to `y[index]` (at `edx = y + index`) and increments the index
  if the coefficient is not 0, and then stores the index to `y[ω + i]`.
* `hintBitUnpack(y, len, omega, h, hlen)`: zeroes the `hlen` words of `h`;
  then, with the index in `eax`, `edi = y`, `esi = 1`, for each of the `k`
  polynomials (counting down in the argument slot of `len`; the address of
  `y[ω + i]` in the slot of `hlen`; `ecx` at polynomial `i` of `h`), checks
  the bound `y[ω + i]` (in `ebx`) against the index and `ω`, and sets the
  coefficients `y[index]` of the polynomial up to it (in `ebp`), each but the
  first after checking that it is greater than the previous one
  `y[index - 1]` (in `edx`); then checks that the bytes from the index up to
  `ω` are zero. A failed check sets the index to 256 (more than `ω`, and than
  any byte), which ends the loop it is in and fails the check of every
  following bound; the return value is 1 if the index is at most `ω`, 0
  otherwise.
-/

namespace VG.Impl.MlDsa.X86.Pack

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-! ## `vg_mldsa_hint_bit_pack` -/

/-- `edi = y`, `ecx = len`, `eax = 0`. -/
def hbpZeroInit : List Instr := [.mov .edi (.mem (at_ .esp 32)), .mov .ecx (.mem (at_ .esp 36)), .mov .eax (.imm 0)]

/-- Zero the byte at `edi`, and on to the next. -/
def hbpZeroBody : List Instr := [.store8 (at_ .edi 0) .al, .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]

/-- `esi = h`, `edi = y`, `ecx = y + ω`, `ebp = len - ω`. -/
def hbpSetup : List Instr :=
  [.mov .esi (.mem (at_ .esp 20)), .mov .edi (.mem (at_ .esp 32)), .mov .ecx (.reg .edi),
    .alu .add .ecx (.mem (at_ .esp 28)), .mov .ebp (.mem (at_ .esp 36)), .alu .sub .ebp (.mem (at_ .esp 28))]

/-- Load the coefficient at `esi` and compare it with 0. -/
def hbpLoad : List Instr := [.mov .edx (.mem (at_ .esi 0)), .alu .cmp .edx (.imm 0)]

/-- `y[index] ← j`, and the index is incremented. -/
def hbpSet : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.reg .eax), .store8 (at_ .edx 0) .bl, .alu .add .eax (.imm 1)]

/-- On to the next coefficient. -/
def hbpNext : List Instr := [.alu .add .esi (.imm 4), .alu .add .ebx (.imm 1), .alu .cmp .ebx (.imm 256)]

/-- Coefficient `j = ebx` of the polynomial, the word at `esi`: if it is not
0, `y[index] ← j` and the index is incremented. -/
def hbpCoef : Prog isa :=
  .seq (.block hbpLoad) (.seq (.ite .ne (.block hbpSet) (.block [])) (.block hbpNext))

/-- `y[ω + i] ← index`, and on to the next polynomial. -/
def hbpEnd : List Instr := [.store8 (at_ .ecx 0) .al, .alu .add .ecx (.imm 1), .alu .sub .ebp (.imm 1)]

/-- Polynomial `i`: its coefficients, then `y[ω + i] ← index`. -/
def hbpPoly : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0)]) (.seq (.loop hbpCoef .ne) (.block hbpEnd))

def hintBitPack : Prog isa :=
  leaf (.seq (.block hbpZeroInit) (.seq (.loop (.block hbpZeroBody) .ne)
    (.seq (.block hbpSetup) (.loop hbpPoly .ne))))

/-! ## `vg_mldsa_hint_bit_unpack` -/

/-- `ecx = h`, `edx = hlen`, `eax = 0`. -/
def hbuZeroInit : List Instr := [.mov .ecx (.mem (at_ .esp 32)), .mov .edx (.mem (at_ .esp 36)), .mov .eax (.imm 0)]

/-- Zero the word at `ecx`, and on to the next. -/
def hbuZeroBody : List Instr := [.store (at_ .ecx 0) .eax, .alu .add .ecx (.imm 4), .alu .sub .edx (.imm 1)]

/-- `ecx = h`, `edi = y`, `[esp + 24] ← k = len - ω`, `[esp + 36] ← y + ω`,
`esi = 1`. -/
def hbuSetup : List Instr :=
  [.mov .ecx (.mem (at_ .esp 32)), .mov .edi (.mem (at_ .esp 20)), .mov .edx (.mem (at_ .esp 24)),
    .alu .sub .edx (.mem (at_ .esp 28)), .mov .esi (.reg .edi), .alu .add .esi (.mem (at_ .esp 28)),
    .store (at_ .esp 24) .edx, .store (at_ .esp 36) .esi, .mov .esi (.imm 1)]

/-- A failed check: the index becomes 256. -/
def hbuFail : Prog isa := .block [.mov .eax (.imm 256)]

/-- Set coefficient `y[index]` (in `ebp`) of the polynomial at `ecx`, and
increment the index. -/
def hbuSet : List Instr :=
  [.alu .add .ebp (.reg .ebp), .alu .add .ebp (.reg .ebp), .alu .add .ebp (.reg .ecx), .store (at_ .ebp 0) .esi,
    .alu .add .eax (.imm 1)]

/-- `ebp = y[index]` and `edx = y[index - 1]`, compared. -/
def hbuLoads : List Instr :=
  [.mov .edx (.reg .edi), .alu .add .edx (.reg .eax), .movzx8 .ebp (at_ .edx 0), .alu .sub .edx (.imm 1),
    .movzx8 .edx (at_ .edx 0), .alu .cmp .edx (.reg .ebp)]

/-- A coefficient after the first: `y[index - 1] < y[index]`, or fail. -/
def hbuNext : Prog isa :=
  .seq (.block hbuLoads) (.seq (.ite .b (.block hbuSet) hbuFail) (.block [.alu .cmp .eax (.reg .ebx)]))

/-- The first coefficient: `ebp = y[index]`. -/
def hbuFirst : List Instr := [.mov .edx (.reg .edi), .alu .add .edx (.reg .eax), .movzx8 .ebp (at_ .edx 0)]

/-- The coefficients of the polynomial, while the index is less than the
bound `ebx`: the first, then the others. -/
def hbuCoefs : Prog isa :=
  .seq (.block [.alu .cmp .eax (.reg .ebx)])
    (.ite .b
      (.seq (.block hbuFirst) (.seq (.block (hbuSet ++ [.alu .cmp .eax (.reg .ebx)]))
        (.ite .b (.loop hbuNext .b) (.block []))))
      (.block []))

/-- Polynomial `i`: the bound `y[ω + i]` (whose address is in `[esp + 36]`),
checked, and the coefficients up to it. -/
def hbuPoly : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .esp 36))])
    (.seq (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)])
      (.ite .b hbuFail
        (.seq (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) (.ite .b hbuFail hbuCoefs))))

/-- On to the next polynomial. -/
def hbuPolyEnd : List Instr :=
  [.mov .edx (.mem (at_ .esp 36)), .alu .add .edx (.imm 1), .store (at_ .esp 36) .edx, .alu .add .ecx (.imm 1024),
    .mov .edx (.mem (at_ .esp 24)), .alu .sub .edx (.imm 1), .store (at_ .esp 24) .edx]

/-- The byte `y[index]`, compared with 0. -/
def hbuTrailLoad : List Instr := [.mov .edx (.reg .edi), .alu .add .edx (.reg .eax), .movzx8 .edx (at_ .edx 0),
  .alu .cmp .edx (.imm 0)]

/-- The bytes from the index up to `ω` are zero, or fail. -/
def hbuTrail : Prog isa :=
  .seq (.block [.alu .cmp .eax (.mem (at_ .esp 28))])
    (.ite .b
      (.loop (.seq (.block hbuTrailLoad)
        (.seq (.ite .ne hbuFail (.block [.alu .add .eax (.imm 1)])) (.block [.alu .cmp .eax (.mem (at_ .esp 28))]))) .b)
      (.block []))

/-- `eax ← 1` if the index is at most `ω`, 0 otherwise. -/
def hbuRet : List Instr := [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .eax), .mov .eax (.imm 1),
  .alu .sbb .eax (.imm 0)]

def hintBitUnpack : Prog isa :=
  leaf (.seq (.block hbuZeroInit) (.seq (.loop (.block hbuZeroBody) .ne)
    (.seq (.block hbuSetup)
      (.seq (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) (.seq hbuTrail (.block hbuRet))))))

end VG.Impl.MlDsa.X86.Pack
