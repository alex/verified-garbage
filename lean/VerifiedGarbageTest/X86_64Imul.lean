import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for x86-64 `imul r64, r64`

Each expected value (the low 64 bits of the product, CF and OF) was computed
on an x86-64 CPU by the same instruction (`imul rax, rcx`, then `setc` and
`seto`), and is compared with the model's result on the same inputs. The
cases cover a product that fits, `(−1) · (−1)`, products that overflow into
the sign bit or beyond it, and `(−1) · (−2⁶³)`, whose signed result `2⁶³`
does not fit.
-/

namespace VG.Test.Imul

open X86_64

/-- The state after `imul rax, rcx` with `a` in `rax` and `b` in `rcx`. -/
def run (a b : BitVec 64) : Option State :=
  exec (.imul .rax .rcx)
    { gpr := fun r => if r = .rax then a else if r = .rcx then b else 0
      cf := none, zf := none, sf := none, of := none
      mem := fun _ => 0, rd := [], wr := [] }

/-- `rax`, CF and OF after `imul rax, rcx`, and that SF and ZF are undefined. -/
def check (a b r : BitVec 64) (o : Bool) : Bool :=
  match run a b with
  | some s => s.gpr .rax == r && s.cf == some o && s.of == some o && s.sf == none &&
      s.zf == none && s.gpr .rcx == b
  | none => false

#guard check 3 5 0xf false
#guard check 0xffffffffffffffff 0xffffffffffffffff 1 false
#guard check 0x8000000000000000 2 0 true
#guard check 0x0123456789abcdef 0xfedcba9876543210 0x2236d88fe5618cf0 true
#guard check 0x4000000000000000 2 0x8000000000000000 true
#guard check 0xffffffffffffffff 0x8000000000000000 0x8000000000000000 true

#guard Instr.asm (.imul .rax .r10) == ["imul rax, r10"]

-- `imul r64, r64` is in the x86-64 baseline.
#guard isa.requires (.imul .rax .r10) == []

end VG.Test.Imul
