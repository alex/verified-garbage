import VerifiedGarbage.Impl.MlDsa.X86.Pack.Stream

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

Each is a leaf (`leaf`: it saves the caller's `ebx`, `esi`, `edi` and `ebp`,
so its arguments are at `[esp + 20]`, `[esp + 24]`, …) that loads its
input pointer into `esi` and its output pointer into `edi`, and branches on
its public width argument (in `eax`) to a loop of `Stream.lean` for that
width `d`, with groups of `c` coefficients and `nb` bytes: `(d, c, nb)` is
`(3, 8, 3)`, `(4, 2, 1)`, `(6, 4, 3)`, `(10, 4, 5)`, `(13, 8, 13)`,
`(18, 4, 9)` or `(20, 2, 5)`.

* `simpleBitPack(f, b, out, len)`: the value of a coefficient is the
  coefficient.
* `bitPack(f, a, b, out, len)`: the value of a reduced coefficient `x` is
  `b - (x mod± q)`, which is `b - x` if `x ≤ b` and `b - x + q` otherwise:
  `b - x`, and `q` added where the subtraction borrows (`sbb` makes the
  borrow a mask).
* `bitUnpack(v, len, a, b, f)`: the coefficient of a field `x` is `b - x`
  modulo `q`, computed the same way.
* `unpackT1(v, f)`: the coefficient of a 10-bit field `x` is `x · 2¹³`
  (less than `q`), a rotation of `x` right by 19.

Every address and branch depends only on the pointers and the widths.
-/

namespace VG.Impl.MlDsa.X86.Pack

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-! ## `vg_mldsa_simple_bit_pack` -/

/-- Coefficient `j` of the group at `esi`, into `eax`. -/
def sbpLd (j : Nat) : List Instr := [.mov .eax (.mem (at_ .esi (4 * j)))]

def simpleBitPack : Prog isa :=
  leaf (.seq (.block (ldArgs 0 2 1))
    (sel 15 (packLoop sbpLd 4 2 1) (sel 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5))))

/-! ## `vg_mldsa_bit_pack` -/

/-- `b - (x mod± q)` of the coefficient `x` `j` of the group at `esi`, into
`eax`, for `b = B`. Uses `edx`. -/
def bpLd (B : Nat) (j : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 B)), .alu .sub .eax (.mem (at_ .esi (4 * j))),
    .alu .sbb .edx (.reg .edx), .alu .and .edx (.imm qImm), .alu .add .eax (.reg .edx)]

def bitPack : Prog isa :=
  leaf (.seq (.block (ldArgs 0 3 2))
    (sel 2 (packLoop (bpLd 2) 3 8 3)
      (sel 4 (packLoop (bpLd 4) 4 2 1)
        (sel 4096 (packLoop (bpLd 4096) 13 8 13)
          (sel 131072 (packLoop (bpLd 131072) 18 4 9) (packLoop (bpLd 524288) 20 2 5))))))

/-! ## `vg_mldsa_bit_unpack` -/

/-- `b - x` modulo `q` of the field `x` in `eax`, for `b = B`, to
coefficient `j` of the group at `edi`. Uses `edx`. -/
def buFin (B : Nat) (j : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 B)), .alu .sub .edx (.reg .eax), .alu .sbb .eax (.reg .eax),
    .alu .and .eax (.imm qImm), .alu .add .edx (.reg .eax), .store (at_ .edi (4 * j)) .edx]

def bitUnpack : Prog isa :=
  leaf (.seq (.block (ldArgs 0 4 3))
    (sel 2 (unpackLoop (buFin 2) 3 8 3)
      (sel 4 (unpackLoop (buFin 4) 4 2 1)
        (sel 4096 (unpackLoop (buFin 4096) 13 8 13)
          (sel 131072 (unpackLoop (buFin 131072) 18 4 9) (unpackLoop (buFin 524288) 20 2 5))))))

/-! ## `vg_mldsa_unpack_t1` -/

/-- `x · 2¹³` of the 10-bit field `x` in `eax`, to coefficient `j` of the
group at `edi`. -/
def t1Fin (j : Nat) : List Instr := [.shift .ror .eax 19, .store (at_ .edi (4 * j)) .eax]

def unpackT1 : Prog isa := leaf (.seq (.block (ldPtrs 0 1)) (unpackLoop t1Fin 10 4 5))

end VG.Impl.MlDsa.X86.Pack
