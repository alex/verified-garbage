import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Stream

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

Each branches on its public width argument to a loop of `Stream.lean` for
that width `d`, with groups of `c` coefficients and `nb` bytes, as on x86-64:
`(d, c, nb)` is `(3, 8, 3)`, `(4, 2, 1)`, `(6, 4, 3)`, `(10, 4, 5)`,
`(13, 8, 13)`, `(18, 4, 9)` or `(20, 2, 5)`.

* `simpleBitPack(f = r0, b = r1, out = r2, len = r3)`: the value of a
  coefficient is the coefficient. It uses only `r0`–`r3` and `r12`.
* `bitPack(f = r0, a = r1, b = r2, out = r3, len = [sp])` (`out` moved to
  `r2`, `b` to `r12`): the value of a reduced coefficient `x` is
  `b - (x mod± q)`, which is `b - x` if `x ≤ b` and `b - x + q` otherwise:
  `b - x` in 32 bits, and `q` added if it is negative (`bMinus`). It needs
  `r4` as well, which it saves in a frame on the stack (4 bytes).
* `bitUnpack(v = r0, len = r1, a = r2, b = r3, f = [sp])` (`f` loaded into
  `r1`): the coefficient of a field `x` is `b - x` modulo `q`, computed the
  same way; it saves `r4` in a frame, so `f` is then at `[sp, #4]`.
* `unpackT1(v = r0, f = r1)`: the coefficient of a 10-bit field `x` is
  `x · 2¹³` (less than `q`), a shift. It uses only `r0`–`r3` and `r12`.

Every address and branch depends only on the pointers and the widths.
-/

namespace VG.Impl.MlDsa.Arm.Pack

open VG.Arm

/-- `p` if `r` is `v`, else `e`. -/
def sel (r : Reg) (v : Nat) (p e : Prog isa) : Prog isa :=
  .seq (.block [.cmp r (.imm (BitVec.ofNat 32 v))]) (.ite .eq p e)

/-! ## `vg_mldsa_simple_bit_pack` -/

/-- Coefficient `j` of the group at `r0`, into `r12`. -/
def sbpLd (j : Nat) : List Instr := [.ldr .r12 .r0 (4 * j)]

def simpleBitPack : Prog isa :=
  sel .r1 15 (packLoop sbpLd 4 2 1) (sel .r1 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5))

/-! ## `vg_mldsa_bit_pack` -/

/-- `b - (x mod± q)` of the coefficient `x` `j` of the group at `r0`, into
`r12`, for `b = B`. Uses `r4`. -/
def bpLd (B : Nat) (j : Nat) : List Instr := .ldr .r4 .r0 (4 * j) :: bMinus B .r12 .r4

/-- The body of `bitPack`, in its frame. -/
def bitPackBody : Prog isa :=
  .seq (.block [.mov .r12 (.reg .r2), .mov .r2 (.reg .r3)])
    (sel .r12 2 (packLoop (bpLd 2) 3 8 3)
      (sel .r12 4 (packLoop (bpLd 4) 4 2 1)
        (sel .r12 4096 (packLoop (bpLd 4096) 13 8 13)
          (sel .r12 131072 (packLoop (bpLd 131072) 18 4 9) (packLoop (bpLd 524288) 20 2 5)))))

def bitPack : Prog isa := .frame (.push [.r4]) bitPackBody (.pop .r4 4)

/-! ## `vg_mldsa_bit_unpack` -/

/-- `b - x` modulo `q` of the field `x` in `r12`, for `b = B`, to
coefficient `j` of the group at `r1`. Uses `r4`. -/
def buFin (B : Nat) (j : Nat) : List Instr := bMinus B .r4 .r12 ++ [.str .r4 .r1 (4 * j)]

/-- The body of `bitUnpack`, in its frame. -/
def bitUnpackBody : Prog isa :=
  .seq (.block [.ldrSp .r1 4])
    (sel .r3 2 (unpackLoop (buFin 2) 3 8 3)
      (sel .r3 4 (unpackLoop (buFin 4) 4 2 1)
        (sel .r3 4096 (unpackLoop (buFin 4096) 13 8 13)
          (sel .r3 131072 (unpackLoop (buFin 131072) 18 4 9) (unpackLoop (buFin 524288) 20 2 5)))))

def bitUnpack : Prog isa := .frame (.push [.r4]) bitUnpackBody (.pop .r4 4)

/-! ## `vg_mldsa_unpack_t1` -/

/-- `x · 2¹³` of the 10-bit field `x` in `r12`, to coefficient `j` of the
group at `r1`. -/
def t1Fin (j : Nat) : List Instr := [.mov .r12 (.shifted .r12 .lsl 13), .str .r12 .r1 (4 * j)]

def unpackT1 : Prog isa := unpackLoop t1Fin 10 4 5

end VG.Impl.MlDsa.Arm.Pack
