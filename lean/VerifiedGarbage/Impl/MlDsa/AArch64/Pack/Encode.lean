import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Stream

/-!
# ML-DSA on AArch64: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

Each branches on its public length argument (which its contract makes
`32 d`) to a loop of `Stream.lean` for that width `d`, with groups of `c`
coefficients and `nb` bytes: `(d, c, nb)` is `(3, 8, 3)`, `(4, 2, 1)`,
`(6, 4, 3)`, `(10, 4, 5)`, `(13, 8, 13)`, `(18, 4, 9)` or `(20, 2, 5)`. The
widths `a` and `b` themselves are 32-bit arguments that the code never
reads: the length determines them.

* `simpleBitPack(f = x0, b = w1, out = x2, len = x3)`: the value of a
  coefficient is the coefficient.
* `bitPack(f = x0, a = w1, b = w2, out = x3, len = x4)` (`out` moved to
  `x2`): the value of a reduced coefficient `x` is `b - (x mod± q)`, which
  is `b - x` if `x ≤ b` and `b - x + q` otherwise: `b - x` in 64 bits (`b`
  in `x12`), plus `q` (in `x13`) times its sign bit (`madd`).
* `bitUnpack(v = x0, len = x1, a = w2, b = w3, f = x4)`: the coefficient of
  a field `x` is `b - x` modulo `q`, computed the same way.
* `unpackT1(v = x0, f = x1)` (`f` moved to `x4`): the coefficient of a
  10-bit field `x` is `x · 2¹³` (less than `q`), a shift left by 13.

Every address and branch depends only on the pointers and the length.
-/

namespace VG.Impl.MlDsa.AArch64.Pack

open VG.AArch64
open VG.Impl.MlKem.AArch64 (movImm mov)

/-- `p` if `r = v` (for `v < 4096`), else `e`. Uses `x9`. -/
def sel (r : Reg) (v : Nat) (p e : Prog isa) : Prog isa :=
  .seq (.block [.subImm .x .x9 r v]) (.ite (.zero .x .x9) p e)

/-! ## `vg_mldsa_simple_bit_pack` -/

/-- Coefficient `j` of the group at `x0`, into `x10`. -/
def sbpLd (j : Nat) : List Instr := [.ldr .w .x10 .x0 (4 * j)]

def simpleBitPack : Prog isa :=
  sel .x3 128 (packLoop sbpLd 4 2 1) (sel .x3 192 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5))

/-! ## `vg_mldsa_bit_pack` -/

/-- `b - (x mod± q)` of the coefficient `x` `j` of the group at `x0`, into
`x10`, for `b` in `x12` and `q` in `x13`. Uses `x14`. -/
def bpLd (j : Nat) : List Instr :=
  [.ldr .w .x10 .x0 (4 * j), .sub .x .x10 .x12 .x10, .lsr .x .x14 .x10 63, .madd .x .x10 .x14 .x13 .x10]

/-- The loop for `b = B`. -/
def bpWidth (B d c nb : Nat) : Prog isa := .seq (.block (movImm .x12 (BitVec.ofNat 64 B))) (packLoop bpLd d c nb)

def bitPack : Prog isa :=
  .seq (.block (mov .x2 .x3 :: movImm .x13 (BitVec.ofNat 64 qNat)))
    (sel .x4 96 (bpWidth 2 3 8 3)
      (sel .x4 128 (bpWidth 4 4 2 1)
        (sel .x4 416 (bpWidth 4096 13 8 13)
          (sel .x4 576 (bpWidth 131072 18 4 9) (bpWidth 524288 20 2 5)))))

/-! ## `vg_mldsa_bit_unpack` -/

/-- `b - x` modulo `q` of the field `x` in `x10`, for `b` in `x12` and `q` in
`x13`, to coefficient `j` of the group at `x4`. Uses `x14`. -/
def buFin (j : Nat) : List Instr :=
  [.sub .x .x10 .x12 .x10, .lsr .x .x14 .x10 63, .madd .x .x10 .x14 .x13 .x10, .str .w .x10 .x4 (4 * j)]

/-- The loop for `b = B`. -/
def buWidth (B d c nb : Nat) : Prog isa := .seq (.block (movImm .x12 (BitVec.ofNat 64 B))) (unpackLoop buFin d c nb)

def bitUnpack : Prog isa :=
  .seq (.block (movImm .x13 (BitVec.ofNat 64 qNat)))
    (sel .x1 96 (buWidth 2 3 8 3)
      (sel .x1 128 (buWidth 4 4 2 1)
        (sel .x1 416 (buWidth 4096 13 8 13)
          (sel .x1 576 (buWidth 131072 18 4 9) (buWidth 524288 20 2 5)))))

/-! ## `vg_mldsa_unpack_t1` -/

/-- `x · 2¹³` of the 10-bit field `x` in `x10`, to coefficient `j` of the
group at `x4`. -/
def t1Fin (j : Nat) : List Instr := [.lsl .x .x10 .x10 13, .str .w .x10 .x4 (4 * j)]

def unpackT1 : Prog isa := .seq (.block [mov .x4 .x1]) (unpackLoop t1Fin 10 4 5)

end VG.Impl.MlDsa.AArch64.Pack
