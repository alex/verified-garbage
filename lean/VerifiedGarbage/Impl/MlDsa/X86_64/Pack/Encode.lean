import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream

/-!
# ML-DSA on x86-64: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

Each branches on its public width argument to a loop of `Stream.lean` for
that width `d`, with groups of `c` coefficients and `nb` bytes: `(d, c, nb)`
is `(3, 8, 3)`, `(4, 2, 1)`, `(6, 4, 3)`, `(10, 4, 5)`, `(13, 8, 13)`,
`(18, 4, 9)` or `(20, 2, 5)`.

* `simpleBitPack(f = rdi, b = esi, out = rdx, len = rcx)` (`out` moved to
  `r8`): the value of a coefficient is the coefficient.
* `bitPack(f = rdi, a = esi, b = edx, out = rcx, len = r8)` (`out` moved to
  `r8`): the value of a reduced coefficient `x` is `b - (x mod± q)`, which
  is `b - x` if `x ≤ b` and `b - x + q` otherwise: `b - x` in 32 bits, and
  `q` added where the subtraction borrows (`sbb` makes the borrow a mask).
* `bitUnpack(v = rdi, len = rsi, a = edx, b = ecx, f = r8)` (`f` moved to
  `rsi`): the coefficient of a field `x` is `b - x` modulo `q`, computed the
  same way.
* `unpackT1(v = rdi, f = rsi)`: the coefficient of a 10-bit field `x` is
  `x · 2¹³` (less than `q`), a rotation of the 32-bit `x` right by 19.

Every address and branch depends only on the pointers and the widths.
-/

namespace VG.Impl.MlDsa.X86_64.Pack

open VG.X86_64

/-- `p` if the low 32 bits of `r` are `v`, else `e`. -/
def sel (r : Reg) (v : Nat) (p e : Prog isa) : Prog isa :=
  .seq (.block [.alu32 .cmp r (.imm (BitVec.ofNat 32 v))]) (.ite .e p e)

/-! ## `vg_mldsa_simple_bit_pack` -/

/-- Coefficient `j` of the group at `rdi`, into `rax`. -/
def sbpLd (j : Nat) : List Instr := [.mov32 .rax (.mem (at_ .rdi (4 * j)))]

def simpleBitPack : Prog isa :=
  .seq (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx)])
    (sel .rsi 15 (packLoop sbpLd 4 2 1) (sel .rsi 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5)))

/-! ## `vg_mldsa_bit_pack` -/

/-- `b - (x mod± q)` of the coefficient `x` `j` of the group at `rdi`, into
`rax`, for `b = B`. Uses `r11`. -/
def bpLd (B : Nat) (j : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 B)), .alu32 .sub .rax (.mem (at_ .rdi (4 * j))),
    .alu32 .sbb .r11 (.reg .r11), .alu32 .and .r11 (.imm qImm), .alu32 .add .rax (.reg .r11)]

def bitPack : Prog isa :=
  .seq (.block [.mov32 .rdx (.reg .rdx), .mov .r8 (.reg .rcx)])
    (sel .rdx 2 (packLoop (bpLd 2) 3 8 3)
      (sel .rdx 4 (packLoop (bpLd 4) 4 2 1)
        (sel .rdx 4096 (packLoop (bpLd 4096) 13 8 13)
          (sel .rdx 131072 (packLoop (bpLd 131072) 18 4 9) (packLoop (bpLd 524288) 20 2 5)))))

/-! ## `vg_mldsa_bit_unpack` -/

/-- `b - x` modulo `q` of the field `x` in `rax`, for `b = B`, to
coefficient `j` of the group at `rsi`. Uses `r11`. -/
def buFin (B : Nat) (j : Nat) : List Instr :=
  [.mov32 .r11 (.imm (BitVec.ofNat 32 B)), .alu32 .sub .r11 (.reg .rax), .alu32 .sbb .rax (.reg .rax),
    .alu32 .and .rax (.imm qImm), .alu32 .add .r11 (.reg .rax), .store32 (at_ .rsi (4 * j)) .r11]

def bitUnpack : Prog isa :=
  .seq (.block [.mov32 .rcx (.reg .rcx), .mov .rsi (.reg .r8)])
    (sel .rcx 2 (unpackLoop (buFin 2) 3 8 3)
      (sel .rcx 4 (unpackLoop (buFin 4) 4 2 1)
        (sel .rcx 4096 (unpackLoop (buFin 4096) 13 8 13)
          (sel .rcx 131072 (unpackLoop (buFin 131072) 18 4 9) (unpackLoop (buFin 524288) 20 2 5)))))

/-! ## `vg_mldsa_unpack_t1` -/

/-- `x · 2¹³` of the 10-bit field `x` in `rax`, to coefficient `j` of the
group at `rsi`. -/
def t1Fin (j : Nat) : List Instr := [.shift32 .ror .rax 19, .store32 (at_ .rsi (4 * j)) .rax]

def unpackT1 : Prog isa := unpackLoop t1Fin 10 4 5

end VG.Impl.MlDsa.X86_64.Pack
