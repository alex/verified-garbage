import VerifiedGarbage.Impl.Bignum.X86_64

/-!
# RSA with a precomputed modulus on x86-64

`vg_rsa_public_precompute` writes what Montgomery multiplication needs of a
modulus, `m` and `R² mod m`, once per key; `vg_rsa_public_precomputed`
computes RSAEP from them. Both use the working space, header and arrays of
`vg_rsa_public` (`Impl/Bignum/X86_64.lean`).
-/

namespace VG.Impl.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `w` words (`r12`) from `[rsi]` to `[rbx]`. -/
def copyWords : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .store (ix .rbx .r14) .rax]

/-- `w` (`r12`) times 8 into `rax`. -/
def eightW : List Instr :=
  [.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)]

/-- `w := ⌈k / 8⌉` (`k` from the header) into `r12` and its slot, the
arrays' bases, then the base of `m`'s array into `rbx` and the pointer in
slot `sN` into `rsi`. -/
def head : List Instr :=
  [.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
    .shift .shr .r12 3, .store (hdr sW) .r12] ++ setBases ++
  [.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))]

/-! ## `vg_rsa_public_precompute`

`(pre, pre_len, n, n_len, scratch, scratch_len)`, all in registers: `pre`
in slot `sOut`, `n` in `sN` and `n_len` in `sK`. -/

namespace Precompute

/-- Save the callee-saved registers and the arguments in the header at
`scratch` (`r8`), with its base in `rdi`. -/
def entry : List Instr :=
  (saved.zipIdx.map fun (r, i) => .store { base := .r8, disp := 8 * i } r) ++
  [.store { base := .r8, disp := 8 * sOut } .rdi, .store { base := .r8, disp := 8 * sN } .rdx,
    .store { base := .r8, disp := 8 * sK } .rcx, .mov .rdi (.reg .r8)]

/-- Zeros to the `16 ⌈k / 8⌉` bytes of `pre`, and 0 returned. -/
def fail : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)), .alu .add .rcx (.imm 7),
      .shift .shr .rcx 3, .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .rcx), .mov32 .rax (.imm 0)])
    (.seq (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)
      (.block exit))

/-- The computation, once `m` is known valid: `m` into its array, `-m⁻¹`,
`R² mod m` as `vg_rsa_public` computes it, then `m` and `R² mod m` to
`pre`, and 1 returned. -/
def main : Prog isa := seqs [
  .block head,
  loadBE,
  .block ([.mov .r10 (.reg .rbx), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .rbx))] ++
    minv ++ [.store (hdr sMinv) .r15]),
  -- `2^(b - 1)` for the bit length `b` of `m`, into the array of `R² mod m`.
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  -- `2^w R mod m`, then six squarings: `R² mod m`.
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2,
  -- `m`, then `R² mod m`, to `pre`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))), .mov .rbx (.mem (hdr sOut))],
  copyWords,
  .block (eightW ++ [.alu .add .rbx (.reg .rax), .mov .rsi (.mem (hdr (sArr aR2)))]),
  copyWords,
  .block ([.mov32 .rax (.imm 1)] ++ exit)]

/-- `vg_rsa_public_precompute`. -/
def code : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite .ne fail main)

end Precompute

/-! ## `vg_rsa_public_precomputed`

`(out, out_len, pre, pre_len, e, e_len, input, input_len, scratch,
scratch_len)`, as `vg_rsa_public`'s with `pre` for `n` and the modulus'
length `k = out_len`: `pre` in slot `sN` and `out_len` in `sK`. -/

namespace Precomputed

/-- Whether the exponentiation has met a set bit of `e`: 0 or 1. -/
def sStarted : Nat := sFn 11

/-- Save the callee-saved registers and the arguments in the header, with
the working space's base in `rdi`. -/
def entry : List Instr :=
  [.mov .r11 (.mem { base := .rsp, disp := 24 })] ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  [.store { base := .r11, disp := 8 * sOut } .rdi, .store { base := .r11, disp := 8 * sN } .rdx,
    .store { base := .r11, disp := 8 * sK } .rsi, .store { base := .r11, disp := 8 * sE } .r8,
    .store { base := .r11, disp := 8 * sElen } .r9, .mov .rax (.mem { base := .rsp, disp := 8 }),
    .store { base := .r11, disp := 8 * sIn } .rax, .mov .rdi (.reg .r11)]

/-- `m` and `R² mod m` from `pre` into their arrays, then ZF set unless `m`
is odd, its top word is not zero and `R² mod m < m`: the values of no
modulus are refused before any arithmetic on them. -/
def load : List (Prog isa) := [
  .block head,
  copyWords,
  .block (eightW ++ [.alu .add .rsi (.reg .rax), .mov .rbx (.mem (hdr (sArr aR2)))]),
  copyWords,
  .block [.mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    cfToRbp],
  .block [.mov .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .and .rax (.reg .rbp),
    .mov .rdx (.mem (ix .r10 .r12 (-8))), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .add .rdx (.imm 1), .alu .and .rax (.reg .rdx), .alu .test .rax (.reg .rax)]]

/-- Whether the exponentiation has started, into ZF (clear if it has). -/
def startedTest : List Instr := [.mov .rax (.mem (hdr sStarted)), .alu .test .rax (.reg .rax)]

/-- `Y := X` (the input in Montgomery form), and the exponentiation started. -/
def start : Prog isa :=
  .seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm))), .mov .rbx (.mem (hdr (sArr aY)))])
    (.seq copyWords (.block [.mov32 .rax (.imm 1), .store (hdr sStarted) .rax]))

/-- One bit of `e`, once started: `Y := Y²`; then if the bit is set,
`Y := Y X` once started, or `Y := X` and started. Before the first set bit
`Y` is not used, and squaring 1 is skipped. -/
def expBit : Prog isa :=
  .seq (.block startedTest) (.seq (.ite .ne (mm aY aY aY) (.block []))
    (.seq (.block bitTest)
      (.seq (.ite .ne (.seq (.block startedTest) (.ite .ne (mm aY aY aXm) start)) (.block []))
        (.block bitNext))))

/-- The exponentiation, over the bytes of `e` and their bits, most
significant first. -/
def expLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (hdr sI) .rax, .store (hdr sStarted) .rax])
    (.loop (.seq (.block byteHead) (.seq (.loop expBit .ne) (.block byteNext))) .ne)

/-- `Y R⁻¹`, or 1 if `e = 0`. -/
def finish : Prog isa :=
  .seq (.block startedTest)
    (.ite .ne (mm aY aY aOne)
      (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]) (setWord aY .rcx)))

/-- The computation, once the values are accepted. -/
def rest : Prog isa := seqs [
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  loadBE,
  -- The mask of `input < m`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    cfToRbp],
  -- `-m⁻¹`, and the number 1.
  .block ([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] ++ minv ++
    [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
  setWord aOne .rcx,
  -- `X = input R mod m`, the exponentiation, and the result.
  mm aXm aX aR2, expLoop, finish,
  .block [.mov .rbx (.mem (hdr (sArr aY))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  storeBE,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

/-- `vg_rsa_public_precomputed`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq (seqs load) (.ite .e fail rest))

end Precomputed

end VG.Impl.Rsa.X86_64
