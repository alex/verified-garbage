import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Common
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86-64: `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`ntt(f = rdi, scratch = rsi)` and `nttInv(f = rdi, scratch = rsi)`: the
prologue stores a table of 256 zetas to `scratch` as `u32`s (`storeTab`,
with `r9` = `scratch`): `ζ^BitRev8(m) mod q` for `NTT`, and its negation
`-ζ^BitRev8(m) mod q` for `NTT⁻¹` (the `z` of Algorithm 42). Then each of
the eight layers runs its blocks, with `rsi` pointing at coefficient `j` of
`f`, `r8` at the zeta of the block, `rdi` counting the blocks down and `rcx`
the butterflies of a block; the zeta of the block is in `r9`.

* `NTT` (Algorithm 41): the layers with `len` = 128, 64, …, 1, whose zetas
  are consecutive, from `m = 1` up. A butterfly computes
  `t = ζ · f[j + len] mod q` (with `reduce`, a Barrett reduction with
  `mul`), and stores `f[j] - t` (`f[j] + q - t`, reduced with `csubQ`) to
  `f[j + len]` and `f[j] + t` (reduced) to `f[j]`.
* `NTT⁻¹` (Algorithm 42): the layers with `len` = 1, 2, …, 128, whose zetas
  are consecutive from `m = 255` down. A butterfly stores `f[j] + f[j + len]`
  (reduced) to `f[j]` and `z · (f[j] - f[j + len]) mod q` to `f[j + len]`.
  Then every coefficient is multiplied by `8347681 = 256⁻¹ mod q` and
  reduced.

A block ends with `rsi` advanced past its upper half, so a layer ends with
`rsi` at `f + 1024`, and moves it back. Every address and branch depends
only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64

/-- `ζ^BitRev8(m) mod q`. -/
def zetaTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417

/-- `-ζ^BitRev8(m) mod q`. -/
def negZetaTab (m : Nat) : Nat := (8380417 - zetaTab m) % 8380417

/-- A butterfly of `NTT` on `[rsi]` and `[rsi + 4len]`, with the zeta in `r9`. -/
def bfly (len : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi (4 * len))), .mul .r9] ++ reduce ++
    [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .rdx (.reg .rax), .alu32 .add .rdx (.imm qImm),
      .alu32 .sub .rdx (.reg .r10)] ++ csubQ .rdx .r11 ++
    [.store32 (at_ .rsi (4 * len)) .rdx, .alu32 .add .rax (.reg .r10)] ++ csubQ .rax .r11 ++
    [.store32 (at_ .rsi 0) .rax, .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)]

/-- A butterfly of `NTT⁻¹` on `[rsi]` and `[rsi + 4len]`, with the zeta in `r9`. -/
def bflyInv (len : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .r10 (.mem (at_ .rsi (4 * len))), .mov32 .rdx (.reg .rax),
    .alu32 .add .rdx (.reg .r10)] ++ csubQ .rdx .r11 ++
    [.store32 (at_ .rsi 0) .rdx, .alu32 .add .rax (.imm qImm), .alu32 .sub .rax (.reg .r10)] ++
    csubQ .rax .r11 ++ [.mul .r9] ++ reduce ++
    [.store32 (at_ .rsi (4 * len)) .r10, .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)]

/-- A block of `len` butterflies `b`, with the zeta at `r8`, which then moves
by `dz` bytes (4 or -4). -/
def nttBlk (b : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block [.mov32 .r9 (.mem (at_ .r8 0)), .alu .add .r8 (.imm dz), .mov32 .rcx (.imm (BitVec.ofNat 32 len))])
    (.seq (.loop (.block b) .ne)
      (.block [.alu .add .rsi (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rdi (.imm 1)]))

/-- A layer: its `128 / len` blocks, then `rsi` back to `f`. -/
def nttLay (b : List Instr) (len : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block [.mov32 .rdi (.imm (BitVec.ofNat 32 (128 / len)))])
    (.seq (.loop (nttBlk b len dz) .ne) (.block [.alu .sub .rsi (.imm 1024)]))

/-- The layers of `NTT` with `len` in `lens`. -/
def nttLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bfly len) len 4) (nttLays lens)

/-- The layers of `NTT⁻¹` with `len` in `lens`. -/
def nttInvLays : List Nat → Prog isa
  | [] => .block []
  | len :: lens => .seq (nttLay (bflyInv len) len (-4)) (nttInvLays lens)

/-- The table `t` to `scratch`, and `rsi` = `f`. -/
def nttPro (t : Nat → Nat) : List Instr :=
  [.mov .r9 (.reg .rsi)] ++ storeTab t 256 ++ [.mov .rsi (.reg .rdi), .mov .r8 (.reg .r9)]

def ntt : Prog isa :=
  .seq (.block (nttPro zetaTab ++ [.alu .add .r8 (.imm 4)])) (nttLays [128, 64, 32, 16, 8, 4, 2, 1])

/-- A coefficient times `8347681`, reduced. -/
def scaleBody : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mul .r9] ++ reduce ++
    [.store32 (at_ .rsi 0) .r10, .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)]

def nttInv : Prog isa :=
  .seq (.block (nttPro negZetaTab ++ [.alu .add .r8 (.imm (4 * 255))]))
    (.seq (nttInvLays [1, 2, 4, 8, 16, 32, 64, 128])
      (.seq (.block [.mov32 .r9 (.imm 8347681)])
        (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block scaleBody) .ne))))

end VG.Impl.MlDsa.X86_64.Arith
