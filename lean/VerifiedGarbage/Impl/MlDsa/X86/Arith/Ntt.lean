import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Impl.MlKem.X86.Ntt
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

The layers are those of ML-KEM on x86 (`Impl.MlKem.X86.layerCode`), with
the butterflies of ML-DSA: a table of 256 zetas is stored in `scratch` as
`u32`s (through `edx`, from `eax = scratch`), and read through `ebp`; the
end of the polynomial, `f + 1024`, is stored in the argument slot of
`scratch`, which the loops over blocks compare their pointer with. In a
block, `esi` points at coefficient `j`, `edi` at `j + len`, and `ecx`
counts the butterflies left. The zetas are in Montgomery form (times
`2³² mod q`), so that `mred` of a coefficient times one is the coefficient
times the zeta, reduced.

* `ntt(f, scratch)` (Algorithm 41): the table of `ζ^BitRev8(m) · 2³² mod q`,
  and the layers with `len` = 128, 64, …, 1, whose zetas are consecutive
  from `m = 1` up. A butterfly computes `t = ζ · f[j + len] mod q` in `ebx`,
  and stores `f[j] - t` (`f[j] + q - t`, reduced) to `f[j + len]` and
  `f[j] + t` (reduced) to `f[j]`.
* `nttInv(f, scratch)` (Algorithm 42): the table of the negated zetas (the
  `z` of Algorithm 42) in Montgomery form, and the layers with `len` = 1,
  2, …, 128, whose zetas are consecutive from `m = 255` down. A butterfly
  stores `f[j] + f[j + len]` (reduced) to `f[j]` and
  `z · (f[j] + q - f[j + len]) mod q` to `f[j + len]`. Then every
  coefficient is multiplied by `8347681 = 256⁻¹ mod q`, in Montgomery form.

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86.Arith

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf layerCode layers zUp zDown ldScratch)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- `ζ^BitRev8(m) · 2³² mod q`. -/
def montZeta (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m % 8380417 * 2 ^ 32 % 8380417

/-- `-ζ^BitRev8(m) · 2³² mod q`. -/
def montNegZeta (m : Nat) : Nat := (8380417 - 1753 ^ Spec.MlDsa.bitRev8 m % 8380417) % 8380417 * 2 ^ 32 % 8380417

/-- `8347681 · 2³² mod q`: `256⁻¹` in Montgomery form. -/
def scaleImm : BitVec 32 := 16382

/-- The 256 entries `t 0, …, t 255` as `u32`s at `[eax]`, through `edx`. -/
def table (t : Nat → Nat) : List Instr :=
  (List.range 256).flatMap fun k => [.mov .edx (.imm (BitVec.ofNat 32 (t k))), .store (at_ .eax (4 * k)) .edx]

/-- The butterfly of `NTT` on `[esi]` and `[edi]` with the zeta at `[ebp]`. -/
def bflyBody : List Instr :=
  [.mov .eax (.mem (at_ .edi 0)), .mov .edx (.mem (at_ .ebp 0)), .mul .edx] +++ mred .ebx +++
  [.mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.imm qImm), .alu .sub .eax (.reg .ebx)] +++
  csubQ .eax .edx +++
  [.store (at_ .edi 0) .eax, .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.reg .ebx)] +++
  csubQ .eax .edx +++
  [.store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- The butterfly of `NTT⁻¹` on `[esi]` and `[edi]` with the zeta at `[ebp]`. -/
def ibflyBody : List Instr :=
  [.mov .ebx (.mem (at_ .esi 0)), .alu .add .ebx (.imm qImm), .alu .sub .ebx (.mem (at_ .edi 0)),
    .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] +++ csubQ .eax .edx +++
  [.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx] +++
  mred .ebx +++
  [.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

/-- The table `t`, `ebp` at entry `z`, and `f + 1024` in the slot of `scratch`. -/
def nttSetup (t : Nat → Nat) (z : Nat) : List Instr :=
  table t +++
  [.mov .ebp (.reg .eax), .alu .add .ebp (.imm (BitVec.ofNat 32 (4 * z))), .mov .edx (.mem (at_ .esp 20)),
    .alu .add .edx (.imm 1024), .store (at_ .esp 24) .edx]

def ntt : Prog isa :=
  leaf (.seq (.block ldScratch) (.seq (.block (nttSetup montZeta 1))
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1])))

/-- `[esi] ← [esi] · 8347681 mod q`, and on to the next coefficient. -/
def scaleBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mov .edx (.imm scaleImm), .mul .edx] +++ mred .ebx +++
  [.store (at_ .esi 0) .ebx, .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)]

def nttInv : Prog isa :=
  leaf (.seq (.block ldScratch) (.seq (.block (nttSetup montNegZeta 255))
    (.seq (layers (layerCode ibflyBody zDown) [1, 2, 4, 8, 16, 32, 64, 128])
      (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
        (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne))))))

end VG.Impl.MlDsa.X86.Arith
