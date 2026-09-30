import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_expand_mask_poly`

`expandMask(seed = x0, gamma1 = w1, a = x2, scratch = x3)` (see
`Common.lean` for the layout) squeezes 640 bytes of SHAKE256 of the 66 bytes
of the seed (5 blocks, which also hold the 576 bytes that `γ₁ = 2¹⁷` needs),
and unpacks the first `32c` of them, `c = 18` or `20` (`emLoop c`, chosen by
a branch on the public `γ₁`), four coefficients of `c` bits (a group of
`c/2` bytes, at `x2`) at a time: the group's first 8 bytes are loaded as a
`u64` (`x6`), and its last `c/2 - 8` bytes one at a time (`x7`, and `x11`
for `c = 20`); the first three fields are bits `ck` to `ck + c - 1` of
`x6`, shifted and masked (with `x8` = `2ᶜ - 1`), and the last is the top
`64 - 3c` bits of `x6` plus the last bytes above them. Coefficient `i` is
`γ₁` minus its field, stored modulo `q` (`q`, in `x9`, added where the
difference is negative, by its sign bit). There is no branch on the data,
and the addresses depend only on the pointers and `γ₁`: it is constant
time.
-/

namespace VG.Impl.MlDsa.AArch64.Sample

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)

/-- The bytes of the group at `x2`: the first 8 in `x6`, the 9th in `x7`,
the 10th in `x11` (`c = 20`). -/
def emLoad (c : Nat) : List Instr :=
  [.ldr .x .x6 .x2 0, .ldrb .x7 .x2 8] ++ (if c = 20 then [.ldrb .x11 .x2 9] else [])

/-- Field `k` of the group into `x12`. -/
def emField (c k : Nat) : List Instr :=
  if k = 0 then [.logic .and .x .x12 .x6 .x8]
  else if k < 3 then [.lsr .x .x12 .x6 (c * k), .logic .and .x .x12 .x12 .x8]
  else [.lsr .x .x12 .x6 (3 * c), .lsl .x .x13 .x7 (64 - 3 * c), .add .x .x12 .x12 .x13] ++
    (if c = 20 then [.lsl .x .x13 .x11 12, .add .x .x12 .x12 .x13] else [])

/-- `γ₁` (in `x27`) minus the field `x12`, modulo `q`, to coefficient `k` of
the group at `x3`. -/
def emStore (k : Nat) : List Instr :=
  [.sub .x .x13 .x27 .x12, .lsr .x .x14 .x13 63, .madd .x .x13 .x14 .x9 .x13, .str .w .x13 .x3 (4 * k)]

/-- An iteration: 4 coefficients. -/
def emBody (c : Nat) : List Instr :=
  emLoad c ++ (List.range 4).flatMap (fun k => emField c k ++ emStore k) ++
    [.addImm .x .x2 .x2 (c / 2), .addImm .x .x3 .x3 16, .subImm .x .x5 .x5 1]

/-- The 64 iterations, from the XOF output at `scratch + 840`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block ([.addImm .x .x2 .x25 840, mov .x3 .x26, .movz .x .x5 64 0,
      .movz .x .x8 (BitVec.ofNat 16 (2 ^ (c - 16) - 1)) 1, .movk .x .x8 0xffff 0] ++ movQ .x9))
    (.loop (.block (emBody c)) (.nonzero .x .x5))

def expandMask : Prog isa :=
  .seq (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0)))
    (.seq (sponge 136 640)
      (.seq (.seq (.block [.lsr .x .x9 .x27 18]) (.ite (.zero .x .x9) (emLoop 18) (emLoop 20)))
        (.block epi)))

end VG.Impl.MlDsa.AArch64.Sample
