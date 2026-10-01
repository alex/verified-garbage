import VerifiedGarbage.Impl.MlKem.AArch64.Basic
import VerifiedGarbage.Impl.Sha3.AArch64.Stream

/-!
# ML-DSA on AArch64: sampling from SHAKE

The sampling functions `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball` share a layout and
a prologue, as on x86-64. Each keeps its working space `scratch` (2048
bytes) in `x25`, its output polynomial in `x26` and its parameter (`eta`,
`gamma1` or `tau`, zero-extended; 0 for `vg_mldsa_rej_ntt_poly`) in `x27`,
whose caller's values it saves, with its return address `x30`, in
`scratch[2016..2048)` (`pro`) and restores at the end (`epi`); the Keccak
functions it calls preserve `x25`–`x27` without touching them (they save and
restore `x19`–`x24` through memory, where the taint analysis would lose
that they are public). `scratch` holds, from byte 0, the
Keccak state (200 bytes), the working space of the sponge functions (640
bytes) and, from byte 840, the XOF output.

`sponge rate outlen` hashes the message at `x3` of `x4` bytes: it zeroes the
state (the empty message), absorbs the message with `vg_keccak_absorb`, pads
it with `vg_keccak_pad` (SHAKE's suffix `0x1f`) from the position absorbing
returns, and squeezes `outlen` bytes to `scratch + 840` with
`vg_keccak_squeeze`: whole blocks of the rate, so that no permutation is
wasted. Its addresses and branches depend only on the pointers and the length.

A loop that stores coefficients one at a time keeps `x3` at the next one
and `x4` = 256 minus their number.
-/

namespace VG.Impl.MlDsa.AArch64.Sample

open VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)

/-- Where the XOF output starts in `scratch`. -/
abbrev outOff : Nat := 840

/-- Save `x25`, `x26`, `x27` and `x30` at `scr + 2016`, and set up the layout:
`x25` = `scr`, `x26` = `a`, `x27` = the parameter (`prm`), `x3` = the
message (from `x0`) and `x4` = its length (`len`). -/
def pro (scr a : Reg) (prm len : Instr) : List Instr :=
  [.str .x .x25 scr 2016, .str .x .x26 scr 2024, .str .x .x27 scr 2032, .str .x .x30 scr 2040,
    mov .x25 scr, mov .x26 a, prm, mov .x3 .x0, len]

/-- The 25 lanes of the state at `x25`, zeroed (with `x9`). -/
def zeroSt : List Instr := .movz .x .x9 0 0 :: (List.range 25).map fun k => .str .x .x9 .x25 (8 * k)

/-- The arguments of `absorb` but the message (`x3`, `x4`). -/
def absArgs (rate : Nat) : List Instr :=
  [mov .x0 .x25, .movz .x .x1 (BitVec.ofNat 16 rate) 0, .movz .x .x2 0 0, .addImm .x .x5 .x25 200]

/-- The arguments of `pad`, from the position `absorb` returned. -/
def padArgs (rate : Nat) : List Instr :=
  [mov .x2 .x0, mov .x0 .x25, .movz .x .x1 (BitVec.ofNat 16 rate) 0, .movz .x .x3 0x1f 0,
    .addImm .x .x4 .x25 200]

/-- The arguments of `squeeze`. -/
def sqzArgs (rate outlen : Nat) : List Instr :=
  [mov .x0 .x25, .movz .x .x1 (BitVec.ofNat 16 rate) 0, .movz .x .x2 0 0, .addImm .x .x3 .x25 840,
    .movz .x .x4 (BitVec.ofNat 16 outlen) 0, .addImm .x .x5 .x25 200]

/-- `outlen` bytes of SHAKE with the rate `rate` of the message at `x3`, of
`x4` bytes, to `x25 + 840`. -/
def spongeWith (c : Impl.Sha3.AArch64.Callee) (rate outlen : Nat) : Prog isa :=
  .seq (.block (zeroSt ++ absArgs rate))
    (.seq (.call ("vg_keccak_absorb" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c))
      (.seq (.block (padArgs rate))
        (.seq (.call ("vg_keccak_pad" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c))
          (.seq (.block (sqzArgs rate outlen))
            (.call ("vg_keccak_squeeze" ++ c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c))))))

def sponge := spongeWith .scalar

/-- `x30`, `x26`, `x27` and `x25` restored. -/
def epi : List Instr :=
  [.ldr .x .x30 .x25 2040, .ldr .x .x26 .x25 2024, .ldr .x .x27 .x25 2032, .ldr .x .x25 .x25 2016]

/-- `q = 8380417 = 0x7fe001` into `r`. -/
def movQ (r : Reg) : List Instr := [.movz .x r 0xe001 0, .movk .x r 0x7f 1]

/-- The 256 coefficients of the polynomial at `x26` zeroed; `x3` and `x4`
then as for a loop that has stored no coefficient. -/
def zeroPoly : Prog isa :=
  .seq (.block [.movz .x .x9 0 0, mov .x3 .x26, .movz .x .x4 256 0])
    (.loop (.block [.str .w .x9 .x3 0, .addImm .x .x3 .x3 4, .subImm .x .x4 .x4 1]) (.nonzero .x .x4))

/-- `x0 ← 1` if `x4 = 0`, and 0 if `0 < x4 ≤ 256`. -/
def retZ : List Instr := [.subImm .x .x0 .x4 1, .lsr .x .x0 .x0 63]

end VG.Impl.MlDsa.AArch64.Sample
