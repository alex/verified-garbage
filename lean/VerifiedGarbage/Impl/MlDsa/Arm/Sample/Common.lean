import VerifiedGarbage.Impl.MlKem.Arm.Sample

/-!
# ML-DSA on 32-bit ARM: sampling from SHAKE

The sampling functions `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball` share a layout and
a prologue, and call the SHA-3 sponge functions as `vg_mlkem_sample_ntt`
does (`Impl.MlKem.Arm.absorbCall`, `padCall`, `squeezeCall`, whose frames
use 8 bytes of stack). Each saves its caller's `r4`–`r11` and `lr` in
`scratch[2012..2048)` (`pro`) and restores them at the end (`epi`); from the
prologue on, `r5` is its output polynomial, `r6` its working space
`scratch` (2048 bytes), `r7` its parameter (`eta`, `gamma1` or `tau`), `r8`
the message hashed and `r9` its length, which the functions it calls
preserve. `scratch` holds, from byte 0, the Keccak state (200 bytes), the
working space of the sponge functions (640 bytes) and, from byte 840, the
XOF output.

`sponge rate outlen` hashes the message: it zeroes the state (the empty
message), absorbs the message with `vg_keccak_absorb`, pads it with
`vg_keccak_pad` (SHAKE's suffix `0x1f`) from the position absorbing returns,
and squeezes `outlen` bytes to `scratch + 840` with `vg_keccak_squeeze`:
whole blocks of the rate, so that no permutation is wasted. Its addresses
and branches depend only on the pointers and the length.
-/

namespace VG.Impl.MlDsa.Arm.Sample

open VG.Arm
open VG.Impl.MlKem.Arm (saveRegs restoreRegs zeroState absorbCall padCall squeezeCall)

/-- Where the XOF output starts in `scratch`. -/
abbrev outOff : Nat := 840

/-- Where our caller's registers are saved in `scratch`. -/
abbrev saveOff : Nat := 2012

/-- Save `r4`–`r11` and `lr` at `scr + 2012`, and set up the layout: `r5` =
`a`, `r6` = `scr`, `r7` = the parameter, `r8` = the message (from `msg`)
and `r9` = its length. `scr`, `a` and `msg` are not among `r4`–`r9`. -/
def pro (scr a : Reg) (prm len : Op2) (msg : Reg) : List Instr :=
  saveRegs scr saveOff ++
    [.str .lr scr (saveOff + 32), .mov .r5 (.reg a), .mov .r6 (.reg scr), .mov .r7 prm, .mov .r8 (.reg msg),
      .mov .r9 len]

/-- The state at `r6` zeroed, and the arguments of `absorb`:
`absorb(state, rate, 0, msg, len, scratch + 200)`. -/
def absArgs (rate : Nat) : List Instr :=
  zeroState .r6 ++
    [.mov .r0 (.reg .r6), .mov .r1 (.imm (BitVec.ofNat 32 rate)), .mov .r2 (.imm 0), .mov .r3 (.reg .r8),
      .mov .r12 (.reg .r9), .dp .add .lr .r6 (.imm 200)]

/-- `pad(state, rate, pos, 0x1f, scratch + 200)`, with `pos` from `absorb`. -/
def padArgs (rate : Nat) : List Instr :=
  [.mov .r2 (.reg .r0), .mov .r0 (.reg .r6), .mov .r1 (.imm (BitVec.ofNat 32 rate)), .mov .r3 (.imm 0x1f),
    .dp .add .lr .r6 (.imm 200)]

/-- `squeeze(state, rate, 0, scratch + 840, outlen, scratch + 200)`. -/
def sqzArgs (rate outlen : Nat) : List Instr :=
  [.mov .r0 (.reg .r6), .mov .r1 (.imm (BitVec.ofNat 32 rate)), .mov .r2 (.imm 0), .dp .add .r3 .r6 (.imm 840),
    .mov .r12 (.imm (BitVec.ofNat 32 outlen)), .dp .add .lr .r6 (.imm 200)]

/-- `outlen` bytes of SHAKE with the rate `rate` of the message at `r8`, of
`r9` bytes, to `r6 + 840`. -/
def sponge (rate outlen : Nat) : Prog isa :=
  .seq (.block (absArgs rate))
    (.seq absorbCall
      (.seq (.block (padArgs rate))
        (.seq padCall
          (.seq (.block (sqzArgs rate outlen)) squeezeCall))))

/-- Our caller's `r4`–`r11` and `lr` restored, through `r3`. -/
def epi : List Instr := [.mov .r3 (.reg .r6)] ++ restoreRegs .r3 saveOff ++ [.ldr .lr .r3 (saveOff + 32)]

/-- `r0 ← r2 >> 8`: 1 if `r2` = 256, 0 if it is less. -/
def retJ : List Instr := [.mov .r0 (.shifted .r2 .lsr 8)]

/-- `Z` set iff `r2 ≥ 256` (`r2` less than `2³¹`), through `r11`. -/
def jFull : List Instr := [.dp .sub .r11 .r2 (.imm 256), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]

/-- Store `v` to `a[r2]` (`r5 + 4 r2`, through `r11`) and increment `r2`. -/
def storeJ (v : Reg) : List Instr :=
  [.dp .add .r11 .r5 (.shifted .r2 .lsl 2), .str v .r11 0, .dp .add .r2 .r2 (.imm 1)]

/-- `r0 ← r0 + k`, `r3 ← r3 - 1`: the step of a loop over the XOF output. -/
def step (k : Nat) : List Instr := [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 k)), .subs .r3 .r3 (.imm 1)]

end VG.Impl.MlDsa.Arm.Sample
