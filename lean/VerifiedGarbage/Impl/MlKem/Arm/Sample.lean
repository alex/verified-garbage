import VerifiedGarbage.Impl.MlKem.Arm.Ntt
import VerifiedGarbage.Impl.Sha3.Arm.Stream

/-!
# ML-KEM on 32-bit ARM: `SampleNTT`, and calling the SHA-3 sponge

`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` take their last
arguments on the stack. A caller puts them in `r12` and `lr` (which a call
changes anyway, and whose value, our return address, the callers save
first) and pushes them in a frame around the call (`absorbCall`, `padCall`,
`squeezeCall`); the pop loads the first of them back into `r12`. So each
call uses 8 bytes of stack below the stack pointer.

`vg_mlkem_sample_ntt(seed = r0, a = r1, scratch = r2) -> r0`: the 2048
bytes of `scratch` hold the Keccak state (`[0, 200)`), the working space of
the sponge functions (`[200, 840)`), the 840 bytes of XOF output
(`[840, 1680)`), and our caller's `r4`–`r11` and `lr` (`[1680, 1716)`).
`r4`, `r5` and `r6` keep `seed`, `a` and `scratch` across the calls (the
callees preserve them). The state is zeroed (the empty message), the 34
bytes of the seed absorbed with rate 168, the SHAKE padding (`0x1f`)
absorbed, and 840 bytes squeezed: 280 chunks of three bytes, which the
loop of Algorithm 7 then goes through (`rejBody`), with `r0` the next
chunk, `r1` the next coefficient of `a`, `r2` the number `j` of
coefficients accepted and `r3` the chunks left. A candidate `d` is accepted
if `d < q` and `j < 256`: the AND of the sign bits of `d - q` and
`j - 256`, compared with zero. It returns `j >> 8`: 1 if `j = 256`.

The loop's branches depend on the XOF output, a function of the seed, which
the contract lets the function leak; every address depends only on the
pointers and on `j`, likewise.
-/

namespace VG.Impl.MlKem.Arm

open VG.Arm

/-! ## The sponge functions, with their stack arguments -/

/-- `vg_keccak_absorb(state = r0, rate = r1, pos = r2, data = r3, len = r12,
scratch = lr)`. -/
def absorbCall : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_keccak_absorb" Impl.Sha3.Arm.Stream.absorb) (.pop .r12 8)

/-- `vg_keccak_pad(state = r0, rate = r1, pos = r2, suffix = r3, scratch = lr)`. -/
def padCall : Prog isa :=
  .frame (.push [.lr]) (.call "vg_keccak_pad" Impl.Sha3.Arm.Stream.pad) (.pop .r12 4)

/-- `vg_keccak_squeeze(state = r0, rate = r1, pos = r2, out = r3, outlen = r12,
scratch = lr)`. -/
def squeezeCall : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_keccak_squeeze" Impl.Sha3.Arm.Stream.squeeze) (.pop .r12 8)

/-- The Keccak state at `[b]` zeroed, through `r12`. -/
def zeroState (b : Reg) : List Instr :=
  .mov .r12 (.imm 0) :: (List.range 50).flatMap fun k => [.str .r12 b (4 * k)]

/-! ## `SampleNTT` -/

/-- Our caller's registers saved, the arguments moved to `r4`–`r6`, the
state zeroed. -/
def sampleSetup : List Instr :=
  saveRegs .r2 1680 ++
    ([.str .lr .r2 1712, .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2)] : List Instr) ++
    zeroState .r6

/-- `absorb(state, 168, 0, seed, 34, scratch + 200)`. -/
def absorbSeedArgs : List Instr :=
  [.mov .r0 (.reg .r6), .mov .r1 (.imm 168), .mov .r2 (.imm 0), .mov .r3 (.reg .r4), .mov .r12 (.imm 34),
   .dp .add .lr .r6 (.imm 200)]

/-- `pad(state, 168, pos, 0x1f, scratch + 200)`, with `pos` from `absorb`. -/
def padArgs : List Instr :=
  [.mov .r2 (.reg .r0), .mov .r0 (.reg .r6), .mov .r1 (.imm 168), .mov .r3 (.imm 0x1f),
   .dp .add .lr .r6 (.imm 200)]

/-- `squeeze(state, 168, 0, scratch + 840, 840, scratch + 200)`. -/
def squeezeArgs : List Instr :=
  [.mov .r0 (.reg .r6), .mov .r1 (.imm 168), .mov .r2 (.imm 0), .dp .add .r3 .r6 (.imm 840),
   .mov .r12 (.imm 840), .dp .add .lr .r6 (.imm 200)]

/-- `Z` set unless the candidate `d` is accepted: `d < q` and `j = r2 < 256`. -/
def acceptTest (d : Reg) : List Instr :=
  [.dp .sub .r12 d (.imm 3328), .dp .sub .r12 .r12 (.imm 1), .mov .r12 (.shifted .r12 .lsr 31),
   .dp .sub .r7 .r2 (.imm 256), .mov .r7 (.shifted .r7 .lsr 31), .dp .and .r12 .r12 (.reg .r7),
   .cmp .r12 (.imm 0)]

/-- The candidate `d` stored as the next coefficient, if accepted. -/
def accept (d : Reg) : Prog isa :=
  .ite .eq (.block []) (.block [.str d .r1 0, .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 1)])

/-- The two candidates of the chunk at `r0`: `d₁` in `r10`, `d₂` in `r11`. -/
def candidates : List Instr :=
  [.ldrb .r7 .r0 0, .ldrb .r8 .r0 1, .ldrb .r9 .r0 2, .mov .r10 (.shifted .r8 .lsl 28),
   .dp .add .r10 .r7 (.shifted .r10 .lsr 20), .mov .r11 (.shifted .r8 .lsr 4),
   .dp .add .r11 .r11 (.shifted .r9 .lsl 4)]

/-- An iteration of Algorithm 7, lines 5–15. -/
def rejBody : Prog isa :=
  .seq (.block (candidates ++ acceptTest .r10))
  (.seq (accept .r10)
  (.seq (.block (acceptTest .r11))
  (.seq (accept .r11)
    (.block [.dp .add .r0 .r0 (.imm 3), .subs .r3 .r3 (.imm 1)]))))

/-- The return value, and our caller's registers restored. -/
def sampleEnd : List Instr :=
  [.mov .r0 (.shifted .r2 .lsr 8), .mov .r3 (.reg .r6)] ++ restoreRegs .r3 1680 ++ ([.ldr .lr .r3 1712] : List Instr)

def sampleNTT : Prog isa :=
  .seq (.block sampleSetup)
  (.seq (.seq (.block absorbSeedArgs) absorbCall)
  (.seq (.seq (.block padArgs) padCall)
  (.seq (.seq (.block squeezeArgs) squeezeCall)
  (.seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5), .mov .r2 (.imm 0), .mov .r3 (.imm 280)])
  (.seq (.loop rejBody .ne) (.block sampleEnd))))))

end VG.Impl.MlKem.Arm
