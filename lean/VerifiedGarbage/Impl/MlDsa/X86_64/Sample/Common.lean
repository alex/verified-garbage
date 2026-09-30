import VerifiedGarbage.Impl.MlKem.X86_64.Sample

/-!
# ML-DSA on x86-64: sampling from SHAKE

The sampling functions `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball` share a layout and
a prologue. Each keeps its working space `scratch` (2048 bytes) in `rbx`, its
output polynomial in `rbp` and its parameter (`eta`, `gamma1` or `tau`) in
`r12`, whose caller's values it saves in `scratch[2024..2048)` (`save`) and
restores at the end (`epi`); the functions it calls preserve them. `scratch`
holds, from byte 0, the Keccak state (200 bytes), the working space of the
sponge functions (640 bytes) and, from byte 840, the XOF output.

`sponge rate outlen` hashes the message at `rcx` of `r8` bytes: it zeroes the
state (the empty message), absorbs the message with `vg_keccak_absorb`, pads
it with `vg_keccak_pad` (SHAKE's suffix `0x1f`) from the position absorbing
returns, and squeezes `outlen` bytes to `scratch + 840` with
`vg_keccak_squeeze`: whole blocks of the rate, so that no permutation is
wasted. Its addresses and branches depend only on the pointers and the length.
-/

namespace VG.Impl.MlDsa.X86_64.Sample

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- Where the XOF output starts in `scratch`. -/
abbrev outOff : Nat := 840

/-- Save `rbx`, `rbp` and `r12` at `scr + 2024`, and set up the layout: `rbx`
= `scr`, `rbp` = `a`, `r12` = the parameter, `rcx` = the message (from `rdi`)
and `r8` = its length. -/
def pro (scr a : Reg) (prm len : Src) : List Instr :=
  [.store (at_ scr 2024) .rbx, .store (at_ scr 2032) .rbp, .store (at_ scr 2040) .r12, .mov .rbx (.reg scr),
    .mov .rbp (.reg a), .mov32 .r12 prm, .mov .rcx (.reg .rdi), .mov .r8 len]

/-- The 25 lanes of the state at `rbx`, zeroed (as `vg_mlkem_sample_ntt` does). -/
def zeroSt : List Instr := [.mov32 .rax (.imm 0)] ++ Impl.MlKem.X86_64.zeroSt .rbx 0

/-- The arguments of `absorb` but the message (`rcx`, `r8`). -/
def absArgs (rate : BitVec 32) : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm rate), .mov32 .rdx (.imm 0), .mov .r9 (.reg .rbx),
    .alu .add .r9 (.imm 200)]

/-- The arguments of `pad`, from the position `absorb` returned. -/
def padArgs (rate : BitVec 32) : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm rate), .mov .rdx (.reg .rax), .mov32 .rcx (.imm 0x1f),
    .mov .r8 (.reg .rbx), .alu .add .r8 (.imm 200)]

/-- The arguments of `squeeze`. -/
def sqzArgs (rate outlen : BitVec 32) : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm rate), .mov32 .rdx (.imm 0), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm 840), .mov32 .r8 (.imm outlen), .mov .r9 (.reg .rbx), .alu .add .r9 (.imm 200)]

/-- `outlen` bytes of SHAKE with the rate `rate` of the message at `rcx`, of
`r8` bytes, to `rbx + 840`. -/
def sponge (rate outlen : BitVec 32) : Prog isa :=
  .seq (.block (zeroSt ++ absArgs rate))
    (.seq (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb)
      (.seq (.block (padArgs rate))
        (.seq (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad)
          (.seq (.block (sqzArgs rate outlen))
            (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze)))))

/-- `rbp`, `r12` and `rbx` restored. -/
def epi : List Instr :=
  [.mov .rbp (.mem (at_ .rbx 2032)), .mov .r12 (.mem (at_ .rbx 2040)), .mov .rbx (.mem (at_ .rbx 2024))]

/-- `rax ← rdi >> 8`: 1 if `rdi` = 256, 0 if it is less. -/
def retJ : List Instr := [.mov .rax (.reg .rdi), .shift .shr .rax 8]

/-- `a[rdi]`: `[rbp + 4 rdi]`. -/
def aJ : MemOp := { base := .rbp, index := some .rdi, scale := 4 }

end VG.Impl.MlDsa.X86_64.Sample
