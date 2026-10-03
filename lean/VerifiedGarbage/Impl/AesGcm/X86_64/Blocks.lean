import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch

/-!
# AES-GCM on whole blocks: x86-64 implementation

`vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks`
`(ctx = rdi, rounds = rsi, counter = rdx, y = rcx, data = r8, n = r9,
scratch = [rsp + 8])`, generic over the implementations of `vg_aes_ctr32` and
`vg_ghash` they call, as the other functions of AES-GCM.

The entry keeps the arguments in `scratch` (`ctx`, `rounds`, `counter`, `y`,
`data` and `n` at `scratch` … `scratch + 40`). With `stitch` (VAES and
VPCLMULQDQ), the first `16 ⌊n / 16⌋` blocks, if any, are encrypted and hashed
in one pass (`Gcm.X86_64.Stitch`, with the powers of `H` at `scratch + 64`),
and the arguments kept become those of the rest. The rest (all the blocks,
without `stitch`) is then encrypted with `vg_aes_ctr32` and hashed with
`vg_ghash` (hashed first when decrypting), each called with `scratch + 64`,
reloading the arguments from `scratch` after each call.
-/

namespace VG.Impl.AesGcm.X86_64.Blocks

open VG.X86_64

/-- Where the entry keeps the arguments, in `scratch`. -/
def argCtx : Nat := 0
def argRounds : Nat := 8
def argCtr : Nat := 16
def argY : Nat := 24
def argData : Nat := 32
def argN : Nat := 40

/-- The arguments kept, with `scratch` in `r11`. -/
def entry : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .store (at_ .r11 argCtx) .rdi, .store (at_ .r11 argRounds) .rsi,
    .store (at_ .r11 argCtr) .rdx, .store (at_ .r11 argY) .rcx, .store (at_ .r11 argData) .r8,
    .store (at_ .r11 argN) .r9]

/-- If there are at least 16 blocks, the first `16 ⌊n / 16⌋` by `piece`, with
`r11` at the powers, `scratch + 64`. -/
def stitchPart (piece : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (imm 16)])
    (.ite .b (.block [])
      (.seq (.block [.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax),
        .alu .add .r11 (imm 64)]) piece))

/-- The arguments of the rest: `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
def rest : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .mov .rax (.reg .r8),
    .alu .and .r8 (imm 15), .alu .sub .rax (.reg .r8), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.mem (at_ .r11 argData)),
    .store (at_ .r11 argData) .rax, .store (at_ .r11 argN) .r8]

/-- The arguments of `vg_aes_ctr32` on the rest. -/
def ctrArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .mov .rdi (.mem (at_ .r11 argCtx)), .mov .rsi (.mem (at_ .r11 argRounds)),
    .mov .rdx (.mem (at_ .r11 argCtr)), .mov .rcx (.mem (at_ .r11 argData)), .mov .r8 (.mem (at_ .r11 argN)),
    .mov .r9 (.reg .r11), .alu .add .r9 (imm 64)]

/-- The arguments of `vg_ghash` on the rest. -/
def ghArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)), .mov .rdi (.mem (at_ .r11 argCtx)), .alu .add .rdi (imm 240),
    .mov .rsi (.mem (at_ .r11 argY)), .mov .rdx (.mem (at_ .r11 argData)), .mov .rcx (.mem (at_ .r11 argN)),
    .mov .r8 (.reg .r11), .alu .add .r8 (imm 64)]

variable (ctr gh : Fn)

/-- The rest, if any, with `first` and then `second`. -/
def tail (first second : Prog isa) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq first second))

def ctrCall : Prog isa := .seq (.block ctrArgs) (.call ctr.name ctr.code)
def ghCall : Prog isa := .seq (.block ghArgs) (.call gh.name gh.code)

/-- The first blocks by `piece` (with `stitch`), then the rest. -/
def blocks (stitch : Bool) (piece : Prog isa) (first second : Prog isa) : Prog isa :=
  .seq (.block entry)
    (.seq (if stitch then .seq (stitchPart piece) (.block rest) else .block []) (tail first second))

/-- `vg_aes_gcm_encrypt_blocks`. -/
def encrypt (stitch : Bool) : Prog isa := blocks stitch Gcm.X86_64.Stitch.enc (ctrCall ctr) (ghCall gh)

/-- `vg_aes_gcm_decrypt_blocks`. -/
def decrypt (stitch : Bool) : Prog isa := blocks stitch Gcm.X86_64.Stitch.dec (ghCall gh) (ctrCall ctr)

end VG.Impl.AesGcm.X86_64.Blocks
