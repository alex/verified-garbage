import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch

/-!
# AES-GCM on whole blocks: x86-64 implementation

`vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks`
`(ctx = rdi, rounds = rsi, counter = rdx, y = rcx, data = r8, n = r9,
scratch = [rsp + 8])`, generic over the implementations of `vg_aes_ctr32` and
`vg_ghash` they call, as the other functions of AES-GCM.

They load `scratch` into `r11` and push a frame of the arguments (`ctx`,
`rounds`, `counter`, `y`, `data`, `n` and `scratch`, the last at `rsp`). With
`stitch` (VAES and VPCLMULQDQ), the first `16 ⌊n / 16⌋` blocks, if any, are
encrypted and hashed in one pass (`Gcm.X86_64.Stitch`, which keeps the powers
of `H` at `scratch`), and the data and `n` kept become those of the rest. The
rest (all the blocks, without `stitch`) is then encrypted with `vg_aes_ctr32`
and hashed with `vg_ghash` (hashed first when decrypting), each called with
`scratch` as its working space, reloading the arguments from the frame
before each call.
-/

namespace VG.Impl.AesGcm.X86_64.Blocks

open VG.X86_64

/-- Where the frame keeps the arguments, from `rsp`. -/
def argScr : Nat := 0
def argN : Nat := 8
def argData : Nat := 16
def argY : Nat := 24
def argCtr : Nat := 32
def argRounds : Nat := 40
def argCtx : Nat := 48

/-- The registers of the frame, the first pushed first (highest). -/
def frameRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r11]

/-- If there are at least 16 blocks, the first `16 ⌊n / 16⌋` by `piece`. -/
def stitchPart (piece : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r9 (imm 16)])
    (.ite .b (.block [])
      (.seq (.block [.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax)]) piece))

/-- The data and `n` kept become those of the rest: `n mod 16` blocks after
the first `16 ⌊n / 16⌋`. -/
def rest : List Instr :=
  [.mov .r8 (.mem (at_ .rsp argN)), .mov .rax (.reg .r8), .alu .and .r8 (imm 15), .alu .sub .rax (.reg .r8),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.mem (at_ .rsp argData)), .store (at_ .rsp argData) .rax, .store (at_ .rsp argN) .r8]

/-- The arguments of `vg_aes_ctr32` on the rest. -/
def ctrArgs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp argCtx)), .mov .rsi (.mem (at_ .rsp argRounds)), .mov .rdx (.mem (at_ .rsp argCtr)),
    .mov .rcx (.mem (at_ .rsp argData)), .mov .r8 (.mem (at_ .rsp argN)), .mov .r9 (.mem (at_ .rsp argScr))]

/-- The arguments of `vg_ghash` on the rest. -/
def ghArgs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp argCtx)), .alu .add .rdi (imm 240), .mov .rsi (.mem (at_ .rsp argY)),
    .mov .rdx (.mem (at_ .rsp argData)), .mov .rcx (.mem (at_ .rsp argN)), .mov .r8 (.mem (at_ .rsp argScr))]

/-- The rest, if any, with `first` and then `second`. -/
def tail (first second : Prog isa) : Prog isa :=
  .seq (.block [.mov .r8 (.mem (at_ .rsp argN)), .alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq first second))

variable (ctr gh : Fn)

def ctrCall : Prog isa := .seq (.block ctrArgs) (.call ctr.name ctr.code)
def ghCall : Prog isa := .seq (.block ghArgs) (.call gh.name gh.code)

/-- The first blocks by `piece` (with `stitch`), then the rest, in the frame. -/
def blocks (stitch : Bool) (piece : Prog isa) (first second : Prog isa) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (at_ .rsp 8))])
    (.frame (.push frameRegs)
      (.seq (if stitch then .seq (stitchPart piece) (.block rest) else .block []) (tail first second))
      (.pop .rax 7))

/-- `vg_aes_gcm_encrypt_blocks`. -/
def encrypt (stitch : Bool) : Prog isa := blocks stitch Gcm.X86_64.Stitch.enc (ctrCall ctr) (ghCall gh)

/-- `vg_aes_gcm_decrypt_blocks`. -/
def decrypt (stitch : Bool) : Prog isa := blocks stitch Gcm.X86_64.Stitch.dec (ghCall gh) (ctrCall ctr)

end VG.Impl.AesGcm.X86_64.Blocks
