import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.TCB.Print

/-!
# Printer for the AArch64 model

**Trusted.** Emits the GNU/LLVM assembler syntax used by Rust's
`asm!`/`naked_asm!` on AArch64.
-/

namespace VG.AArch64

def Reg.index : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11 | .x12 => 12 | .x13 => 13 | .x14 => 14
  | .x15 => 15 | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19 | .x20 => 20 | .x21 => 21
  | .x22 => 22 | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27 | .x28 => 28
  | .x29 => 29 | .x30 => 30

/-- `w<n>` or `x<n>`. -/
def Reg.name (sz : Size) (r : Reg) : String :=
  match sz with
  | .w => s!"w{r.index}"
  | .x => s!"x{r.index}"

def LogicOp.name : LogicOp → String
  | .and => "and" | .orr => "orr" | .eor => "eor"

def Instr.asm : Instr → List String
  | .add sz d n m => [s!"add {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sub sz d n m => [s!"sub {d.name sz}, {n.name sz}, {m.name sz}"]
  | .addImm sz d n imm => [s!"add {d.name sz}, {n.name sz}, #{imm}"]
  | .subImm sz d n imm => [s!"sub {d.name sz}, {n.name sz}, #{imm}"]
  | .logic op sz d n m => [s!"{op.name} {d.name sz}, {n.name sz}, {m.name sz}"]
  | .ror sz d n sh => [s!"ror {d.name sz}, {n.name sz}, #{sh}"]
  | .lsr sz d n sh => [s!"lsr {d.name sz}, {n.name sz}, #{sh}"]
  | .rev32 d n => [s!"rev {d.name .w}, {n.name .w}"]
  | .rev d n => [s!"rev {d.name .x}, {n.name .x}"]
  | .movz sz d imm hw => [s!"movz {d.name sz}, #{imm.toNat}, lsl #{16 * hw}"]
  | .movk sz d imm hw => [s!"movk {d.name sz}, #{imm.toNat}, lsl #{16 * hw}"]
  | .ldr sz t n off => [s!"ldr {t.name sz}, [{n.name .x}, #{off}]"]
  | .str sz t n off => [s!"str {t.name sz}, [{n.name .x}, #{off}]"]
  | .ldrb t n off => [s!"ldrb {t.name .w}, [{n.name .x}, #{off}]"]
  | .strb t n off => [s!"strb {t.name .w}, [{n.name .x}, #{off}]"]

def printer : Printer isa where
  instr := Instr.asm
  branch c l := match c with
    | .zero sz r => s!"cbz {r.name sz}, {l}"
    | .nonzero sz r => s!"cbnz {r.name sz}, {l}"
  jump l := s!"b {l}"
  ret := ["ret"]

end VG.AArch64
