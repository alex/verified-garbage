import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.TCB.Print

/-!
# Printer for the ARMv7 model

**Trusted.** Emits the unified assembler language (UAL) accepted by Rust's
`asm!`/`naked_asm!` on 32-bit ARM, valid for both the ARM and the Thumb
instruction sets.
-/

namespace VG.Arm

def Reg.name : Reg → String
  | .r0 => "r0" | .r1 => "r1" | .r2 => "r2" | .r3 => "r3" | .r4 => "r4" | .r5 => "r5"
  | .r6 => "r6" | .r7 => "r7" | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .lr => "lr"

def Shift.name : Shift → String
  | .lsl => "lsl" | .lsr => "lsr" | .ror => "ror"

def Op2.str : Op2 → String
  | .imm v => s!"#{v.toNat}"
  | .reg r => r.name
  | .shifted r sh n => s!"{r.name}, {sh.name} #{n}"

def DpOp.name : DpOp → String
  | .add => "add" | .sub => "sub" | .and => "and" | .orr => "orr" | .eor => "eor"

def Instr.asm : Instr → List String
  | .mov d (.shifted m sh n) => [s!"{sh.name} {d.name}, {m.name}, #{n}"]
  | .mov d op2 => [s!"mov {d.name}, {op2.str}"]
  | .dp op d n op2 => [s!"{op.name} {d.name}, {n.name}, {op2.str}"]
  | .adds d n op2 => [s!"adds {d.name}, {n.name}, {op2.str}"]
  | .adc d n op2 => [s!"adc {d.name}, {n.name}, {op2.str}"]
  | .subs d n op2 => [s!"subs {d.name}, {n.name}, {op2.str}"]
  | .cmp n op2 => [s!"cmp {n.name}, {op2.str}"]
  | .movw d imm => [s!"movw {d.name}, #{imm.toNat}"]
  | .movt d imm => [s!"movt {d.name}, #{imm.toNat}"]
  | .rev d m => [s!"rev {d.name}, {m.name}"]
  | .mul d n m => [s!"mul {d.name}, {n.name}, {m.name}"]
  | .ldr t n off => [s!"ldr {t.name}, [{n.name}, #{off}]"]
  | .str t n off => [s!"str {t.name}, [{n.name}, #{off}]"]
  | .ldrb t n off => [s!"ldrb {t.name}, [{n.name}, #{off}]"]
  | .strb t n off => [s!"strb {t.name}, [{n.name}, #{off}]"]
  | .addSp d imm => [s!"add {d.name}, sp, #{imm}"]
  | .alloc bytes => [s!"sub sp, sp, #{bytes}"]
  | .free bytes => [s!"add sp, sp, #{bytes}"]
  | .ldrSp t off => [s!"ldr {t.name}, [sp, #{off}]"]
  | .push rs => [s!"push \{{", ".intercalate (rs.map Reg.name)}}"]
  | .pop t n => [s!"ldr {t.name}, [sp], #{n}"]

def Cond.name : Cond → String
  | .eq => "eq" | .ne => "ne"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := [s!"b{c.name} {l}"]
  jump l := s!"b {l}"
  ret := ["bx lr"]
  call := "bl"

end VG.Arm
