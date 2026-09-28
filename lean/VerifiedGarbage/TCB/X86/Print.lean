import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.Print

/-!
# Intel-syntax printer for the x86 (32-bit) model

**Trusted.** Emits Intel syntax without register prefixes, which is the
default dialect of Rust's `asm!`/`naked_asm!` on x86.
-/

namespace VG.X86

def Reg.name : Reg → String
  | .eax => "eax" | .ecx => "ecx" | .edx => "edx" | .ebx => "ebx"
  | .esp => "esp" | .ebp => "ebp" | .esi => "esi" | .edi => "edi"

def Reg8.name : Reg8 → String
  | .al => "al" | .cl => "cl" | .dl => "dl" | .bl => "bl"

/-- `[base+disp]` -/
def MemOp.addr (m : MemOp) : String :=
  let d := if m.disp = 0 then "" else s!"+{m.disp}"
  s!"[{m.base.name}{d}]"

def MemOp.str (m : MemOp) : String := s!"DWORD PTR {m.addr}"

def MemOp.str8 (m : MemOp) : String := s!"BYTE PTR {m.addr}"

def Src.str : Src → String
  | .reg r => r.name
  | .imm v => toString v.toInt
  | .mem m => m.str

def AluOp.name : AluOp → String
  | .add => "add" | .adc => "adc" | .sub => "sub" | .sbb => "sbb" | .and => "and"
  | .or => "or" | .xor => "xor" | .cmp => "cmp" | .test => "test"

def ShiftOp.name : ShiftOp → String
  | .ror => "ror" | .shr => "shr"

def Instr.asm : Instr → List String
  | .mov d s => [s!"mov {d.name}, {s.str}"]
  | .store m r => [s!"mov {m.str}, {r.name}"]
  | .alu op d s => [s!"{op.name} {d.name}, {s.str}"]
  | .shift op d n => [s!"{op.name} {d.name}, {n}"]
  | .bswap d => [s!"bswap {d.name}"]
  | .movzx8 d m => [s!"movzx {d.name}, {m.str8}"]
  | .store8 m r => [s!"mov {m.str8}, {r.name}"]
  | .push rs => rs.map fun r => s!"push {r.name}"
  | .pop r k => List.replicate k s!"pop {r.name}"

def Cond.name : Cond → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := s!"j{c.name} {l}"
  jump l := s!"jmp {l}"
  ret := ["ret"]
  call := "call"

end VG.X86
