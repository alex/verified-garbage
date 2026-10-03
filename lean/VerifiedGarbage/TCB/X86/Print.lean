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

def XReg.name : XReg → String
  | .xmm0 => "xmm0" | .xmm1 => "xmm1" | .xmm2 => "xmm2" | .xmm3 => "xmm3"
  | .xmm4 => "xmm4" | .xmm5 => "xmm5" | .xmm6 => "xmm6" | .xmm7 => "xmm7"

def MemOp.str128 (m : MemOp) : String := s!"XMMWORD PTR {m.addr}"

def XBinOp.name : XBinOp → String
  | .movdqa => "movdqa" | .paddd => "paddd" | .pxor => "pxor" | .por => "por"
  | .pand => "pand" | .pandn => "pandn"
  | .punpckldq => "punpckldq" | .punpckhdq => "punpckhdq"
  | .punpcklqdq => "punpcklqdq" | .punpckhqdq => "punpckhqdq"
  | .pshufb => "pshufb" | .sha256msg1 => "sha256msg1" | .sha256msg2 => "sha256msg2"
  | .aesenc => "aesenc" | .aesenclast => "aesenclast"

def XShiftOp.name : XShiftOp → String
  | .pslld => "pslld" | .psrld => "psrld" | .psllq => "psllq" | .psrlq => "psrlq"
  | .pslldq => "pslldq" | .psrldq => "psrldq"

def XOp.asm : XOp → String
  | .bin op d r => s!"{op.name} {d.name}, {r.name}"
  | .shift op d n => s!"{op.name} {d.name}, {n.toNat}"
  | .pshufd d r o => s!"pshufd {d.name}, {r.name}, {o.toNat}"
  | .palignr d r n => s!"palignr {d.name}, {r.name}, {n.toNat}"
  | .sha256rnds2 d r => s!"sha256rnds2 {d.name}, {r.name}, xmm0"
  | .movd d r => s!"movd {d.name}, {r.name}"
  | .aeskeygenassist d r n => s!"aeskeygenassist {d.name}, {r.name}, {n.toNat}"
  | .pclmulqdq d r n => s!"pclmulqdq {d.name}, {r.name}, {n.toNat}"

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
  | .mul r => [s!"mul {r.name}"]
  | .movdquLoad d m => [s!"movdqu {d.name}, {m.str128}"]
  | .movdquStore m r => [s!"movdqu {m.str128}, {r.name}"]
  | .xop op => [op.asm]

def Cond.name : Cond → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := [s!"j{c.name} {l}"]
  jump l := s!"jmp {l}"
  ret := ["ret"]
  call := "call"
  /- Every function starts on a 64-byte boundary, a cache line: the unit
  AMD's op cache builds its entries from (Zen 4 Software Optimization Guide,
  57647, §2.9.1), and one of the 16- and 32-byte windows Intel's decoders and
  decoded ICache work in. So where a function's code, and its loops, lie
  relative to them is fixed by the function alone: a change to other code
  cannot move them, and with them its performance. -/
  funcAlign := [".p2align 6"]

end VG.X86
