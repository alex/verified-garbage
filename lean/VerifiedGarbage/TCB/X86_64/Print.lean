import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.Print

/-!
# Intel-syntax printer for the x86-64 model

**Trusted.** Emits Intel syntax without register prefixes, which is the
default dialect of Rust's `asm!`/`naked_asm!` on x86-64.
-/

namespace VG.X86_64

def Reg.name : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The 32-bit name of a register (its low 32 bits). -/
def Reg.name32 : Reg → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | .r8 => "r8d" | .r9 => "r9d" | .r10 => "r10d" | .r11 => "r11d"
  | .r12 => "r12d" | .r13 => "r13d" | .r14 => "r14d" | .r15 => "r15d"

/-- The 8-bit name of a register (its low byte). -/
def Reg.name8 : Reg → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl"
  | .rsp => "spl" | .rbp => "bpl" | .rsi => "sil" | .rdi => "dil"
  | .r8 => "r8b" | .r9 => "r9b" | .r10 => "r10b" | .r11 => "r11b"
  | .r12 => "r12b" | .r13 => "r13b" | .r14 => "r14b" | .r15 => "r15b"

/-- `[base+index*scale+disp]` -/
def MemOp.addr (m : MemOp) : String :=
  let idx := match m.index with
    | none => ""
    | some i => s!"+{i.name}*{m.scale}"
  let d := if m.disp = 0 then "" else if m.disp > 0 then s!"+{m.disp}" else s!"{m.disp}"
  s!"[{m.base.name}{idx}{d}]"

def MemOp.str (m : MemOp) : String := s!"QWORD PTR {m.addr}"

def MemOp.str32 (m : MemOp) : String := s!"DWORD PTR {m.addr}"

def MemOp.str8 (m : MemOp) : String := s!"BYTE PTR {m.addr}"

def MemOp.str128 (m : MemOp) : String := s!"XMMWORD PTR {m.addr}"

def XReg.name : XReg → String
  | .xmm0 => "xmm0" | .xmm1 => "xmm1" | .xmm2 => "xmm2" | .xmm3 => "xmm3"
  | .xmm4 => "xmm4" | .xmm5 => "xmm5" | .xmm6 => "xmm6" | .xmm7 => "xmm7"
  | .xmm8 => "xmm8" | .xmm9 => "xmm9" | .xmm10 => "xmm10" | .xmm11 => "xmm11"
  | .xmm12 => "xmm12" | .xmm13 => "xmm13" | .xmm14 => "xmm14" | .xmm15 => "xmm15"

/-- The name of the AVX register whose low 128 bits are `r`. -/
def XReg.yname (r : XReg) : String := "y" ++ (r.name.drop 1).toString

/-- A vector register's name at a VEX vector length. -/
def XReg.vname (r : XReg) : VLen → String
  | .l128 => r.name
  | .l256 => r.yname

def MemOp.str256 (m : MemOp) : String := s!"YMMWORD PTR {m.addr}"

/-- A memory operand of a VEX vector length. -/
def MemOp.strV (m : MemOp) : VLen → String
  | .l128 => m.str128
  | .l256 => m.str256

def XBinOp.name : XBinOp → String
  | .movdqa => "movdqa" | .paddd => "paddd" | .pxor => "pxor" | .por => "por"
  | .punpckldq => "punpckldq" | .punpckhdq => "punpckhdq"
  | .punpcklqdq => "punpcklqdq" | .punpckhqdq => "punpckhqdq"
  | .pshufb => "pshufb" | .sha256msg1 => "sha256msg1" | .sha256msg2 => "sha256msg2"
  | .pand => "pand" | .pandn => "pandn" | .paddq => "paddq" | .pmuludq => "pmuludq"
  | .aesenc => "aesenc" | .aesenclast => "aesenclast" | .aesdec => "aesdec"
  | .aesdeclast => "aesdeclast" | .aesimc => "aesimc"

def XShiftOp.name : XShiftOp → String
  | .pslld => "pslld" | .psrld => "psrld" | .psllq => "psllq" | .psrlq => "psrlq"
  | .pslldq => "pslldq" | .psrldq => "psrldq"

def XOp.asm : XOp → String
  | .bin op d r => s!"{op.name} {d.name}, {r.name}"
  | .shift op d n => s!"{op.name} {d.name}, {n.toNat}"
  | .pshufd d r o => s!"pshufd {d.name}, {r.name}, {o.toNat}"
  | .palignr d r n => s!"palignr {d.name}, {r.name}, {n.toNat}"
  | .sha256rnds2 d r => s!"sha256rnds2 {d.name}, {r.name}, xmm0"
  | .movq d r => s!"movq {d.name}, {r.name}"
  | .aeskeygenassist d r n => s!"aeskeygenassist {d.name}, {r.name}, {n.toNat}"
  | .pclmulqdq d r n => s!"pclmulqdq {d.name}, {r.name}, {n.toNat}"

def VBinOp.name : VBinOp → String
  | .vpaddd => "vpaddd" | .vpaddq => "vpaddq" | .vpxor => "vpxor" | .vpor => "vpor"
  | .vpand => "vpand" | .vpandn => "vpandn" | .vpshufb => "vpshufb" | .vpmuludq => "vpmuludq"
  | .vpunpckldq => "vpunpckldq" | .vpunpckhdq => "vpunpckhdq"
  | .vpunpcklqdq => "vpunpcklqdq" | .vpunpckhqdq => "vpunpckhqdq"

def VVarOp.name : VVarOp → String
  | .vpsllvd => "vpsllvd" | .vpsrlvd => "vpsrlvd" | .vpsllvq => "vpsllvq" | .vpsrlvq => "vpsrlvq"

def VOp.asm : VOp → String
  | .vbin op l d a b => s!"{op.name} {d.vname l}, {a.vname l}, {b.vname l}"
  | .vmovdqa l d r => s!"vmovdqa {d.vname l}, {r.vname l}"
  | .vshift op l d r n => s!"v{op.name} {d.vname l}, {r.vname l}, {n.toNat}"
  | .vpshufd l d r o => s!"vpshufd {d.vname l}, {r.vname l}, {o.toNat}"
  | .vpalignr l d a b n => s!"vpalignr {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vpblendd l d a b n => s!"vpblendd {d.vname l}, {a.vname l}, {b.vname l}, {n.toNat}"
  | .vvar op l d a b => s!"{op.name} {d.vname l}, {a.vname l}, {b.vname l}"
  | .vpbroadcastd l d r => s!"vpbroadcastd {d.vname l}, {r.name}"
  | .vpbroadcastq l d r => s!"vpbroadcastq {d.vname l}, {r.name}"
  | .vpermq d r o => s!"vpermq {d.yname}, {r.yname}, {o.toNat}"
  | .vperm2i128 d a b n => s!"vperm2i128 {d.yname}, {a.yname}, {b.yname}, {n.toNat}"
  | .vinserti128 d a b n => s!"vinserti128 {d.yname}, {a.yname}, {b.name}, {n.toNat}"
  | .vextracti128 d r n => s!"vextracti128 {d.name}, {r.yname}, {n.toNat}"
  | .vmovq d r => s!"vmovq {d.name}, {r.name}"
  | .vzeroupper => "vzeroupper"

def Src.str : Src → String
  | .reg r => r.name
  | .imm v => toString v.toInt
  | .mem m => m.str

/-- A 32-bit source operand. -/
def Src.str32 : Src → String
  | .reg r => r.name32
  | .imm v => toString v.toInt
  | .mem m => m.str32

def AluOp.name : AluOp → String
  | .add => "add" | .adc => "adc" | .sub => "sub" | .sbb => "sbb" | .and => "and"
  | .or => "or" | .xor => "xor" | .cmp => "cmp" | .test => "test"

def ShiftOp.name : ShiftOp → String
  | .ror => "ror" | .shr => "shr"

def Instr.asm : Instr → List String
  | .mov d s => [s!"mov {d.name}, {s.str}"]
  | .store m r => [s!"mov {m.str}, {r.name}"]
  | .alu op d s => [s!"{op.name} {d.name}, {s.str}"]
  | .mov32 d s => [s!"mov {d.name32}, {s.str32}"]
  | .store32 m r => [s!"mov {m.str32}, {r.name32}"]
  | .alu32 op d s => [s!"{op.name} {d.name32}, {s.str32}"]
  | .shift32 op d n => [s!"{op.name} {d.name32}, {n}"]
  | .bswap32 d => [s!"bswap {d.name32}"]
  | .movzx8 d m => [s!"movzx {d.name32}, {m.str8}"]
  | .store8 m r => [s!"mov {m.str8}, {r.name8}"]
  | .bswap d => [s!"bswap {d.name}"]
  | .shift op d n => [s!"{op.name} {d.name}, {n}"]
  -- `movabs` always selects the `REX.W + B8+rd io` encoding, whatever the value.
  | .movImm64 d v => [s!"movabs {d.name}, {v.toInt}"]
  | .movdquLoad d m => [s!"movdqu {d.name}, {m.str128}"]
  | .movdquStore m r => [s!"movdqu {m.str128}, {r.name}"]
  | .xop op => [op.asm]
  | .vop op => [op.asm]
  | .vmovdquLoad l d m => [s!"vmovdqu {d.vname l}, {m.strV l}"]
  | .vmovdquStore l m r => [s!"vmovdqu {m.strV l}, {r.vname l}"]
  | .vbroadcasti128 d m => [s!"vbroadcasti128 {d.yname}, {m.str128}"]
  | .stmxcsr m => [s!"stmxcsr {m.str32}"]
  | .ldmxcsr m => [s!"ldmxcsr {m.str32}"]
  | .lfence => ["lfence"]

def Cond.name : Cond → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := s!"j{c.name} {l}"
  jump l := s!"jmp {l}"
  ret := ["ret"]
  call := "call"

end VG.X86_64
