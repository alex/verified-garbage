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
  | .x15 => 15 | .x16 => 16 | .x17 => 17 | .x19 => 19 | .x20 => 20 | .x21 => 21
  | .x22 => 22 | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27 | .x28 => 28
  | .x30 => 30

/-- `w<n>` or `x<n>`. -/
def Reg.name (sz : Size) (r : Reg) : String :=
  match sz with
  | .w => s!"w{r.index}"
  | .x => s!"x{r.index}"

def VReg.index : VReg → Nat
  | .v0 => 0 | .v1 => 1 | .v2 => 2 | .v3 => 3 | .v4 => 4 | .v5 => 5 | .v6 => 6 | .v7 => 7
  | .v8 => 8 | .v9 => 9 | .v10 => 10 | .v11 => 11 | .v12 => 12 | .v13 => 13 | .v14 => 14
  | .v15 => 15
  | .v16 => 16 | .v17 => 17 | .v18 => 18 | .v19 => 19 | .v20 => 20 | .v21 => 21 | .v22 => 22
  | .v23 => 23 | .v24 => 24 | .v25 => 25 | .v26 => 26 | .v27 => 27 | .v28 => 28 | .v29 => 29
  | .v30 => 30 | .v31 => 31

/-- `v<n>.<t>` -/
def VReg.arr (r : VReg) (t : String) : String := s!"v{r.index}.{t}"

/-- `v<n>.16b` -/
def VReg.b (r : VReg) : String := r.arr "16b"

/-- `q<n>` -/
def VReg.q (r : VReg) : String := s!"q{r.index}"

/-- `s<n>` -/
def VReg.s (r : VReg) : String := s!"s{r.index}"

def VArr.name : VArr → String
  | .s4 => "4s" | .d2 => "2d" | .b16 => "16b"

/-- The element size of an arrangement, in an element operand (`v<n>.<t>[i]`). -/
def VArr.elem : VArr → String
  | .s4 => "s" | .d2 => "d" | .b16 => "b"

def VLogicOp.name : VLogicOp → String
  | .and => "and" | .orr => "orr" | .eor => "eor" | .bic => "bic" | .orn => "orn"

def VShiftOp.name : VShiftOp → String
  | .shl => "shl" | .ushr => "ushr" | .sri => "sri" | .sli => "sli" | .sshr => "sshr"

def VSelOp.name : VSelOp → String
  | .bsl => "bsl" | .bit => "bit" | .bif => "bif"

/-- `{vn.16b, …}`: the `len` registers from `n`. -/
def tableList (n : VReg) (len : Nat) : String :=
  "{" ++ ", ".intercalate ((List.range len).map fun i => (Nat.repeat VReg.succ i n).b) ++ "}"

def VPermOp.name : VPermOp → String
  | .zip1 => "zip1" | .zip2 => "zip2" | .trn1 => "trn1" | .trn2 => "trn2" | .uzp1 => "uzp1"
  | .uzp2 => "uzp2"

def Sha1Op.name : Sha1Op → String
  | .c => "sha1c" | .p => "sha1p" | .m => "sha1m"

def VOp.asm : VOp → String
  | .mov d n => s!"mov {d.b}, {n.b}"
  | .movi0 d => s!"movi {d.arr "2d"}, #0"
  | .dup .s4 d n => s!"dup {d.arr "4s"}, {n.name .w}"
  | .dup .d2 d n => s!"dup {d.arr "2d"}, {n.name .x}"
  | .ins .s4 d i n => s!"mov v{d.index}.s[{i}], {n.name .w}"
  | .ins .d2 d i n => s!"mov v{d.index}.d[{i}], {n.name .x}"
  | .dup .b16 d n => s!"dup {d.b}, {n.name .w}"
  | .ins .b16 d i n => s!"mov v{d.index}.b[{i}], {n.name .w}"
  | .dupS d n i => s!"dup {d.s}, v{n.index}.s[{i}]"
  | .dupE a d n i => s!"dup {d.arr a.name}, v{n.index}.{a.elem}[{i}]"
  | .insE a d i n j => s!"mov v{d.index}.{a.elem}[{i}], v{n.index}.{a.elem}[{j}]"
  | .cmeq a d n m => s!"cmeq {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .bsel op d n m => s!"{op.name} {d.b}, {n.b}, {m.b}"
  | .logic op d n m => s!"{op.name} {d.b}, {n.b}, {m.b}"
  | .not d n => s!"not {d.b}, {n.b}"
  | .add a d n m => s!"add {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .sub a d n m => s!"sub {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .shift op a d n sh => s!"{op.name} {d.arr a.name}, {n.arr a.name}, #{sh}"
  | .ext d n m imm => s!"ext {d.b}, {n.b}, {m.b}, #{imm}"
  | .rev .rev32b d n => s!"rev32 {d.b}, {n.b}"
  | .rev .rev32h d n => s!"rev32 {d.arr "8h"}, {n.arr "8h"}"
  | .rev .rev64b d n => s!"rev64 {d.b}, {n.b}"
  | .rev .rev64s d n => s!"rev64 {d.arr "4s"}, {n.arr "4s"}"
  | .perm op a d n m => s!"{op.name} {d.arr a.name}, {n.arr a.name}, {m.arr a.name}"
  | .tbl d n m => s!"tbl {d.b}, \{{n.b}}, {m.b}"
  | .tblN x len d n m => s!"{if x then "tbx" else "tbl"} {d.b}, {tableList n len}, {m.b}"
  | .umull false d n m => s!"umull {d.arr "2d"}, {n.arr "2s"}, {m.arr "2s"}"
  | .umull true d n m => s!"umull2 {d.arr "2d"}, {n.arr "4s"}, {m.arr "4s"}"
  | .umlal false d n m => s!"umlal {d.arr "2d"}, {n.arr "2s"}, {m.arr "2s"}"
  | .umlal true d n m => s!"umlal2 {d.arr "2d"}, {n.arr "4s"}, {m.arr "4s"}"
  | .mul d n m => s!"mul {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .mla d n m => s!"mla {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .mls d n m => s!"mls {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sqdmulh d n m => s!"sqdmulh {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .umin d n m => s!"umin {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .pmull false d n m => s!"pmull {d.arr "1q"}, {n.arr "1d"}, {m.arr "1d"}"
  | .pmull true d n m => s!"pmull2 {d.arr "1q"}, {n.arr "2d"}, {m.arr "2d"}"
  | .aese d n => s!"aese {d.b}, {n.b}"
  | .aesd d n => s!"aesd {d.b}, {n.b}"
  | .aesmc d n => s!"aesmc {d.b}, {n.b}"
  | .aesimc d n => s!"aesimc {d.b}, {n.b}"
  | .sha1 op d n m => s!"{op.name} {d.q}, {n.s}, {m.arr "4s"}"
  | .sha1h d n => s!"sha1h {d.s}, {n.s}"
  | .sha1su0 d n m => s!"sha1su0 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sha1su1 d n => s!"sha1su1 {d.arr "4s"}, {n.arr "4s"}"
  | .sha256h d n m => s!"sha256h {d.q}, {n.q}, {m.arr "4s"}"
  | .sha256h2 d n m => s!"sha256h2 {d.q}, {n.q}, {m.arr "4s"}"
  | .sha256su0 d n => s!"sha256su0 {d.arr "4s"}, {n.arr "4s"}"
  | .sha256su1 d n m => s!"sha256su1 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"
  | .sha512h d n m => s!"sha512h {d.q}, {n.q}, {m.arr "2d"}"
  | .sha512h2 d n m => s!"sha512h2 {d.q}, {n.q}, {m.arr "2d"}"
  | .sha512su0 d n => s!"sha512su0 {d.arr "2d"}, {n.arr "2d"}"
  | .sha512su1 d n m => s!"sha512su1 {d.arr "2d"}, {n.arr "2d"}, {m.arr "2d"}"
  | .eor3 d n m a => s!"eor3 {d.b}, {n.b}, {m.b}, {a.b}"
  | .bcax d n m a => s!"bcax {d.b}, {n.b}, {m.b}, {a.b}"
  | .rax1 d n m => s!"rax1 {d.arr "2d"}, {n.arr "2d"}, {m.arr "2d"}"
  | .xar d n m imm => s!"xar {d.arr "2d"}, {n.arr "2d"}, {m.arr "2d"}, #{imm}"
  | .xarS d m rot => s!"xar z{d.index}.s, z{d.index}.s, z{m.index}.s, #{rot}"

def LogicOp.name : LogicOp → String
  | .and => "and" | .orr => "orr" | .eor => "eor"

def Instr.asm : Instr → List String
  | .add sz d n m => [s!"add {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sub sz d n m => [s!"sub {d.name sz}, {n.name sz}, {m.name sz}"]
  | .adds sz d n m => [s!"adds {d.name sz}, {n.name sz}, {m.name sz}"]
  | .adcs sz d n m => [s!"adcs {d.name sz}, {n.name sz}, {m.name sz}"]
  | .subs sz d n m => [s!"subs {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sbcs sz d n m => [s!"sbcs {d.name sz}, {n.name sz}, {m.name sz}"]
  | .adc sz d n m => [s!"adc {d.name sz}, {n.name sz}, {m.name sz}"]
  | .sbc sz d n m => [s!"sbc {d.name sz}, {n.name sz}, {m.name sz}"]
  | .addImm sz d n imm => [s!"add {d.name sz}, {n.name sz}, #{imm}"]
  | .subImm sz d n imm => [s!"sub {d.name sz}, {n.name sz}, #{imm}"]
  | .logic op sz d n m => [s!"{op.name} {d.name sz}, {n.name sz}, {m.name sz}"]
  | .logicRor op sz d n m sh =>
    [s!"{op.name} {d.name sz}, {n.name sz}, {m.name sz}, ror #{sh}"]
  | .bicRor sz d n m sh =>
    [s!"bic {d.name sz}, {n.name sz}, {m.name sz}, ror #{sh}"]
  | .ror sz d n sh => [s!"ror {d.name sz}, {n.name sz}, #{sh}"]
  | .extr sz d n m lsb => [s!"extr {d.name sz}, {n.name sz}, {m.name sz}, #{lsb}"]
  | .lsr sz d n sh => [s!"lsr {d.name sz}, {n.name sz}, #{sh}"]
  | .lsl sz d n sh => [s!"lsl {d.name sz}, {n.name sz}, #{sh}"]
  | .madd sz d n m a => [s!"madd {d.name sz}, {n.name sz}, {m.name sz}, {a.name sz}"]
  | .mul sz d n m => [s!"mul {d.name sz}, {n.name sz}, {m.name sz}"]
  | .umulh d n m => [s!"umulh {d.name .x}, {n.name .x}, {m.name .x}"]
  | .rev32 d n => [s!"rev {d.name .w}, {n.name .w}"]
  | .rev d n => [s!"rev {d.name .x}, {n.name .x}"]
  | .movz sz d imm hw => [s!"movz {d.name sz}, #{imm.toNat}, lsl #{16 * hw}"]
  | .movk sz d imm hw => [s!"movk {d.name sz}, #{imm.toNat}, lsl #{16 * hw}"]
  | .ldr sz t n off => [s!"ldr {t.name sz}, [{n.name .x}, #{off}]"]
  | .str sz t n off => [s!"str {t.name sz}, [{n.name .x}, #{off}]"]
  | .ldrb t n off => [s!"ldrb {t.name .w}, [{n.name .x}, #{off}]"]
  | .strb t n off => [s!"strb {t.name .w}, [{n.name .x}, #{off}]"]
  | .push r => [s!"str {r.name .x}, [sp, #-16]!"]
  | .pop r => [s!"ldr {r.name .x}, [sp], #16"]
  | .addSp d imm => [s!"add {d.name .x}, sp, #{imm}"]
  | .alloc bytes => [s!"sub sp, sp, #{bytes}"]
  | .free bytes => [s!"add sp, sp, #{bytes}"]
  | .ldrSp t off => [s!"ldr {t.name .x}, [sp, #{off}]"]
  | .vop op => [op.asm]
  | .ldrq t n off => [s!"ldr {t.q}, [{n.name .x}, #{off}]"]
  | .strq t n off => [s!"str {t.q}, [{n.name .x}, #{off}]"]
  | .umov .w d n i => [s!"umov {d.name .w}, v{n.index}.s[{i}]"]
  | .umov .x d n i => [s!"umov {d.name .x}, v{n.index}.d[{i}]"]

def printer : Printer isa where
  instr := Instr.asm
  branch c l := match c with
    | .zero sz r => s!"cbz {r.name sz}, {l}"
    | .nonzero sz r => s!"cbnz {r.name sz}, {l}"
  jump l := s!"b {l}"
  ret := ["ret"]
  call := "bl"
  -- LLVM's AArch64 assembler rejects, e.g., `aese` unless the `aes` extension
  -- is enabled, and a directive in a naked function stays in effect for the
  -- rest of the module, so each function disables what it enabled.
  enableFeature f := [s!".arch_extension {f}"]
  disableFeature f := [s!".arch_extension no{f}"]

end VG.AArch64
