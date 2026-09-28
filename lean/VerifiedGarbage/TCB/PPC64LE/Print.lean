import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.TCB.Print

/-!
# Printer for the 64-bit little-endian PowerPC model

**Trusted.** Emits the GNU/LLVM assembler syntax used by Rust's
`asm!`/`naked_asm!` on PowerPC, with registers written `%rN` (and `%cr0`)
so that they cannot be read as numbers. The rotates and shifts are printed
as the base instructions (`rlwinm`, `rldicl`, `rldicr`) whose operands the
model's semantics describes, not as extended mnemonics.
-/

namespace VG.PPC64LE

def Reg.index : Reg → Nat
  | .r0 => 0 | .r2 => 2 | .r3 => 3 | .r4 => 4 | .r5 => 5 | .r6 => 6 | .r7 => 7 | .r8 => 8
  | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r14 => 14 | .r15 => 15 | .r16 => 16
  | .r17 => 17 | .r18 => 18 | .r19 => 19 | .r20 => 20 | .r21 => 21 | .r22 => 22 | .r23 => 23
  | .r24 => 24 | .r25 => 25 | .r26 => 26 | .r27 => 27 | .r28 => 28 | .r29 => 29 | .r30 => 30
  | .r31 => 31

/-- `%r<n>`. -/
def Reg.name (r : Reg) : String := s!"%r{r.index}"

def LogicOp.name : LogicOp → String
  | .and => "and" | .or => "or" | .xor => "xor"

/-- A 16-bit immediate, as an unsigned number. -/
def imm16 (v : BitVec 16) : String := toString v.toNat

def Instr.asm : Instr → List String
  | .add d n m => [s!"add {d.name}, {n.name}, {m.name}"]
  | .sub d n m => [s!"subf {d.name}, {m.name}, {n.name}"]
  | .addi d n imm => [s!"addi {d.name}, {n.name}, {imm}"]
  | .subi d n imm => [s!"addi {d.name}, {n.name}, -{imm}"]
  | .li d imm => [s!"li {d.name}, {imm}"]
  -- `lis` takes a signed immediate: print the 16 bits as one.
  | .lis d imm => [s!"lis {d.name}, {imm.toInt}"]
  | .ori d n imm => [s!"ori {d.name}, {n.name}, {imm16 imm}"]
  | .oris d n imm => [s!"oris {d.name}, {n.name}, {imm16 imm}"]
  | .logic op d n m => [s!"{op.name} {d.name}, {n.name}, {m.name}"]
  | .rotr .w d n sh => [s!"rlwinm {d.name}, {n.name}, {(32 - sh) % 32}, 0, 31"]
  | .rotr .d d n sh => [s!"rldicl {d.name}, {n.name}, {(64 - sh) % 64}, 0"]
  | .lsr .w d n sh => [s!"rlwinm {d.name}, {n.name}, {(32 - sh) % 32}, {sh}, 31"]
  | .lsr .d d n sh => [s!"rldicl {d.name}, {n.name}, {(64 - sh) % 64}, {sh}"]
  | .lsl d n sh => [s!"rldicr {d.name}, {n.name}, {sh}, {63 - sh}"]
  | .load .w t n off => [s!"lwz {t.name}, {off}({n.name})"]
  | .load .d t n off => [s!"ld {t.name}, {off}({n.name})"]
  | .store .w t n off => [s!"stw {t.name}, {off}({n.name})"]
  | .store .d t n off => [s!"std {t.name}, {off}({n.name})"]
  | .lbz t n off => [s!"lbz {t.name}, {off}({n.name})"]
  | .stb t n off => [s!"stb {t.name}, {off}({n.name})"]
  | .loadRev .w t a b => [s!"lwbrx {t.name}, {a.name}, {b.name}"]
  | .loadRev .d t a b => [s!"ldbrx {t.name}, {a.name}, {b.name}"]
  | .storeRev .w t a b => [s!"stwbrx {t.name}, {a.name}, {b.name}"]
  | .storeRev .d t a b => [s!"stdbrx {t.name}, {a.name}, {b.name}"]
  | .mflr d => [s!"mflr {d.name}"]
  | .mtlr r => [s!"mtlr {r.name}"]
  | .push r => ["stdu %r1, -48(%r1)", s!"std {r.name}, 32(%r1)"]
  | .pop r => [s!"ld {r.name}, 32(%r1)", "addi %r1, %r1, 48"]

/-- The comparison with zero of a condition. -/
def Cond.cmp : Cond → String
  | .zero .w r | .nonzero .w r => s!"cmplwi %cr0, {r.name}, 0"
  | .zero .d r | .nonzero .d r => s!"cmpldi %cr0, {r.name}, 0"

def Cond.branch : Cond → String
  | .zero .. => "beq"
  | .nonzero .. => "bne"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := [c.cmp, s!"{c.branch} %cr0, {l}"]
  jump l := s!"b {l}"
  ret := ["blr"]
  call := "bl"

end VG.PPC64LE
