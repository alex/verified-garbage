import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.TCB.Axioms

/-! Golden tests for contiguous stack buffers and SP-relative addresses. -/
namespace VG.Test.AArch64Stack
open AArch64

private def initial : State where
  gpr _ := 42
  sp := 0x1000
  c := true
  mem _ := 0xa5
  rd := [⟨0x8000, 32⟩]
  wr := [⟨0x9000, 64⟩]

private def reserved := push (.alloc 256) initial

-- Allocation leaves registers, flags and memory unchanged; the whole buffer
-- is one writable region so it can be passed to an existing verified callee.
#guard (reserved.map fun s =>
  (s.sp, s.wr, s.gpr .x0, s.c, s.mem 0xf00)) ==
    some (0xf00, [⟨0xf00, 256⟩, ⟨0x9000, 64⟩], 42, true, 0xa5)
#guard (reserved.bind fun s => s.store 0xf00 64 0).isSome
#guard (reserved.bind fun s => s.store 0xff8 16 0).isNone
#guard (reserved.bind fun s => s.store 0xef8 8 0).isNone

#guard (reserved.bind fun s => (pop (.free 256) s s).map fun t =>
  (t.sp, t.wr, t.rd, t.gpr .x0, t.c)) ==
    some (0x1000, initial.wr, initial.rd, 42, true)
#guard (reserved.bind fun s => pop (.free 128) s s).isNone
#guard (reserved.bind fun s => pop (.free 256) s { s with sp := s.sp + 16 }).isNone
#guard (reserved.bind fun s => pop (.free 256) s { s with wr := s.wr.tail }).isNone
#guard (pop (.free 256) initial initial).isNone

-- Immediate encoding, alignment, positivity and no-underflow restrictions.
#guard (push (.alloc 0) initial).isNone
#guard (push (.alloc 24) initial).isNone
#guard (push (.alloc 4096) initial).isNone
#guard (push (.alloc 256) { initial with sp := 128 }).isNone
#guard (push (.alloc 4080) initial).isSome
#guard (exec (.alloc 256) initial).isNone
#guard (exec (.free 256) initial).isNone

#guard ((exec (.addSp .x3 192) initial).map fun s =>
  (s.gpr .x3, s.sp, s.c)) == some (0x10c0, 0x1000, true)
#guard ((exec (.addSp .x3 4095) initial).map fun s => s.gpr .x3) == some 0x1fff
#guard (exec (.addSp .x3 4096) initial).isNone
#guard ((exec (.addSp .x3 16) { initial with sp := 0xfffffffffffffff0 }).map
  fun s => s.gpr .x3) == some 0

#guard Instr.asm (.alloc 256) == ["sub sp, sp, #256"]
#guard Instr.asm (.free 256) == ["add sp, sp, #256"]
#guard Instr.asm (.addSp .x3 192) == ["add x3, sp, #192"]

#guard ([Instr.alloc 256, .free 256, .addSp .x3 192].all (·.requires.isEmpty))
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs []) (.addSp .x3 192)).map
  (fun τ => AArch64.Taint.pub τ .x3)) == some true
#guard (AArch64.Taint.push (AArch64.Taint.ofRegs [.x0]) (.alloc 256)).isSome
#guard ((AArch64.Taint.pop (AArch64.Taint.ofRegs [.x0]) (.free 256)).map
  (fun τ => AArch64.Taint.pub τ .x0)) == some true

-- The old frame-depth bound would wrongly report 32 bytes here.
#guard (Code.frame (Instr.push .x30)
  (.frame (.alloc 256) (.block []) (.free 256)) (.pop .x30)).aarch64Depth == 17

#assert_standard_axioms VG.AArch64.Exec.frameSp
#assert_standard_axioms VG.AArch64.WP.alloc
#assert_standard_axioms VG.AArch64.taint
end VG.Test.AArch64Stack
