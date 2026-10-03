import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.TCB.Axioms

/-! ARMv7/Thumb-2 stack-buffer semantics and instruction encodings. -/
namespace VG.Test.ArmStack
open Arm

private def initial : State where
  gpr _ := 42
  sp := 0x1000
  n := true
  z := false
  c := true
  v := false
  mem _ := 0xa5
  rd := [⟨0x8000, 32⟩]
  wr := [⟨0x9000, 64⟩]

private def reserved := push (.alloc 224) initial

#guard (reserved.map fun s =>
  (s.sp, s.wr, s.gpr .r0, s.n, s.z, s.c, s.v, s.mem 0xf20)) ==
    some (0xf20, [⟨0xf20, 224⟩, ⟨0x9000, 64⟩], 42, true, false, true, false, 0xa5)
#guard (reserved.map fun s => decide (InRegions s.wr 0xf20 64)) == some true
#guard (reserved.bind fun s => s.store32 0xffc 0).isSome
#guard (reserved.bind fun s => s.store32 0xffd 0).isNone
#guard (reserved.bind fun s => s.store32 0xf1c 0).isNone

#guard (reserved.bind fun s => (pop (.free 224) s s).map fun t =>
  (t.sp, t.wr, t.rd, t.gpr .r0, t.n, t.z, t.c, t.v)) ==
    some (0x1000, initial.wr, initial.rd, 42, true, false, true, false)
#guard (reserved.bind fun s => pop (.free 216) s s).isNone
#guard (reserved.bind fun s => pop (.free 224) s { s with sp := s.sp + 8 }).isNone
#guard (reserved.bind fun s => pop (.free 224) s { s with wr := s.wr.tail }).isNone
#guard (pop (.free 224) initial initial).isNone
#guard (push (.alloc 0) initial).isNone
#guard (push (.alloc 12) initial).isNone
#guard (push (.alloc 4096) initial).isNone
#guard (push (.alloc 224) { initial with sp := 128 }).isNone
#guard (push (.alloc 248) initial).isSome
-- Sizes up to a page, if A32 encodes them (an 8-bit value rotated by an even
-- amount): 1872 = 0x75 << 4, but not 1864 = 0x1d1 << 3.
#guard (push (.alloc 256) initial).isSome
#guard (push (.alloc 1872) { initial with sp := 0x2000 }).isSome
#guard (push (.alloc 4032) { initial with sp := 0x2000 }).isSome
#guard (push (.alloc 1864) { initial with sp := 0x2000 }).isNone
#guard ((push (.alloc 1872) { initial with sp := 0x2000 }).bind fun s =>
  (pop (.free 1872) s s).map (·.sp)) == some 0x2000
#guard (exec (.alloc 224) initial).isNone
#guard (exec (.free 224) initial).isNone

#guard ((exec (.addSp .r3 192) initial).map fun s =>
  (s.gpr .r3, s.sp, s.n, s.z, s.c, s.v)) == some (0x10c0, 0x1000, true, false, true, false)
#guard ((exec (.addSp .lr 255) initial).map fun s => s.gpr .lr) == some 0x10ff
#guard (exec (.addSp .r3 256) initial).isNone
#guard ((exec (.addSp .r3 16) { initial with sp := 0xfffffff0 }).map
  fun s => s.gpr .r3) == some 0
#guard Instr.asm (.alloc 224) == ["sub sp, sp, #224"]
#guard Instr.asm (.free 224) == ["add sp, sp, #224"]
#guard Instr.asm (.addSp .r3 192) == ["add r3, sp, #192"]

-- The taint domain knows SP is public only when it tracks stack arguments.
private def publicSP : Arm.Taint.T := { regs := .ofList [], flags := false, argLen := 4 }
#guard ((Arm.Taint.step publicSP (.addSp .r3 192)).map (fun τ => Arm.Taint.pub τ .r3)) == some true
#guard ((Arm.Taint.step { publicSP with argLen := 0 } (.addSp .r3 192)).map
  (fun τ => Arm.Taint.pub τ .r3)) == some false

-- Nested buffer frames contribute their full byte sizes to the stack bound.
#guard stackUse (.frame (.alloc 224) (.frame (.alloc 16) (.block []) (.free 16)) (.free 224)) == 240

#assert_standard_axioms VG.Arm.Exec.frameSp
#assert_standard_axioms VG.Arm.WP.alloc
#assert_standard_axioms VG.Arm.Exec.sp
#assert_standard_axioms VG.Arm.Taint.step_sound
end VG.Test.ArmStack
