import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Axioms

/-! Golden tests for stack buffer frames (`alloc`/`free`) on x86-64. -/
namespace VG.Test.X86_64Stack
open X86_64

private def initial : State where
  gpr r := if r = .rsp then 0x1000 else 42
  cf := some true
  zf := some false
  sf := none
  of := some false
  mem _ := 0xa5
  rd := [⟨0x8000, 32⟩]
  wr := [⟨0x9000, 64⟩]

private def reserved := push (.alloc 256) initial

-- Allocation moves only `rsp`, leaves the flags and memory unchanged, and
-- makes the whole buffer one writable region.
#guard (reserved.map fun s =>
  (s.gpr .rsp, s.wr, s.rd, s.gpr .rax, s.cf, s.zf, s.sf, s.of, s.mem 0xf00)) ==
    some (0xf00, [⟨0xf00, 256⟩, ⟨0x9000, 64⟩], initial.rd, 42, some true, some false, none,
      some false, 0xa5)
#guard (reserved.bind fun s => s.store64 0xf00 0).isSome
#guard (reserved.bind fun s => s.store64 0xff8 0).isSome
#guard (reserved.bind fun s => s.store64 0xffc 0).isNone
#guard (reserved.bind fun s => s.store64 0xef8 0).isNone

-- Release requires the frame's size, `rsp` and the writable regions the
-- allocation left; it restores `rsp` and removes the region.
#guard (reserved.bind fun s => (pop (.free 256) s s).map fun t =>
  (t.gpr .rsp, t.wr, t.rd, t.gpr .rax, t.cf, t.mem 0xf00)) ==
    some (0x1000, initial.wr, initial.rd, 42, some true, 0xa5)
#guard (reserved.bind fun s => pop (.free 128) s s).isNone
#guard (reserved.bind fun s => pop (.free 256) s (s.setReg .rsp (s.gpr .rsp + 8))).isNone
#guard (reserved.bind fun s => pop (.free 256) s { s with wr := s.wr.tail }).isNone
#guard (pop (.free 256) initial initial).isNone
-- The pop of a frame of registers releases a buffer frame of its size too.
#guard (reserved.bind fun s => (pop (.pop .rcx 32) s s).map fun t => (t.gpr .rsp, t.wr)) ==
    some (0x1000, initial.wr)

-- Size: positive, a multiple of 8, less than 4096; no wrapping.
#guard (push (.alloc 0) initial).isNone
#guard (push (.alloc 12) initial).isNone
#guard (push (.alloc 4096) initial).isNone
#guard (push (.alloc 4088) initial).isSome
#guard (push (.alloc 256) (initial.setReg .rsp 128)).isNone
#guard (push (.alloc 128) (initial.setReg .rsp 128)).isSome
#guard (exec (.alloc 256) initial).isNone
#guard (exec (.free 256) initial).isNone
#guard addrs (.alloc 256) initial == []
#guard addrs (.free 256) initial == []

#guard Instr.asm (.alloc 256) == ["lea rsp, [rsp-256]"]
#guard Instr.asm (.free 256) == ["lea rsp, [rsp+256]"]
#guard ([Instr.alloc 256, .free 256].all (·.requires.isEmpty))
#guard isa.writesSp (.alloc 256) == false
#guard isa.writesSp (.free 256) == false

end VG.Test.X86_64Stack
