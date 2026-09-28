import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Golden tests for the push and pop of frames

The ISA models are part of the TCB; these tests run the push and pop of a
frame on concrete states, so that what they store, load and permit, and when
they fault, show up in review.
-/

namespace VG.Test.Frames

/-! ## AArch64 -/

def a64 : AArch64.State :=
  { gpr := fun r => if r = .x30 then 0x1122334455667788 else 0, sp := 0x1000,
    mem := fun _ => 0, rd := [], wr := [⟨0x8000, 8⟩] }

def a64push : Option AArch64.State := AArch64.push (.push .x30) a64

-- `x30` is stored at `sp - 16`, which becomes a writable region at the head of `wr`.
#guard (a64push.map fun s => (s.sp, s.mem.read 0xff0 8, s.wr.map (·.base), s.wr.map (·.len))) ==
  some (0xff0, 0x1122334455667788, [0xff0, 0x8000], [16, 8])

-- The pop loads its register from the frame, moves `sp` back and removes the region.
#guard (a64push.bind fun s₁ => (AArch64.pop (.pop .x9) s₁ s₁).map fun s =>
    (s.sp, s.gpr .x9, s.wr.map (·.base))) == some (0x1000, 0x1122334455667788, [0x8000])

-- It faults if the stack pointer or the regions are not those the push left.
#guard (a64push.bind fun s₁ => AArch64.pop (.pop .x9) s₁ { s₁ with sp := s₁.sp + 16 }).isNone
#guard (a64push.bind fun s₁ => AArch64.pop (.pop .x9) s₁ { s₁ with wr := s₁.wr.tail }).isNone
#guard (AArch64.pop (.pop .x9) a64 a64).isNone
-- The push faults if the frame would wrap around the address space.
#guard (AArch64.push (.push .x30) { a64 with sp := 8 }).isNone
-- Neither is an instruction of a block.
#guard (AArch64.exec (.push .x30) a64).isNone && (AArch64.exec (.pop .x30) a64).isNone

/-! ## ARMv7 -/

def arm : Arm.State :=
  { gpr := fun r => if r = .r0 then 0x11111111 else if r = .lr then 0x22222222 else 0,
    sp := 0x1000, n := false, z := false, c := false, v := false,
    mem := fun _ => 0, rd := [], wr := [] }

def armPush : Option Arm.State := Arm.push (.push [.r0, .lr]) arm

-- The lowest-numbered register at the lowest address.
#guard (armPush.map fun s => (s.sp, s.mem.readW 0xff8 32, s.mem.readW 0xffc 32,
    s.wr.map (·.base), s.wr.map (·.len))) ==
  some (0xff8, 0x11111111, 0x22222222, [0xff8], [8])

-- The pop loads the word at `sp` and removes the whole frame.
#guard (armPush.bind fun s₁ => (Arm.pop (.pop .r5 8) s₁ s₁).map fun s =>
    (s.sp, s.gpr .r5, s.wr.length)) == some (0x1000, 0x11111111, 0)

-- It faults unless the frame has the size popped.
#guard (armPush.bind fun s₁ => Arm.pop (.pop .r5 4) s₁ s₁).isNone
-- Register lists must be ascending and not empty.
#guard Arm.regList [.r0, .r4, .lr] && !Arm.regList [.lr, .r0] && !Arm.regList [.r4, .r4] &&
  !Arm.regList []
#guard (Arm.push (.push [.lr, .r0]) arm).isNone
#guard (Arm.push (.push [.r0]) { arm with sp := 2 }).isNone
#guard (Arm.exec (.push [.r0]) arm).isNone && (Arm.exec (.pop .r0 4) arm).isNone

/-! ## x86 -/

def x86 : X86.State :=
  { gpr := fun r => if r = .esp then 0x1000 else if r = .eax then 0xaaaaaaaa
      else if r = .ecx then 0xcccccccc else 0,
    cf := none, zf := none, sf := none, of := none, mem := fun _ => 0, rd := [], wr := [] }

def x86Push : Option X86.State := X86.push (.push [.ecx, .eax]) x86

-- `push ecx; push eax`: `eax` at the lower address.
#guard (x86Push.map fun s => (s.gpr .esp, s.mem.readW 0xff8 32, s.mem.readW 0xffc 32,
    s.wr.map (·.base), s.wr.map (·.len))) ==
  some (0xff8, 0xaaaaaaaa, 0xcccccccc, [0xff8], [8])

-- `pop edx; pop edx`: `edx` holds the last word, and `esp` is back.
#guard (x86Push.bind fun s₁ => (X86.pop (.pop .edx 2) s₁ s₁).map fun s =>
    (s.gpr .esp, s.gpr .edx, s.wr.length)) == some (0x1000, 0xcccccccc, 0)

#guard (x86Push.bind fun s₁ => X86.pop (.pop .edx 1) s₁ s₁).isNone
#guard (x86Push.bind fun s₁ => X86.pop (.pop .esp 2) s₁ s₁).isNone
#guard (X86.push (.push [.esp]) x86).isNone && (X86.push (.push []) x86).isNone
#guard (X86.exec (.push [.eax]) x86).isNone && (X86.exec (.pop .eax 1) x86).isNone

/-! ## x86-64 -/

def x64 : X86_64.State :=
  { gpr := fun r => if r = .rsp then 0x1000 else if r = .rax then 0xaaaaaaaaaaaaaaaa
      else if r = .rcx then 0xcccccccccccccccc else 0,
    cf := none, zf := none, sf := none, of := none, mem := fun _ => 0, rd := [], wr := [⟨0x8000, 8⟩] }

def x64Push : Option X86_64.State := X86_64.push (.push [.rcx, .rax]) x64

-- `push rcx; push rax`: `rax` at the lower address; the 16 bytes become a
-- writable region at the head of `wr`.
#guard (x64Push.map fun s => (s.gpr .rsp, s.mem.readW 0xff0 64, s.mem.readW 0xff8 64,
    s.wr.map (·.base), s.wr.map (·.len))) ==
  some (0xff0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, [0xff0, 0x8000], [16, 8])

-- `pop rdx; pop rdx`: `rdx` holds the last quadword, `rsp` is back and the
-- frame's region is removed.
#guard (x64Push.bind fun s₁ => (X86_64.pop (.pop .rdx 2) s₁ s₁).map fun s =>
    (s.gpr .rsp, s.gpr .rdx, s.wr.map (·.base))) == some (0x1000, 0xcccccccccccccccc, [0x8000])

-- The pop faults unless the frame has the size popped, `rsp` and the regions
-- are those the push left, and its register is not `rsp`.
#guard (x64Push.bind fun s₁ => X86_64.pop (.pop .rdx 1) s₁ s₁).isNone
#guard (x64Push.bind fun s₁ => X86_64.pop (.pop .rdx 2) s₁ (s₁.setReg .rsp (s₁.gpr .rsp + 16))).isNone
#guard (x64Push.bind fun s₁ => X86_64.pop (.pop .rdx 2) s₁ { s₁ with wr := s₁.wr.tail }).isNone
#guard (x64Push.bind fun s₁ => X86_64.pop (.pop .rsp 2) s₁ s₁).isNone
#guard (X86_64.pop (.pop .rdx 1) x64 x64).isNone
-- The push faults on an empty list, on `rsp`, and if the frame would wrap
-- around the address space.
#guard (X86_64.push (.push [.rsp]) x64).isNone && (X86_64.push (.push []) x64).isNone
#guard (X86_64.push (.push [.rcx, .rax]) (x64.setReg .rsp 8)).isNone
-- Neither is an instruction of a block.
#guard (X86_64.exec (.push [.rax]) x64).isNone && (X86_64.exec (.pop .rax 1) x64).isNone

-- Passing two arguments on the stack: pushed the last first, just before the
-- call, they are the callee's first two stack arguments at `[rsp + 8]` and
-- `[rsp + 16]` on entry, above the return address, in the region the frame
-- made readable, which is the callee's argument area.
def x64Entry : Option X86_64.State := x64Push.bind X86_64.call

#guard (x64Entry.map fun s => (s.gpr .rsp, X86_64.stackArg s 0, X86_64.stackArg s 1)) ==
  some (0xfe8, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)
#guard (x64Entry.map fun s => (X86_64.abi.argArea (List.replicate 8 64) s).map
    fun (r, w) => (r.base, r.len, w)) == some [(0xff0, 16, false)]
#guard (x64Entry.map fun s => decide (InRegions (s.rd ++ s.wr) (X86_64.stackArgAddr s 0) 16)) ==
  some true

/-! ## PPC64LE -/

def ppc : PPC64LE.State :=
  { gpr := fun r => if r = .r0 then 0x1122334455667788 else 0, lr := 0, sp := 0x1000,
    mem := fun _ => 0, rd := [], wr := [⟨0x8000, 8⟩] }

def ppcPush : Option PPC64LE.State := PPC64LE.push (.push .r0) ppc

-- `stdu r1, -48(r1)` stores the back chain (the old `sp`) at the new `sp`; `std r0, 32(r1)`
-- stores `r0` above the 32-byte header, and the 16 bytes there become a writable region at
-- the head of `wr`.
#guard (ppcPush.map fun s => (s.sp, s.mem.read 0xfd0 8, s.mem.read 0xff0 8, s.mem.read 0xfd8 24,
    s.wr.map (·.base), s.wr.map (·.len))) ==
  some (0xfd0, 0x1000, 0x1122334455667788, 0, [0xff0, 0x8000], [16, 8])

-- The pop loads its register from the frame, moves `sp` back and removes the region.
#guard (ppcPush.bind fun s₁ => (PPC64LE.pop (.pop .r9) s₁ s₁).map fun s =>
    (s.sp, s.gpr .r9, s.wr.map (·.base))) == some (0x1000, 0x1122334455667788, [0x8000])

-- It faults if the stack pointer or the regions are not those the push left.
#guard (ppcPush.bind fun s₁ => PPC64LE.pop (.pop .r9) s₁ { s₁ with sp := s₁.sp + 16 }).isNone
#guard (ppcPush.bind fun s₁ => PPC64LE.pop (.pop .r9) s₁ { s₁ with wr := s₁.wr.tail }).isNone
#guard (PPC64LE.pop (.pop .r9) ppc ppc).isNone
-- The push faults if the frame would wrap around the address space.
#guard (PPC64LE.push (.push .r0) { ppc with sp := 32 }).isNone
-- Neither is an instruction of a block.
#guard (PPC64LE.exec (.push .r0) ppc).isNone && (PPC64LE.exec (.pop .r0) ppc).isNone

end VG.Test.Frames
