import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Golden tests for the PPC64LE instruction semantics

The ISA model is part of the TCB; these tests run each instruction on a
concrete state, so that the values they compute (in particular the word
forms, the byte-reversed accesses and the sign extension of `lis`) and when
they fault show up in review. The expected values were checked against the
same instructions run under QEMU's ppc64le emulation (`qemu-ppc64le`).
-/

namespace VG.Test.PPC64LE

open VG.PPC64LE

/-- `r3` points to 16 readable and writable bytes `0x00, 0x01, …, 0x0f` at
`0x1000`; `r4 = 0x8000_0001_f000_0001`, `r5 = 4`, `r6 = 0xffff_ffff_0123_4567`. -/
def s0 : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x80000001f0000001 | .r5 => 4 | .r6 => 0xffffffff01234567 | _ => 0
  lr := 0x4000
  sp := 0x2000
  mem a := a.setWidth 8
  rd := []
  wr := [⟨0x1000, 16⟩]

/-- `r7` after running `i` (the destination of every test). -/
def reg (i : Instr) : Option (BitVec 64) := (exec i s0).map (·.gpr .r7)

-- 64-bit arithmetic and logic.
#guard reg (.add .r7 .r4 .r6) == some 0x80000000f1234568
#guard reg (.sub .r7 .r5 .r4) == some 0x7ffffffe10000003
#guard reg (.addi .r7 .r6 0x7fff) == some 0xffffffff0123c566
#guard reg (.subi .r7 .r5 5) == some 0xffffffffffffffff
#guard reg (.subi .r7 .r5 32768) == some 0xffffffffffff8004
#guard reg (.li .r7 32767) == some 0x7fff
#guard reg (.lis .r7 0x7fff) == some 0x7fff0000
#guard reg (.lis .r7 0x8000) == some 0xffffffff80000000
#guard reg (.ori .r7 .r5 0xff00) == some 0xff04
#guard reg (.oris .r7 .r5 0xff00) == some 0xff000004
#guard reg (.logic .and .r7 .r4 .r6) == some 0x8000000100000001
#guard reg (.logic .or .r7 .r4 .r5) == some 0x80000001f0000005
#guard reg (.logic .xor .r7 .r4 .r6) == some 0x7ffffffef1234566

-- Word rotates and shifts read the low word and zero-extend the result.
#guard reg (.rotr .w .r7 .r4 4) == some 0x1f000000
#guard reg (.rotr .w .r7 .r6 0) == some 0x01234567
#guard reg (.lsr .w .r7 .r4 28) == some 0xf
#guard reg (.lsr .w .r7 .r6 0) == some 0x01234567
-- Doubleword rotates and shifts.
#guard reg (.rotr .d .r7 .r4 4) == some 0x180000001f000000
#guard reg (.lsr .d .r7 .r4 60) == some 0x8
#guard reg (.lsl .r7 .r6 32) == some 0x0123456700000000
#guard (reg (.rotr .w .r7 .r4 32)).isNone && (reg (.lsr .d .r7 .r4 64)).isNone &&
  (reg (.lsl .r7 .r4 64)).isNone

-- Loads are little-endian and zero-extended; the byte-reversed ones are big-endian.
#guard reg (.load .w .r7 .r3 4) == some 0x07060504
#guard reg (.load .d .r7 .r3 8) == some 0x0f0e0d0c0b0a0908
#guard reg (.lbz .r7 .r3 15) == some 0x0f
#guard reg (.loadRev .w .r7 .r3 .r5) == some 0x04050607
#guard reg (.loadRev .d .r7 .r3 .r5) == some 0x0405060708090a0b
#guard reg (.loadRev .d .r7 .r3 .r0) == some 0x0001020304050607
-- Out of the permitted regions, or with an unencodable displacement or `r0` as the base.
#guard (reg (.load .d .r7 .r3 9)).isNone
#guard (reg (.load .d .r7 .r3 6)).isNone
#guard (reg (.load .w .r7 .r3 32768)).isNone
#guard (reg (.load .w .r7 .r0 0)).isNone
#guard (reg (.loadRev .w .r7 .r0 .r3)).isNone
#guard (reg (.addi .r7 .r0 1)).isNone

def mem (i : Instr) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  (exec i s0).map (·.mem.read a n)

-- Stores: the low bytes, little-endian; the byte-reversed ones big-endian.
#guard mem (.store .w .r6 .r3 0) 0x1000 8 == some 0x0706050401234567
#guard mem (.store .d .r4 .r3 8) 0x1008 8 == some 0x80000001f0000001
#guard mem (.stb .r6 .r3 3) 0x1000 4 == some 0x67020100
#guard mem (.storeRev .w .r6 .r3 .r5) 0x1004 4 == some 0x67452301
#guard mem (.storeRev .d .r4 .r3 .r5) 0x1004 8 == some 0x010000f001000080
#guard (mem (.store .w .r6 .r3 13) 0x1000 1).isNone

-- The link register.
#guard reg (.mflr .r7) == some 0x4000
#guard ((exec (.mtlr .r6) s0).map (·.lr)) == some 0xffffffff01234567

-- Conditions compare the word or the doubleword with zero.
#guard eval (.zero .w .r4) s0 == some false && eval (.zero .w .r7) s0 == some true
#guard eval (.zero .w .r4) { s0 with gpr := fun _ => 0x100000000 } == some true
#guard eval (.nonzero .d .r4) { s0 with gpr := fun _ => 0x100000000 } == some true
#guard eval (.nonzero .d .r4) { s0 with gpr := fun _ => 0 } == some false

-- A call leaves the next unknown values in `LR`, `r0`, `r11` and `r12`; the
-- return only goes back to that address.
def sCall : State := { s0 with unknowns := fun n => BitVec.ofNat 64 (n + 100) }
#guard (call sCall).map (fun s => (s.lr, s.gpr .r0, s.gpr .r11, s.gpr .r12, s.gpr .r3,
    s.unknowns 0)) == some (100, 101, 102, 103, 0x1000, 104)
#guard ((call sCall).bind fun s₁ => (ret s₁ s₁).map (·.lr)) == some 100
#guard ((call sCall).bind fun s₁ => ret s₁ { s₁ with lr := 0 }).isNone

end VG.Test.PPC64LE
