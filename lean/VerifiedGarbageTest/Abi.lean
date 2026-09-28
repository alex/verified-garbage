import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.X86.Target

/-!
# Golden tests for signatures and calling conventions

`Sig.rust` and each target's `abi` are part of the TCB; these tests pin down
the rendered signatures and where each calling convention places arguments,
so that changes to them are deliberate and show up in review.
-/

namespace VG.Test.Abi

/-- Every kind of parameter. -/
def sample : Sig where
  params := [("a", .int .u64 false), ("b", .int .u32 true), ("c", .int .usize true),
    ("s", .array true .u32 8), ("t", .array false .u8 3),
    ("blocks", .slice false (.array .u8 64) "n"), ("k", .slice true .u64 "k_len")]
  ret := some .u64

#guard sample.rust == "(a: u64, b: u32, c: usize, s: *mut [u32; 8], t: *const [u8; 3], \
  blocks: *const [u8; 64], n: usize, k: *mut u64, k_len: usize) -> u64"
#guard ({ params := [] } : Sig).rust == "()"

#guard (sample.words 64).map (·.bits 64) == [64, 32, 64, 64, 64, 64, 64, 64, 64]
#guard (sample.words 32).map (·.bits 32) == [64, 32, 32, 32, 32, 32, 32, 32, 32]

/-! ## x86-64 and AArch64: one register per argument -/

def x86_64State : X86_64.State where
  gpr r := match r with
    | .rdi => 1 | .rsi => 2 | .rdx => 3 | .rcx => 4 | .r8 => 5 | .r9 => 6 | .rax => 7 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []

/-- `x86_64State` with `rsp = 0x100` and the bytes 1 to 8 at `0x108`. -/
def x86_64Stack : X86_64.State :=
  { x86_64State with
    gpr := fun r => if r = .rsp then 0x100 else x86_64State.gpr r
    mem := fun a => if 0x108 ≤ a.toNat ∧ a.toNat < 0x110 then BitVec.ofNat 8 (a.toNat - 0x107) else 0 }

#guard (X86_64.abi.args [64, 32, 64, 64, 64, 64]).map (· x86_64State) == some [1, 2, 3, 4, 5, 6]
-- The seventh argument is the eightbyte above the return address.
#guard (X86_64.abi.args (List.replicate 7 64)).map (· x86_64Stack) ==
  some [1, 2, 3, 4, 5, 6, 0x0807060504030201]
#guard (X86_64.abi.argArea (List.replicate 8 64) x86_64Stack).map (·.1) == [⟨0x108, 16⟩]
#guard (X86_64.abi.argArea (List.replicate 6 64) x86_64Stack).isEmpty
#guard X86_64.abi.ret x86_64State == 7

def aarch64State : AArch64.State where
  gpr r := match r with
    | .x0 => 1 | .x1 => 2 | .x2 => 3 | .x3 => 4 | .x4 => 5 | .x5 => 6 | .x6 => 7 | .x7 => 8
    | _ => 0
  sp := 0
  mem _ := 0
  rd := []
  wr := []

/-- `aarch64State` with `sp = 0x100` and the bytes 1 to 8 at `0x100`. -/
def aarch64Stack : AArch64.State :=
  { aarch64State with
    sp := 0x100
    mem := fun a => if 0x100 ≤ a.toNat ∧ a.toNat < 0x108 then BitVec.ofNat 8 (a.toNat - 0xff) else 0 }

#guard (AArch64.abi.args (List.replicate 8 64)).map (· aarch64State) == some [1, 2, 3, 4, 5, 6, 7, 8]
-- The ninth argument is the 8 bytes at `sp`; narrower stack arguments are
-- not modelled.
#guard (AArch64.abi.args (List.replicate 9 64)).map (· aarch64Stack) ==
  some [1, 2, 3, 4, 5, 6, 7, 8, 0x0807060504030201]
#guard (AArch64.abi.args (List.replicate 8 64 ++ [32])).isNone
#guard (AArch64.abi.argArea (List.replicate 9 64) aarch64Stack).map (·.1) == [⟨0x100, 8⟩]
#guard AArch64.abi.ret aarch64State == 1

/-! ### Public arguments are public only in the bits of their width

A 32-bit argument leaves the upper half of its 64-bit register unspecified
(whatever the caller left there, which may be secret): two entry states that
differ only there agree on the public argument, and states that differ in its
low half do not. -/

def pubU32 : Sig where
  params := [("n", .int .u32 true)]

/-- `x86_64State` with `v` in `rdi`, the register of `n`. -/
def x86_64Rdi (v : BitVec 64) : X86_64.State :=
  { x86_64State with gpr := fun r => if r = .rdi then v else x86_64State.gpr r }

example : (pubU32.contract X86_64.abi (post := fun _ _ _ _ => True)).pub
    (x86_64Rdi 0x00000000_00000001) (x86_64Rdi 0xffffffff_00000001) :=
  ⟨rfl, fun | 0, _ => rfl | _ + 1, _ => rfl⟩

example : ¬(pubU32.contract X86_64.abi (post := fun _ _ _ _ => True)).pub
    (x86_64Rdi 0x00000000_00000001) (x86_64Rdi 0x00000000_00000002) :=
  fun ⟨_, h⟩ => absurd (h 0 rfl) (by decide)

/-- `aarch64State` with `v` in `x0`, the register of `n`. -/
def aarch64X0 (v : BitVec 64) : AArch64.State :=
  { aarch64State with gpr := fun r => if r = .x0 then v else aarch64State.gpr r }

example : (pubU32.contract AArch64.abi (post := fun _ _ _ _ => True)).pub
    (aarch64X0 0x00000000_00000001) (aarch64X0 0xffffffff_00000001) :=
  ⟨rfl, fun | 0, _ => rfl | _ + 1, _ => rfl⟩

example : ¬(pubU32.contract AArch64.abi (post := fun _ _ _ _ => True)).pub
    (aarch64X0 0x00000000_00000001) (aarch64X0 0x00000000_00000002) :=
  fun ⟨_, h⟩ => absurd (h 0 rfl) (by decide)

/-! ## 32-bit ARM (AAPCS) -/

open Arm in
-- `vg_sha256_update`: `count` skips `r1` for the pair `r2:r3`; the rest is on the stack.
#guard classify [32, 64, 32, 32, 32] 0 0 ==
  ([.reg .r0, .pair .r2 .r3, .stack 0 32, .stack 4 32, .stack 8 32], 12)

open Arm in
-- `vg_hmac_sha256_init`: four registers, then the stack.
#guard classify [32, 32, 32, 32, 32] 0 0 ==
  ([.reg .r0, .reg .r1, .reg .r2, .reg .r3, .stack 0 32], 4)

open Arm in
-- A 64-bit argument with only `r3` left goes on the stack, and `r3` stays unused.
#guard classify [32, 32, 32, 64, 32] 0 0 ==
  ([.reg .r0, .reg .r1, .reg .r2, .stack 0 64, .stack 8 32], 12)

open Arm in
-- A 64-bit argument on the stack is aligned to 8 bytes.
#guard classify [32, 32, 32, 32, 32, 64] 0 0 ==
  ([.reg .r0, .reg .r1, .reg .r2, .reg .r3, .stack 0 32, .stack 8 64], 16)

#guard (Arm.abi.args [32, 16]).isNone

/-- Registers `r0`–`r3` hold 1–4, `sp` is `0x100`, and each byte of memory is
the low byte of its address. -/
def armState : Arm.State where
  gpr r := match r with
    | .r0 => 1 | .r1 => 2 | .r2 => 3 | .r3 => 4 | _ => 0
  sp := 0x100
  n := false
  z := false
  c := false
  v := false
  mem a := a.setWidth 8
  rd := []
  wr := []

#guard (Arm.abi.args [32, 64, 32, 32, 64]).map (· armState) ==
  some [1, 0x0000000400000003, 0x03020100, 0x07060504, 0x0f0e0d0c0b0a0908]
-- A 64-bit stack argument is the little-endian doubleword at its slot.
#guard Arm.Loc.val armState (.stack 8 64) == armState.mem.readW 0x108 64
#guard Arm.abi.argArea [32, 64, 32, 32, 64] armState == [(⟨0x100, 16⟩, false)]
#guard Arm.abi.argArea [32, 32] armState == []
#guard Arm.abi.ret armState == 0x0000000200000001

/-! ## x86 (cdecl): everything on the stack -/

#guard X86.argSlots [32, 64, 32, 64] 0 == [0, 1, 3, 4]
#guard X86.argBytes [32, 64, 32, 64] == 24
#guard (X86.abi.args [32, 16]).isNone

/-- `esp` is `0x100`, `eax` and `edx` hold 1 and 2, and each byte of memory
is the low byte of its address. -/
def x86State : X86.State where
  gpr r := match r with
    | .esp => 0x100 | .eax => 1 | .edx => 2 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := a.setWidth 8
  rd := []
  wr := []

#guard (X86.abi.args [32, 64, 32]).map (· x86State) ==
  some [0x07060504, 0x0f0e0d0c0b0a0908, 0x13121110]
#guard X86.abi.argArea [32, 64, 32] x86State == [(⟨0x104, 16⟩, true)]
#guard X86.abi.reserved 0 x86State == [⟨0x100, 4⟩]
-- A function whose calls use 12 bytes of stack: the 12 bytes below `esp` too.
#guard X86.abi.reserved 12 x86State == [⟨0x100, 4⟩, ⟨0xf4, 12⟩]
#guard X86.abi.ret x86State == 0x0000000200000001

end VG.Test.Abi
