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
    ("blocks", .slice false (.array .u8 64) "n"), ("k", .slice true .u64 "k_len"),
    ("parts", .slices .u8 "count")]
  ret := some .u64

#guard sample.rust == "(a: u64, b: u32, c: usize, s: *mut [u32; 8], t: *const [u8; 3], \
  blocks: *const [u8; 64], n: usize, k: *mut u64, k_len: usize, parts: *const [usize; 2], \
  count: usize) -> u64"
#guard ({ params := [] } : Sig).rust == "()"

#guard (sample.words 64).map (·.bits 64) == [64, 32, 64, 64, 64, 64, 64, 64, 64, 64, 64]
#guard (sample.words 32).map (·.bits 32) == [64, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32]

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
-- The ninth argument is the 8 bytes at `sp`. A lone narrow stack argument
-- is rejected; a u32 followed by u64s has the same aligned layout on both ABIs.
#guard (AArch64.abi.args (List.replicate 9 64)).map (· aarch64Stack) ==
  some [1, 2, 3, 4, 5, 6, 7, 8, 0x0807060504030201]
#guard (AArch64.abi.args (List.replicate 8 64 ++ [32])).isNone
-- The u32 at SP occupies its low half; the next u64 is at SP + 8.
#guard (AArch64.abi.args (List.replicate 8 64 ++ [32, 64])).map (· aarch64Stack) ==
  some [1, 2, 3, 4, 5, 6, 7, 8, 0x0807060504030201, 0]
#guard (AArch64.abi.argArea (List.replicate 8 64 ++ [32, 64]) aarch64Stack).map (·.1) ==
  [⟨0x100, 16⟩]
#guard (AArch64.abi.args (List.replicate 8 64 ++ [32, 32, 64])).isNone
#guard (AArch64.abi.args (List.replicate 8 64 ++ [64, 32, 64])).isNone
#guard (AArch64.abi.args (List.replicate 8 64 ++ [16, 64])).isNone
#guard (AArch64.abi.argArea (List.replicate 9 64) aarch64Stack).map (·.1) == [⟨0x100, 8⟩]
-- `ldr xt, [sp, #off]` reads the stack arguments where the ABI puts them:
-- `stackArg s i` at `sp + 8 * i`, within the argument area.
def aarch64StackRd : AArch64.State :=
  { aarch64Stack with rd := (AArch64.abi.argArea (List.replicate 9 64) aarch64Stack).map (·.1) }
#guard (AArch64.exec (.ldrSp .x9 0) aarch64StackRd).map (·.gpr .x9) ==
  some (AArch64.stackArg aarch64Stack 0)
#guard (AArch64.exec (.ldrSp .x9 0) aarch64StackRd).map (·.gpr .x9) == some 0x0807060504030201
#guard AArch64.addrs (.ldrSp .x9 8) aarch64Stack == [0x108]
-- It faults outside the readable regions, at an offset that is not a
-- multiple of 8, and at one it cannot encode (`imm12 * 8`, so below 32768).
#guard (AArch64.exec (.ldrSp .x9 0) aarch64Stack).isNone
#guard (AArch64.exec (.ldrSp .x9 8) aarch64StackRd).isNone
#guard (AArch64.exec (.ldrSp .x9 4) { aarch64StackRd with sp := 0xfc }).isNone
#guard (AArch64.exec (.ldrSp .x9 32760) { aarch64StackRd with sp := 0x100 - 32760 }).isSome
#guard (AArch64.exec (.ldrSp .x9 32768) { aarch64StackRd with sp := 0x100 - 32768 }).isNone
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
  ⟨rfl, fun | 0, _ => rfl | _ + 1, _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

example : ¬(pubU32.contract X86_64.abi (post := fun _ _ _ _ => True)).pub
    (x86_64Rdi 0x00000000_00000001) (x86_64Rdi 0x00000000_00000002) :=
  fun ⟨_, h, _⟩ => absurd (h 0 rfl) (by decide)

/-- `aarch64State` with `v` in `x0`, the register of `n`. -/
def aarch64X0 (v : BitVec 64) : AArch64.State :=
  { aarch64State with gpr := fun r => if r = .x0 then v else aarch64State.gpr r }

example : (pubU32.contract AArch64.abi (post := fun _ _ _ _ => True)).pub
    (aarch64X0 0x00000000_00000001) (aarch64X0 0xffffffff_00000001) :=
  ⟨rfl, fun | 0, _ => rfl | _ + 1, _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

example : ¬(pubU32.contract AArch64.abi (post := fun _ _ _ _ => True)).pub
    (aarch64X0 0x00000000_00000001) (aarch64X0 0x00000000_00000002) :=
  fun ⟨_, h, _⟩ => absurd (h 0 rfl) (by decide)

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

/-! ## Lists of slices

The memory of a list of slices is its descriptors (two pointer-sized words
each, little-endian) and the slices they list, read from the memory on entry;
where the slices are is public, and their contents are not. -/

/-- A writable buffer, and a list of slices. -/
def listSig : Sig where
  params := [("out", .array true .u8 16), ("parts", .slices .u8 "count")]

/-- The little-endian bytes of `v` in `k` bytes from `base`, in memory `m`. -/
def poke (m : Mem) (base : Nat) (k v : Nat) : Mem := fun a =>
  if base ≤ a.toNat ∧ a.toNat < base + k then BitVec.ofNat 8 (v / 256 ^ (a.toNat - base)) else m a

/-- Two 64-bit descriptors at `0x2000`: 5 bytes at `0x3000`, 3 at `0x4000`. -/
def desc64 : Mem :=
  poke (poke (poke (poke (fun _ => 0) 0x2000 8 0x3000) 0x2008 8 5) 0x2010 8 0x4000) 0x2018 8 3

#guard Sig.lists 64 desc64 listSig.params [0x1000, 0x2000, 2] ==
  [⟨0x2000, 32⟩, ⟨0x3000, 5⟩, ⟨0x4000, 3⟩]
#guard Sig.descs 64 listSig.params [0x1000, 0x2000, 2] == [⟨0x2000, 32⟩]
-- An empty list has no descriptors to read.
#guard Sig.lists 64 desc64 listSig.params [0x1000, 0x2000, 0] == [⟨0x2000, 0⟩]

/-- The same list with 32-bit descriptors. -/
def desc32 : Mem :=
  poke (poke (poke (poke (fun _ => 0) 0x2000 4 0x3000) 0x2004 4 5) 0x2008 4 0x4000) 0x200c 4 3

#guard Sig.lists 32 desc32 listSig.params [0x1000, 0x2000, 2] ==
  [⟨0x2000, 16⟩, ⟨0x3000, 5⟩, ⟨0x4000, 3⟩]

/-- `out` at `0x1000`, the descriptors `desc64` at `0x2000` and the memory
the precondition permits. -/
def listState (m : Mem) : X86_64.State :=
  { x86_64State with
    gpr := fun r => match r with
      | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 2 | .rsp => 0x8000 | _ => 0
    mem := m
    rd := [⟨0x2000, 32⟩, ⟨0x3000, 5⟩, ⟨0x4000, 3⟩]
    wr := [⟨0x1000, 16⟩] }

-- The precondition's memory: the descriptors and the slices they list are
-- read-only.
#guard (X86_64.abi.args [64, 64, 64]).map (fun f =>
    Sig.lists 64 (listState desc64).mem listSig.params (f (listState desc64))) ==
  some [⟨0x2000, 32⟩, ⟨0x3000, 5⟩, ⟨0x4000, 3⟩]

-- Two runs that differ only in a listed slice's contents agree on the public
-- data; two that differ in a descriptor (a slice's length) do not.
example : (listSig.contract X86_64.abi (post := fun _ _ _ _ _ _ => True)).pub
    (listState desc64) (listState (poke desc64 0x3000 5 0x1122334455)) := by
  refine ⟨rfl, fun | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | _ + 3, _ => rfl, fun r hr => ?_⟩
  have hr : r ∈ [(⟨0x2000, 32⟩ : Region)] := hr
  rw [List.mem_singleton] at hr
  subst hr
  decide

example : ¬(listSig.contract X86_64.abi (post := fun _ _ _ _ _ _ => True)).pub
    (listState desc64) (listState (poke desc64 0x2008 8 6)) :=
  fun ⟨_, _, h⟩ => absurd (h ⟨0x2000, 32⟩ (by decide) 8 (by decide)) (by decide)

end VG.Test.Abi
