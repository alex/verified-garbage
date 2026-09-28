import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Spec.Sha256.X86_64
import VerifiedGarbage.Spec.Sha256.Arm

/-!
# Golden tests for signatures and calling conventions

`Sig.rust` and each target's `abi` are part of the TCB; these tests pin down
the rendered signatures and where each calling convention places arguments,
so that changes to them are deliberate and show up in review. The last
section checks that `Sig.contract` implies the hand-written contracts of
`vg_sha256_update` on x86-64 and 32-bit ARM.
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

#guard (X86_64.abi.args [64, 32, 64, 64, 64, 64]).map (· x86_64State) == some [1, 2, 3, 4, 5, 6]
#guard (X86_64.abi.args (List.replicate 7 64)).isNone
#guard X86_64.abi.ret x86_64State == 7

def aarch64State : AArch64.State where
  gpr r := match r with
    | .x0 => 1 | .x1 => 2 | .x2 => 3 | .x3 => 4 | .x4 => 5 | .x5 => 6 | .x6 => 7 | .x7 => 8
    | _ => 0
  sp := 0
  mem _ := 0
  rd := []
  wr := []

#guard (AArch64.abi.args (List.replicate 8 64)).map (· aarch64State) == some [1, 2, 3, 4, 5, 6, 7, 8]
#guard (AArch64.abi.args (List.replicate 9 64)).isNone
#guard AArch64.abi.ret aarch64State == 1

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
#guard X86.abi.reserved x86State == [⟨0x100, 4⟩]
#guard X86.abi.ret x86State == 0x0000000200000001

/-! ## `Sig.contract` against hand-written contracts -/

section
open Spec.Sha256

def updateSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 20)]

/-- The contract of `vg_sha256_update` on any target. -/
def update {M : ISA} (A : Abi M) : Contract M :=
  updateSig.contract A (post := fun state count data len _scratch m m' _ =>
    ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length →
      Repr m' state (msg ++ bytesAt m data len.toNat))

theorem update_x86_64_pre (s : X86_64.State) (h : (update X86_64.abi).pre s) :
    updateX86_64.pre s := by
  simp [update, Sig.contract, updateSig, Sig.words, Param.words, X86_64.abi, X86_64.argRegs,
    ArgWord.bits, IntTy.bits, Sig.bufs, Elem.size, List.pairwise_cons] at h
  obtain ⟨hrd, hwr, ⟨⟨h1, h2⟩, h3⟩, hret, -⟩ := h
  exact ⟨hrd, hwr, h2, fun a ha hb => h1 a hb ha, h3, hret.1, hret.2.2⟩

theorem update_x86_64_pub (s₁ s₂ : X86_64.State) (h : (update X86_64.abi).pub s₁ s₂) :
    updateX86_64.pub s₁ s₂ := by
  simp [update, Sig.contract, updateSig, Sig.words, Param.words, X86_64.abi, X86_64.argRegs,
    ArgWord.bits, IntTy.bits, Param.pubs] at h
  exact ⟨h.2 0 (by decide), h.2 1 (by decide), h.2 2 (by decide), h.2 3 (by decide),
    h.2 4 (by decide)⟩

theorem update_x86_64_post (s s' : X86_64.State) :
    (update X86_64.abi).post s s' ↔ updateX86_64.post s s' :=
  Iff.rfl

theorem update_arm_pre (s : Arm.State) (h : (update Arm.abi).pre s) : updateArm.pre s := by
  simp [update, Sig.contract, updateSig, Sig.words, Param.words, Arm.abi, Arm.argRegs,
    ArgWord.bits, IntTy.bits, Sig.bufs, Elem.size, List.pairwise_cons, Arm.classify,
    Arm.Loc.val] at h
  obtain ⟨hsp, hrd, hwr, ⟨⟨h1, h2, h3⟩, h4, h5⟩, ⟨n0, n1, n2⟩, -⟩ := h
  have fl : ∀ {a b : Region}, a.Disjoint b → b.Disjoint a := fun h x hb ha => h x ha hb
  have m : ∀ x : BitVec 32, x.toNat % 18446744073709551616 = x.toNat := fun x => by
    have := x.isLt; omega
  simp only [m] at hrd n0 n1 n2 h1 h4
  exact ⟨hrd, hwr, h2, fl h1, h4, fl h3, fl h5, by omega, n1, by omega, by omega⟩

end

end VG.Test.Abi
