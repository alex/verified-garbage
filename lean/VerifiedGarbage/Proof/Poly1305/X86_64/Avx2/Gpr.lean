import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Powers
import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Poly1305 on x86-64 with AVX2: the integer instructions

Untrusted: everything here is checked by Lean. The short blocks of integer
instructions between the vector ones: constants, the MXCSR prologue and
epilogue, loading `r` and the accumulator's words, and the counters.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq M0 M1)

/-- What a block of integer instructions leaves as it was: the vector
registers, MXCSR and the regions. -/
structure VKeep (s s' : State) : Prop where
  xmm : s'.xmm = s.xmm
  ymmHi : s'.ymmHi = s.ymmHi
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VKeep.qw_eq {s s' : State} (h : VKeep s s') (r : XReg) (k : Nat) : qw s' r k = qw s r k := by
  unfold qw State.lane; rw [h.xmm, h.ymmHi]

theorem VKeep.trans {s₁ s₂ s₃ : State} (h₁ : VKeep s₁ s₂) (h₂ : VKeep s₂ s₃) : VKeep s₁ s₃ :=
  ⟨h₂.xmm.trans h₁.xmm, h₂.ymmHi.trans h₁.ymmHi, h₂.mxcsr.trans h₁.mxcsr, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem vec_keep {s s' : State} (h : vec s s' = s') : s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  ⟨vec_gpr h, vec_mem h, vec_rd h, vec_wr h, by rw [← h]; rfl⟩

theorem se16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
theorem se32 : BitVec.signExtend 64 (BitVec.ofNat 32 32) = 32 := by decide
theorem se64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem se3 : BitVec.signExtend 64 (3 : BitVec 32) = 3 := by decide

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ VKeep s s' ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', minBlocks,
    se32]
  exact ⟨trivial, trivial, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

set_option simprocs false in
theorem consts_ok (s : State) :
    WP isa (.block consts) s fun s' =>
      s'.gpr .r8 = 0x3ffffff ∧ s'.gpr .r9 = 0x1000000 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [consts, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, State.setReg32, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, fun r h₁ h₂ => by simp [h₁, h₂], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-- Closes what `simp` leaves of a block of integer instructions. -/
macro "finish_gpr" : tactic => `(tactic| (
  all_goals repeat' first | apply And.intro | apply VKeep.mk
  all_goals first | trivial | rfl | (intros; simp [*])))

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

/-- The memory `mxcsrIn` leaves: MXCSR with bits 31:16 cleared at byte 120,
and `0x1FBF` at byte 124. -/
def mxMem (m : Mem) (st : Addr) (x : BitVec 32) : Mem :=
  ((m.writeW (off st 120) x).writeW (off st 120) (x &&& 0xffff)).writeW (off st 124) (0x1FBF : BitVec 32)

set_option simprocs false in
theorem mxcsrIn_ok (s : State) (w₁ : InRegions s.wr (off (s.gpr .rdi) 120) 4)
    (w₂ : InRegions s.wr (off (s.gpr .rdi) 124) 4) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 120) 4)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 124) 4) :
    WP isa (.block mxcsrIn) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = mxMem s.mem (s.gpr .rdi) s.mxcsr ∧
      s'.mxcsr = 0x1FBF ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mxcsrIn, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc32, execAlu32, arithFlags, State.load32, State.store32, State.setReg32, State.setReg,
    State.setFlags, w₁, w₂, r₁, r₂, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', Mem.readW_writeW_self32, RegUpd.setWidth_setWidth_32]
  refine ⟨fun r h => by simp [h], ?_, trivial⟩
  rfl

theorem powers_split : consts ++ mxcsrIn ++ powers ++ loadHw ++ loadH ++
    ([.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)] : List Instr) =
    consts ++ (mxcsrIn ++ (loadRg ++ (powersV ++ (loadHw ++ (loadH ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)] : List Instr)))))) := by
  simp only [powers_eq, List.append_assoc]

set_option simprocs false in
theorem loadRg_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 24) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 32) 8) :
    WP isa (.block loadRg) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadRg, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.load64, State.setReg, State.setFlags, r₁, r₂, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem loadHw_ok (s : State) (r₀ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 0) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 8) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 16) 8) :
    WP isa (.block loadHw) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rax = s.mem.readW (off (s.gpr .rdi) 16) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadHw, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, State.load64, State.setReg, r₀, r₁, r₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem rcx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rcx = (s.gpr .rdx >>> 2) - 1 ∧ (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1]
  finish_gpr

set_option simprocs false in
theorem adv_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 64), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ (∀ r, r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1, se64]
  finish_gpr

set_option simprocs false in
theorem consts2_ok (s : State) :
    WP isa (.block consts2) s fun s' =>
      s'.gpr .rax = 5 ∧ s'.gpr .r10 = 0x7ffffff ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [consts2, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, State.setReg32, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem mxcsrOut_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 120) 4)
    (hz : (s.mem.readW (off (s.gpr .rdi) 120) 32).extractLsb' 16 16 = 0) :
    WP isa (.block mxcsrOut) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mem.readW (off (s.gpr .rdi) 120) 32 ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [mxcsrOut, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.load32, r₁, hz,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr

set_option simprocs false in
theorem fin3_ok (s : State) :
    WP isa (.block [.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx &&& 3 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, VOp.exec, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left', se3, se64]
  finish_gpr

set_option simprocs false in
theorem test_ok (s : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      s'.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']

end VG.Proof.Poly1305.X86_64.Avx2
