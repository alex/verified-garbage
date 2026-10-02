import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Powers
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Gpr

/-!
# Poly1305 on x86-64 with AVX-512: the integer instructions

The short blocks of integer instructions between the vector ones that differ
from `vg_poly1305_blocks_avx2`'s, or after which the upper halves of the `zmm`
registers matter: they leave the whole vector registers as they were (`VKeep`,
unlike `Avx2.VKeep`, includes bits 511:256).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq M0 M1)
open VG.Proof.Poly1305.X86_64.Avx2 (vec vec_gpr vec_mem vec_rd vec_wr ea_at se1 se3)

/-- What a block of integer instructions leaves as it was: the vector
registers, MXCSR and the regions. -/
structure VKeep (s s' : State) : Prop where
  xmm : s'.xmm = s.xmm
  ymmHi : s'.ymmHi = s.ymmHi
  zmmHi : s'.zmmHi = s.zmmHi
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VKeep.qz_eq {s s' : State} (h : VKeep s s') (r : XReg) (k : Nat) : qz s' r k = qz s r k := by
  unfold qz State.zlane State.lane; rw [h.xmm, h.ymmHi, h.zmmHi]

theorem VKeep.trans {s₁ s₂ s₃ : State} (h₁ : VKeep s₁ s₂) (h₂ : VKeep s₂ s₃) : VKeep s₁ s₃ :=
  ⟨h₂.xmm.trans h₁.xmm, h₂.ymmHi.trans h₁.ymmHi, h₂.zmmHi.trans h₁.zmmHi, h₂.mxcsr.trans h₁.mxcsr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem VKeep.avx2 {s s' : State} (h : VKeep s s') : Avx2.VKeep s s' :=
  ⟨h.xmm, h.ymmHi, h.mxcsr, h.rd, h.wr⟩

/-- Closes what `simp` leaves of a block of integer instructions. -/
macro "finish_gpr8" : tactic => `(tactic| (
  all_goals repeat' first | apply And.intro | apply VKeep.mk
  all_goals first | trivial | rfl | (intros; simp [*])))

theorem se40 : BitVec.signExtend 64 (BitVec.ofNat 32 40) = 40 := by decide
theorem se128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
theorem se7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ VKeep s s' ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 40)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', minBlocks, se40]
  exact ⟨trivial, trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

set_option simprocs false in
theorem loadRg_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 24) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 32) 8) :
    WP isa (.block loadRg) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧ s'.gpr .rax = 1 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadRg, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, arithFlags, State.load64, State.setReg, State.setReg32, State.setFlags,
    r₁, r₂, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr8

set_option simprocs false in
theorem loadHw_ok (s : State) (r₀ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 0) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 8) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 16) 8) :
    WP isa (.block Impl.Poly1305.X86_64.Avx2.loadHw) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rax = s.mem.readW (off (s.gpr .rdi) 16) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Poly1305.X86_64.Avx2.loadHw, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, State.load64, State.setReg, r₀, r₁, r₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  finish_gpr8

set_option simprocs false in
theorem rcx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rcx = (s.gpr .rdx >>> 3) - 1 ∧ (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1]
  finish_gpr8

set_option simprocs false in
theorem adv_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ (∀ r, r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1, se128]
  finish_gpr8

set_option simprocs false in
theorem consts2_ok (s : State) :
    WP isa (.block Impl.Poly1305.X86_64.Avx2.consts2) s fun s' =>
      s'.gpr .rax = 5 ∧ s'.gpr .r10 = 0x7ffffff ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Poly1305.X86_64.Avx2.consts2, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, State.setReg32, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  finish_gpr8

set_option simprocs false in
theorem fin3_ok (s : State) :
    WP isa (.block [.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rdx = s.gpr .rdx &&& 7 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, VOp.exec, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left', se7, se128]
  finish_gpr8

end VG.Proof.Poly1305.X86_64.Avx512
