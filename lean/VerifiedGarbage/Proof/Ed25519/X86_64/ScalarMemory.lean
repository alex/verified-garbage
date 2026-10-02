import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarLoop
import VerifiedGarbage.Proof.X25519.X86_64.Finish

/-!
# Scalar reduction: memory and callee-saved registers

Saving and restoring use the first 48 bytes of the scratch argument, and the
next 8 hold the output's address while the loop keeps the scratch in `rdi`.
The arithmetic loop changes no memory.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (at_ saved zero4)
open VG.Proof.X25519.X86_64

theorem scalarSave_ok {s : State} {base : Addr} (hc : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarSave) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [scalarSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, ea_at, hc, State.store64, w 0 (by omega), w 8 (by omega), w 16 (by omega),
    w 24 (by omega), w 32 (by omega), w 40 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

theorem scalarRestore_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (.block scalarRestore) s fun s' =>
      (∀ rd ∈ saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, Offset.contains_base base hd (by omega)⟩
  have v : ∀ rd ∈ saved, s.mem.readW (off base rd.2) 64 = g rd.1 := hsv
  apply WP.of_runBlock
  simp only [scalarRestore, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hb, hr 0 (by omega), hr 8 (by omega),
    hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega), ite_true, ite_false,
    reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, fun r hr => ?_, trivial, trivial, trivial⟩
  · have e := v rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq] using e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem scalarOut_ok {s : State} {q : Addr} (hq : s.gpr .rdi = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block ([.store (at_ .rdi 0) .r8, .store (at_ .rdi 8) .r9, .store (at_ .rdi 16) .r10,
      .store (at_ .rdi 24) .r11] : List Instr)) s fun s' =>
      s'.mem = st4 s.mem q 0 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hq, State.store64,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  exact ⟨rfl, trivial, trivial, trivial⟩

theorem scalarInit_ok (s : State) :
    WP isa (.block (zero4 ++ ([.mov32 .rbx (.imm 64)] : List Instr))) s fun t =>
      t.gpr .rbx = 64 ∧ scalarValue t = 0 ∧ Keeps [.r8, .r9, .r10, .r11, .rbx] s t := by
  apply WP.of_runBlock
  simp only [zero4, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left', scalarValue, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq]
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The output's address to byte 48 of the scratch (in `rdx`), and the scratch into `rdi`. -/
theorem stashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block [.store (at_ .rdx 48) .rdi, .mov .rdi (.reg .rdx)]) s fun t =>
      t.mem = s.mem.writeW (off base 48) (s.gpr .rdi) ∧ t.gpr .rdi = base ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (off base 48) 8 := ⟨_, hw, Offset.contains_base base (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, ea_at, hb, State.store64, w,
    ite_true, RegUpd.gpr_setReg, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun r hr => by simp only [hr, ite_false], rfl, rfl⟩

/-- The scratch from `rdi` back into `rdx`, and the output's address from byte 48 into `rdi`. -/
theorem finishArgs_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarFinishArgs) s fun t =>
      t.gpr .rdx = base ∧ t.gpr .rdi = s.mem.readW (off base 48) 64 ∧
      (∀ r, r ≠ .rdx → r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hw, Offset.contains_base base (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [scalarFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, ea_at,
    State.load64, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hb, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], trivial, trivial, trivial⟩

theorem scratchFrame {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192) : Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn'
  simp only [ofs]
  omega

end VG.Proof.Ed25519.X86_64
