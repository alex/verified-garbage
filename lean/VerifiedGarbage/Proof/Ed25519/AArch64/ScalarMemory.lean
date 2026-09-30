import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarLoop

/-! Untrusted: scalar reducer saves, restores, and output stores. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- The six used callee-saved registers occupy scratch bytes 0–47. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ rd ∈ saved, word m base rd.2 = g rd.1

theorem scalarSave_ok {s : State} {base : Addr} (hc : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarSave) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 48 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.store, read_x, hc, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), w 32 (by omega), w 40 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, True.intro, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _
  · change word _ base rd.2 = s.gpr rd.1
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    simp only [write64_eq_writeW]
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

theorem scalarRestore_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block scalarRestore) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarRestore, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem scalarOut_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x0 0, .str .x .x5 .x0 8, .str .x .x6 .x0 16, .str .x .x7 .x0 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl

theorem scalarInit_ok (s : State) :
    WP isa (.block scalarInit) s fun t =>
      t.gpr .x19 = 64 ∧ scalarValue t = 0 ∧ t.gpr .x10 = 0 ∧ t.gpr .x11 = 1 ∧
      Keeps [.x4, .x5, .x6, .x7, .x10, .x11, .x19] s t := by
  apply WP.of_runBlock
  simp only [scalarInit, zero4, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    scalarValue, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
