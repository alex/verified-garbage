import VerifiedGarbage.Proof.Ed25519.X86_64.WideMul
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory

/-! Moving the scalar operands and full product through scratch. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

theorem loadWords_ok (s : State) (src : Reg) (hsrc : src ∉ [Reg.r8, .r9, .r10, .r11])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8) :
    WP isa (.block (loadWords src)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem (s.gpr src) 0 ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  apply WP.of_runBlock
  simp only [loadWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hsrc.1, hsrc.2.1, hsrc.2.2.1,
    hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

theorem stores8192_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {o : Nat} (ho : o + 32 ≤ 8192)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun t =>
      t.mem = st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hp, State.store64,
    w o (by omega), w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega),
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, trivial, trivial⟩

theorem copyScalar_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (src : Reg) (hsrc : src ∉ [Reg.r8, .r9, .r10, .r11])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8)
    (o : Nat) (ho : o + 32 ≤ 8192) :
    WP isa (.block (copyScalar src o)) s fun t =>
      fe t.mem base o = fe s.mem (s.gpr src) 0 ∧
      (∀ r, r ∉ [Reg.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base o 32 s.mem t.mem := by
  rw [copyScalar, WP.block_append_iff]
  refine WP.mono (loadWords_ok s src hsrc hr) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (stores8192_ok ((hk.1 .rdi (by decide)).trans hp) (hk.2.2.2 ▸ hw)
    ho .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, fun r h => (congrFun hg r).trans (hk.1 r h), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩
  · rw [hm, fe_st4 _ _ (by omega)]; exact hv
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem mulAddSave_ok {s : State} {base : Addr} (hc : s.gpr .r8 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block mulAddSave) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [mulAddSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
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


end VG.Proof.Ed25519.X86_64
