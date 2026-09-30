import VerifiedGarbage.Proof.Ed25519.AArch64.WideMul
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory

/-! Untrusted: loading scalar operands and saving the caller's registers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem mulAddSave_ok {s : State} {base : Addr} (hc : s.gpr .x4 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block mulAddSave) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 48 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [mulAddSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
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

theorem loadWords_ok (s : State) (src : Reg) (hsrc : src ∉ [Reg.x4, .x5, .x6, .x7])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8) :
    WP isa (.block (loadWords src)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem (s.gpr src) 0 ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  apply WP.of_runBlock
  simp only [loadWords, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hsrc.1, hsrc.2.1, hsrc.2.2.1, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul,
    Nat.reduceLT, and_self, hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

theorem copyScalar_ok {s : State} {base : Addr} (hs : Scr s base)
    (src : Reg) (hsrc : src ∉ [Reg.x4, .x5, .x6, .x7])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8)
    (o : Nat) (ho : FieldRange o) :
    WP isa (.block (copyScalar src o)) s fun t =>
      fe t.mem base o = fe s.mem (s.gpr src) 0 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x7] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Outside base o 32 s.mem t.mem := by
  rw [copyScalar, WP.block_append_iff]
  refine WP.mono (loadWords_ok s src hsrc hr) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) ho) fun u hu => ?_
  subst u
  refine ⟨?_, hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩
  · rw [fe_st4 _ _ (by have := ho.2; omega)]; exact hv
  · rw [hk.mem]; exact st4_outside _ _ (by have := ho.2; omega) _ _ _ _

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (hn : 48 ≤ o) : Saved base g m' := by
  intro rd hr
  have hd : rd.2 + 8 ≤ 48 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [ho.word (Or.inl (by omega)) (by omega)]
  exact h rd hr

end VG.Proof.Ed25519.AArch64
