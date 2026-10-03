import VerifiedGarbage.Impl.Ed25519.X86_64.MulAdd
import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory

/-! Merged from `Proof.Ed25519.X86_64.WideMul`. -/
section
/-! The eight product words represent the full unsigned product. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

def wideValue (s : State) : Nat :=
  val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
    2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)

theorem wideAccumulate_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      wideValue t = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s t := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [show wideAccumulate a b = row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3)) by
    simp only [wideAccumulate, List.append_assoc]]
  rw [WP.block_append_iff, row0]
  refine WP.mono (rowR_ok hs (by omega) hb (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, row1]
  refine WP.mono (rowR_ok hs₁ (by omega) hb (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff, row2]
  refine WP.mono (rowR_ok hs₂ (by omega) hb (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [row3]
  refine WP.mono (rowR_ok hs₃ (by omega) hb (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans (k4.mono (by decide))⟩
  change val4 (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11) +
    2 ^ 256 * val4 (s₄.gpr .r12) (s₄.gpr .r13) (s₄.gpr .r14) (s₄.gpr .r15) = _
  rw [fe_mul_expand]
  -- Every row read the same memory.
  rw [k1.2.1] at e2
  rw [k2.2.1, k1.2.1] at e3
  rw [k3.2.1, k2.2.1, k1.2.1] at e4
  -- The registers along the way.
  have r1 := g k2 .r8 (by decide); have r2 := g k3 .r8 (by decide); have r3 := g k4 .r8 (by decide)
  have q2 := g k3 .r9 (by decide); have q3 := g k4 .r9 (by decide); have q4 := g k4 .r10 (by decide)
  simp only [val4] at e1 e2 e3 e4 ⊢
  rw [r3, r2, r1, q3, q2, q4]
  omega_using [e1, e2, e3, e4]

/-- Reuse the checked four-KiB arithmetic within Ed25519's larger scratch
argument. Execution is lifted by the framework's memory-permission theorem. -/
theorem wideAccumulate8192_ok {s : State} {base : Addr}
    (hp : s.gpr .rdi = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) {a b : Nat} (ha : Slot a) (hb : Slot b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      wideValue t = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s t := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hs : Scr narrow base := ⟨hp, List.mem_singleton_self _, by omega⟩
  obtain ⟨tr, t, he, hv, hk⟩ := wideAccumulate_ok hs ha hb
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hw, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hv, hk.1, hk.2.1, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
end

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
