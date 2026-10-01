import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure WipeStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r

theorem WipeStep.trans {s t u : State} (h : WipeStep s t) (h' : WipeStep t u) : WipeStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.vec.trans h.vec,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem zeroWord_ok {s : State} {E : Addr} (he : s.sp = E)
    (hr : (⟨E, 256⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 32) :
    WP isa (.block (zeroWord k)) s fun t => WipeStep s t ∧
      t.mem = s.mem.writeW (E + BitVec.ofNat 64 (8 * k)) (0 : BitVec 64) := by
  have dest : InRegions s.wr (E + BitVec.ofNat 64 (8 * k)) 8 :=
    ⟨⟨E, 256⟩, hr, Offset.contains_base E (by omega) (by omega)⟩
  have ha {t : State} : exec (.addSp .x15 0) t = some (t.write .x .x15 t.sp) := by
    simp only [exec, show 0 < 4096 from by decide, ite_true, BitVec.add_zero]
  have hz {t : State} : exec (.movz .x .x14 0 0) t = some (t.write .x .x14 0) := by
    simp only [exec, Size.bits, show 16 * 0 < 64 from by decide, ite_true]
    rfl
  apply WP.of_runBlock
  simp only [zeroWord, runBlock_cons, runStep_some, ha, hz]
  rw [exec_str_x ⟨by omega, by omega⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true,
      BitVec.setWidth_eq, he] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h14 h15
    simp only [RegUpd.gpr_write, h14, h15, ite_false]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.setWidth_eq, he]

structure WipeInv (E : Addr) (s : State) (start n : Nat) (t : State) : Prop where
  step : WipeStep s t
  frame : Frame [⟨E + BitVec.ofNat 64 (8 * start), 8 * n⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (8 * (start + j))) 64 = 0

theorem zeroWords_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) (start : Nat) :
    ∀ n, start + n ≤ 32 → WP isa (.block (zeroWords start n)) s (WipeInv E s start n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [zeroWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zeroWords_ok he hw start n (by omega)) fun u hu => ?_
    refine WP.mono (zeroWord_ok (hu.step.sp.trans he) (hu.step.wr ▸ hw) (by omega : start + n < 32))
      fun t ⟨kt, mt⟩ => ?_
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      have old : Frame [⟨E + BitVec.ofNat 64 (8 * start), 8 * (n + 1)⟩] s.mem u.mem :=
        Frame.sub hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
      exact old.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (a := E + BitVec.ofNat 64 (8 * (start + j)))
          (b := E + BitVec.ofNat 64 (8 * (start + n))) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem Ctx.zeroWords {E : Addr} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : Ctx E g v m₀ rd wr s)
    {start count : Nat} (hn : start + count ≤ 32) :
    WP isa (.block (zeroWords start count)) s fun t => Ctx E g v m₀ rd wr t ∧
      Frame [⟨E + BitVec.ofNat 64 (8 * start), 8 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (E + BitVec.ofNat 64 (8 * (start + j))) 64 = 0 := by
  refine WP.mono (zeroWords_ok hc.sp (by rw [hc.wr]; exact List.mem_cons_self) start count hn)
    fun t ht => ⟨?_, ht.frame, ht.words⟩
  refine hc.of_frame ht.step.rd ht.step.wr ht.step.sp ?_ ?_ ht.frame ?_
  · intro r hr _
    apply ht.step.regs
    · rintro rfl; simp [preserved] at hr
    · rintro rfl; simp [preserved] at hr
  · intro r _; rw [ht.step.vec]
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))

end VG.Proof.Ed25519.AArch64.Whole
