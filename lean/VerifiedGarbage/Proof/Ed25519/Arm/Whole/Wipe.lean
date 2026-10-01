import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure WipeStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r

theorem WipeStep.trans {s t u : State} (h : WipeStep s t) (h' : WipeStep t u) : WipeStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem zeroWord_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hr : (⟨State.addr E, 248⟩ : Region) ∈ s.wr)
    {k : Nat} (hk : k < 62) :
    WP isa (.block (zeroWord k)) s fun t => WipeStep s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32) := by
  have ae : State.addr (E + BitVec.ofNat 32 (4 * k)) = State.addr E + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega)
  have dest : InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, hr, Offset.contains_base _ (by omega) (by omega)⟩
  have ha {t : State} : exec (.addSp .r12 0) t = some (t.setReg .r12 t.sp) := by
    simp only [exec, show 0 < 256 from by decide, ite_true, BitVec.add_zero]
  have hz {t : State} : exec (.movw .r0 0) t = some (t.setReg .r0 0) := rfl
  apply WP.of_runBlock
  simp only [zeroWord, runBlock_cons, runStep_some, ha, hz]
  rw [exec_str (by omega) (by
    simpa only [RegUpd.wr_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true,
      he, ae] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h12
    simp only [RegUpd.gpr_setReg, h0, h12, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, he, ae]

structure WipeInv (E : BitVec 32) (s : State) (start n : Nat) (t : State) : Prop where
  step : WipeStep s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * n⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr E + BitVec.ofNat 64 (4 * (start + j))) 32 = 0

theorem zeroWords_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) (start : Nat) :
    ∀ n, start + n ≤ 62 → WP isa (.block (zeroWords start n)) s (WipeInv E s start n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [zeroWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zeroWords_ok he hf hw start n (by omega)) fun u hu => ?_
    refine WP.mono (zeroWord_ok (hu.step.sp.trans he) hf (hu.step.wr ▸ hw) (by omega : start + n < 62))
      fun t ⟨kt, mt⟩ => ?_
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      have old : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * (n + 1)⟩] s.mem u.mem :=
        Frame.sub hu.frame fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
      exact old.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := State.addr E + BitVec.ofNat 64 (4 * (start + j)))
          (b := State.addr E + BitVec.ofNat 64 (4 * (start + n))) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem Ctx.zeroWords {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : Ctx E g m₀ rd wr s)
    (hf : E.toNat + 248 ≤ 2 ^ 32) {start count : Nat} (hn : start + count ≤ 62) :
    WP isa (.block (zeroWords start count)) s fun t => Ctx E g m₀ rd wr t ∧
      Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * count⟩] s.mem t.mem ∧
      ∀ j < count, t.mem.readW (State.addr E + BitVec.ofNat 64 (4 * (start + j))) 32 = 0 := by
  refine WP.mono (zeroWords_ok hc.sp hf (by rw [hc.wr]; exact List.mem_cons_self) start count hn)
    fun t ht => ⟨?_, ht.frame, ht.words⟩
  refine hc.of_frame ht.step.rd ht.step.wr ht.step.sp ?_ ht.frame ?_
  · intro r hr _
    apply ht.step.regs
    · rintro rfl; simp [preserved] at hr
    · rintro rfl; simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))

end VG.Proof.Ed25519.Arm.Whole
