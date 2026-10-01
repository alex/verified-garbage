import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure EntryStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  regs : ∀ r, r ≠ .x15 → t.gpr r = s.gpr r

theorem EntryStep.refl (s : State) : EntryStep s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
theorem EntryStep.trans {s t u : State} (h : EntryStep s t) (h' : EntryStep t u) : EntryStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.v.trans h.v,
    fun r hn => (h'.regs r hn).trans (h.regs r hn)⟩

theorem argReg_ne15 (j : Nat) : argReg j ≠ .x15 := by
  unfold argReg
  split <;> decide

theorem saveWord_ok {s : State} {j : Nat} (hj : j < 6)
    (hw : InRegions s.wr (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 8) :
    WP isa (.block (saveWord j)) s fun t => EntryStep s t ∧
      t.mem = s.mem.writeW (s.sp + BitVec.ofNat 64 (256 + 8 * j)) (s.gpr (argReg j)) := by
  have hs : 256 + 8 * j < 4096 := by omega
  apply WP.of_runBlock
  simp only [saveWord, runBlock_cons, runStep_some, runBlock_nil, exec, State.store, Size.bits,
    Size.bytes, State.read, addr, hs, RegUpd.gpr_write, RegUpd.wr_write,
    RegUpd.mem_write, RegUpd.sp_write, argReg_ne15, BitVec.setWidth_eq,
    Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, ite_false,
    Option.bind_some, hw, BitVec.add_zero, Mem.writeW, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
  intro r hn
  simp only [RegUpd.gpr_write, hn, ite_false]

structure Saved (s : State) (n : Nat) (t : State) : Prop where
  step : EntryStep s t
  frame : Frame [⟨s.sp + 256, 48⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (s.sp + BitVec.ofNat 64 (256 + 8 * j)) 64 = s.gpr (argReg j)

theorem savePrefix_ok {s : State} (hw : (⟨s.sp, 320⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 6, WP isa (.block ((List.range n).flatMap saveWord)) s (Saved s n)
  | 0, _ => WP.block_nil ⟨.refl s, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (savePrefix_ok hw n (by omega)) fun u hu => ?_
    have uw : InRegions u.wr (u.sp + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [hu.step.sp, hu.step.wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    refine WP.mono (saveWord_ok (by omega) uw) fun t ⟨ht, mt⟩ => ?_
    rw [hu.step.sp, hu.step.regs _ (argReg_ne15 n)] at mt
    refine ⟨hu.step.trans ht, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem saveArgs_ok {s : State} (hw : (⟨s.sp, 320⟩ : Region) ∈ s.wr) :
    WP isa (.block saveArgs) s (Saved s 6) := savePrefix_ok hw 6 (by decide)

end VG.Proof.Ed25519.AArch64.Whole
