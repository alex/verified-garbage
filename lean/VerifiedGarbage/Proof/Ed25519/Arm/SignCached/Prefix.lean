import VerifiedGarbage.Impl.Ed25519.Arm.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Spec.Ed25519.Contract

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : PrefixStep s t) (h' : PrefixStep t u) : PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hr : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 8) :
    WP isa (.block (copyWord k)) s fun t => PrefixStep s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (56 + 4 * k))
        (s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 32) := by
  have ae : State.addr (E + BitVec.ofNat 32 (216 + 4 * k)) = State.addr E + BitVec.ofNat 64 (216 + 4 * k) :=
    addr_add (by omega)
  have ad : State.addr (E + BitVec.ofNat 32 (56 + 4 * k)) = State.addr E + BitVec.ofNat 64 (56 + 4 * k) :=
    addr_add (by omega)
  have source : InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, List.mem_append_right _ hr, Offset.contains_base _ (by omega) (by omega)⟩
  have dest : InRegions s.wr (State.addr E + BitVec.ofNat 64 (56 + 4 * k)) 4 :=
    ⟨⟨State.addr E, 248⟩, hr, Offset.contains_base _ (by omega) (by omega)⟩
  have hl : exec (.ldrSp .r0 (216 + 4 * k)) s =
      some (s.setReg .r0 (s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * k)) 32)) := by
    simp only [exec, show 216 + 4 * k < 4096 from by omega, ite_true,
      State.load32, he, ae, source, Option.map_some]
  have ha {t : State} : exec (.addSp .r12 0) t = some (t.setReg .r12 t.sp) := by
    simp only [exec, show 0 < 256 from by decide, ite_true, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_setReg]
  rw [exec_str (by omega) (by
    simpa only [RegUpd.wr_setReg, RegUpd.gpr_setReg_self, he, ad] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h12
    simp only [RegUpd.gpr_setReg, h0, h12, ite_false]
  · simp only [RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, he, ad]

structure PrefixInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : PrefixStep s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 56, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (State.addr E + BitVec.ofNat 64 (56 + 4 * j)) 32 =
    s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * j)) 32

theorem copyPrefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap copyWord)) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hf hw n (by omega)) fun u hu => ?_
    refine WP.mono (copyWord_ok (hu.step.sp.trans he) hf (hu.step.wr ▸ hw) (by omega : n < 8))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * n)) 32 =
        s.mem.readW (State.addr E + BitVec.ofNat 64 (216 + 4 * n)) 32 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega) (by omega) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := State.addr E + BitVec.ofNat 64 (56 + 4 * j))
          (b := State.addr E + BitVec.ofNat 64 (56 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem prefix_ok {s : State} {E : BitVec 32} (he : s.sp = E)
    (hf : E.toNat + 248 ≤ 2 ^ 32) (hw : (⟨State.addr E, 248⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => PrefixStep s t ∧
      Frame [⟨State.addr E + 56, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr E + 56) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr E + 216) 32 := by
  refine WP.mono (copyPrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ed : State.addr E + 56 + BitVec.ofNat 64 i =
      (State.addr E + BitVec.ofNat 64 (56 + 4 * (i / 4))) + BitVec.ofNat 64 (i % 4) := by
    change State.addr E + BitVec.ofNat 64 56 + BitVec.ofNat 64 i = _
    rw [Offset.add_add, Offset.add_add]
    exact congrArg (fun n => State.addr E + BitVec.ofNat 64 n) (by omega)
  have es : State.addr E + 216 + BitVec.ofNat 64 i =
      (State.addr E + BitVec.ofNat 64 (216 + 4 * (i / 4))) + BitVec.ofNat 64 (i % 4) := by
    change State.addr E + BitVec.ofNat 64 216 + BitVec.ofNat 64 i = _
    rw [Offset.add_add, Offset.add_add]
    exact congrArg (fun n => State.addr E + BitVec.ofNat 64 n) (by omega)
  rw [ed, es, Mem.readW_byte t.mem _ (i := i % 4) (Nat.mod_lt _ (by decide)),
    Mem.readW_byte s.mem _ (i := i % 4) (Nat.mod_lt _ (by decide)), ht.words (i / 4) (by omega)]

end VG.Proof.Ed25519.Arm.SignCached
