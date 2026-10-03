import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout

/-! Merged from `Proof.Ed25519.AArch64.Whole.Entry`. -/
section
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
end

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

abbrev base (s : State) : Addr := s.sp - 336
abbrev entered (s : State) : State := allocated 320 (pushed .x30 s)
abbrev bodyRd (s : State) : List Region := s.rd ++ [ARGS (base s)]
abbrev bodyWr (s : State) : List Region := FR (base s) :: s.wr

theorem entered_sp (s : State) : (entered s).sp = base s := by
  change s.sp - 16 - 320#64 = s.sp - 336
  rw [BitVec.sub_sub]
  rfl

theorem base_lr (s : State) : base s + 320 = s.sp - 16 := by
  change s.sp - 336#64 + 320#64 = s.sp - 16#64
  rw [show (336#64) = 16#64 + 320#64 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_return (s : State) : base s + 320 + 16 = s.sp := by
  rw [base_lr, BitVec.sub_add_cancel]

theorem entered_wr (s : State) : (entered s).wr = ⟨base s, 320⟩ :: ⟨s.sp - 16, 16⟩ :: s.wr := by
  change ⟨(entered s).sp, 320⟩ :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [entered_sp]

/-- The frame of a callee of the body is in the 352 bytes below the stack pointer. -/
theorem ck_sub (s : State) : Region.Sub (CK (base s)) (below s.sp 352) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have e : s.sp - BitVec.ofNat 64 336 - BitVec.ofNat 64 16 = s.sp - BitVec.ofNat 64 352 :=
    Offset.sub_sub_ofNat _ _ _
  change (x - (s.sp - BitVec.ofNat 64 336 - BitVec.ofNat 64 16)).toNat + 1 ≤ 16 at hx
  rw [e] at hx
  omega

theorem stk_sub (s : State) : Region.Sub ⟨base s, 336⟩ (below s.sp 352) :=
  below_sub (by decide) (by decide)

theorem base_16 {s : State} (h : 352 ≤ s.sp.toNat) : 16 ≤ (base s).toNat := by
  change 16 ≤ (s.sp - 336#64).toNat
  rw [BitVec.toNat_sub_of_le (by change 336 ≤ s.sp.toNat; omega)]
  change 16 ≤ s.sp.toNat - 336
  omega

theorem saved_ctx {s p : State} (hs : Saved (entered s) 6 p) :
    Ctx (base s) s.gpr s.v p.mem (bodyRd s) s.wr (p.withRegions (bodyRd s) (bodyWr s)) := by
  refine ⟨rfl, rfl, hs.step.sp.trans (entered_sp s), ?_, ?_, Frame.refl _ _⟩
  · intro r hr _
    exact hs.step.regs r (by intro h; subst r; simp [preserved] at hr)
  · intro r _
    change (p.v r).extractLsb' 0 64 = _
    rw [hs.step.v]
    rfl

theorem saved_frame {s p : State} (hs : Saved (entered s) 6 p) :
    Frame [below s.sp 336] s.mem p.mem := by
  have hp : Frame [below s.sp 336] s.mem (entered s).mem := by
    exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _
      (below_frame_contains s.sp 320 (by decide))
  refine hp.trans (Frame.sub hs.frame fun r hr => ?_)
  rw [List.mem_singleton.mp hr, entered_sp]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : 256 + 48 ≤ 336)⟩

theorem saved_words {s p : State} (hs : Saved (entered s) 6 p) {j : Nat} (hj : j < 6) :
    p.mem.readW (base s + BitVec.ofNat 64 (256 + 8 * j)) 64 = s.gpr (argReg j) := by
  have h := hs.words j hj
  rw [entered_sp] at h
  exact h

/-- The complete operations share one LR save and a 320-byte allocation.
Their body sees writable locals and readonly saved arguments, and its
callees' frames take 16 more bytes below them. -/
theorem wrap_ok {body : Prog isa} (hn : body.aarch64Depth ≤ 1) {s : State}
    (hsp : 352 ≤ s.sp.toNat)
    (hw : ∀ r ∈ s.wr, (below s.sp 352).Disjoint r)
    {P : Mem → Mem → BitVec 64 → Prop}
    (hb : ∀ p, Saved (entered s) 6 p →
      WP isa body (p.withRegions (bodyRd s) (bodyWr s)) fun u =>
        Ctx (base s) s.gpr s.v p.mem (bodyRd s) s.wr u ∧ P p.mem u.mem (u.gpr .x0)) :
    WP isa (wrap body) s fun t => abiPreserved s t ∧
      ∃ m, Frame [below s.sp 336] s.mem m ∧ P m t.mem (t.gpr .x0) := by
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · change 320 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by change 16 ≤ s.sp.toNat; omega)]
    change 320 ≤ s.sp.toNat - 16
    omega
  · refine WP.seq (WP.mono (saveArgs_ok (s := entered s) (by simp [entered_wr, entered_sp])) fun p hp => ?_)
    refine WP.narrowF (hb p hp) ?_ ?_ ?_ (by omega)
    · refine Covers.of_sub fun r hr => ?_
      simp only [bodyRd, bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hp.step.rd, hp.step.wr, entered_wr]
      rcases hr with (hr | rfl) | (rfl | hr)
      · exact ⟨r, List.mem_append_left _ hr, 0, by simp⟩
      · exact ⟨⟨base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 256, rfl, by change 256 + 48 ≤ 320; decide⟩
      · exact ⟨⟨base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
      · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), 0, by simp⟩
    · refine Covers.of_sub fun r hr => ?_
      rw [hp.step.wr, entered_wr]
      simp only [bodyWr, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨⟨base s, 320⟩, List.mem_cons_self, 0, by simp⟩
      · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), 0, by simp⟩
    · intro u _ _ hsu hf ⟨hc, ho⟩
      have usp : u.sp = base s := hc.sp
      have lr_sep : ∀ r ∈ bodyWr s ++ [below p.sp (16 * body.aarch64Depth)],
          (⟨s.sp - 16, 16⟩ : Region).Disjoint r := by
        intro r hr
        simp only [bodyWr, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | hr | rfl
        · rw [← base_lr]
          exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (hw r hr).sub_left (below_sub (by decide : 16 ≤ 352) (by decide))
        · rw [hp.step.sp, entered_sp, ← base_lr]
          exact (Offset.below_disjoint (base s) (m := 16 * body.aarch64Depth) (l := 336) (by omega)).symm.sub_left
            (Offset.sub_base _ (by decide : 320 + 16 ≤ 336))
      have lr : u.mem.read (base s + 320) 8 = s.gpr .x30 := by
        rw [base_lr, hf.read (r := ⟨s.sp - 16, 16⟩) (by simp [Region.Contains]) lr_sep (by decide)]
        rw [hp.frame.read (r := ⟨s.sp - 16, 16⟩) (by simp [Region.Contains]) ?_ (by decide)]
        · exact read_write_self _ _ _
        · rintro r hr
          rw [List.mem_singleton.mp hr, entered_sp, ← base_lr]
          exact Offset.disjoint _ (d := 320) (e := 256) (by decide) (by decide) (by decide)
      refine ⟨⟨?_, ?_, ?_⟩, p.mem, saved_frame hp, ?_⟩
      · intro r hr
        change ((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).gpr r = _
        rw [usp]
        change ((freed 320 u).write .x .x30 (u.mem.read (base s + (320 : BitVec 64)) 8)).gpr r = _
        rw [lr, RegUpd.gpr_write]
        by_cases h30 : r = .x30
        · subst r; simp only [ite_true, BitVec.setWidth_eq]
        · simp only [h30, ite_false]
          exact hc.cs r hr h30
      · change u.sp + 320#64 + 16 = s.sp
        rw [usp]
        exact base_return s
      · intro r hr
        change (((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).v r).extractLsb' 0 64 = _
        rw [RegUpd.v_write]
        exact hc.vs r hr
      · change P p.mem ((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).mem
          (((freed 320 u).write .x .x30 (u.mem.read (u.sp + 320#64) 8)).gpr .x0)
        rw [RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ _ (by decide)]
        exact ho

end VG.Proof.Ed25519.AArch64.Whole
