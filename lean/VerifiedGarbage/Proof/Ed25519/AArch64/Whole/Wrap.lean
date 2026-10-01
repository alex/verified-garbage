import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Entry
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout

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
Their body sees writable locals and readonly saved arguments. -/
theorem wrap_ok {body : Prog isa} (hn : body.noFrames = true) {s : State}
    (hsp : 336 ≤ s.sp.toNat)
    (hw : ∀ r ∈ s.wr, (below s.sp 336).Disjoint r)
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
    refine WP.narrow (hb p hp) ?_ ?_ ?_ hn
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
      have lr_sep : ∀ r ∈ bodyWr s, (⟨s.sp - 16, 16⟩ : Region).Disjoint r := by
        intro r hr
        simp only [bodyWr, List.mem_cons] at hr
        rcases hr with rfl | hr
        · rw [← base_lr]
          exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (hw r hr).sub_left (below_sub (by decide : 16 ≤ 336) (by decide))
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
