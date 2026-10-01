import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapSaved

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def finish (u : State) : State := popped .lr 4 (popped .r12 4 (freed 24 (freed 248 u)))

theorem finish_mem (u : State) : (finish u).mem = u.mem := rfl
theorem finish_sp (u : State) : (finish u).sp = u.sp + 280#32 := by
  change u.sp + 248#32 + 24#32 + 4#32 + 4#32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem finish_gpr (u : State) {r : Reg} (h12 : r ≠ .r12) (hl : r ≠ .lr) :
    (finish u).gpr r = u.gpr r := by
  rw [finish, popped_gpr hl, popped_gpr h12]
  rfl

theorem finish_lr (u : State) :
    (finish u).gpr .lr = u.mem.readW (State.addr (u.sp + 276#32)) 32 := by
  change u.mem.readW (State.addr (u.sp + 248#32 + 24#32 + 4#32)) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem saved_lr {s p : State} {n : Nat} (hsp : 280 ≤ s.sp.toNat) (hp : Saved (entered s) n p) :
    p.mem.readW (State.addr (base s) + 276) 32 = s.gpr .lr := by
  rw [hp.frame.readW (r := ⟨State.addr (base s) + 276, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rw [entered_mem hsp, Mem.readW_writeW_sep ?_ (by decide)]
    · exact Mem.readW_writeW_self32 _ _ _
    · exact Offset.sep _ (by decide) (by decide) (by decide)
  · rintro r hr
    rw [List.mem_singleton.mp hr, entered_sp]
    exact Offset.disjoint _ (d := 276) (e := 248) (by decide) (by decide) (by decide)

theorem wrap_ok {body : Prog isa} (hn : body.noFrames = true) {s : State} {n : Nat}
    (hcount : n ≤ 6) (hsp : 280 ≤ s.sp.toNat)
    (htop : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hr : ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4)
    (hw : ∀ r ∈ s.wr, (stack s).Disjoint r)
    {P : Mem → Mem → BitVec 32 → Prop}
    (hb : ∀ p, Saved (entered s) n p →
      WP isa body (p.withRegions (bodyRd s) (bodyWr s)) fun u =>
        Ctx (base s) s.gpr p.mem (bodyRd s) s.wr u ∧ P p.mem u.mem (u.gpr .r0)) :
    WP isa (wrap n body) s fun t => abiPreserved s t ∧
      ∃ m, Frame [stack s] s.mem m ∧ P m t.mem (t.gpr .r0) := by
  refine WP.frame (by decide) (by change 4 ≤ s.sp.toNat; omega) (by decide) ?_
  refine WP.frame (by decide) ?_ (by decide) ?_
  · change 4 ≤ (s.sp - 4#32).toNat
    rw [BitVec.toNat_sub_of_le (by change 4 ≤ s.sp.toNat; omega)]
    change 4 ≤ s.sp.toNat - 4
    omega
  · refine WP.alloc (by decide) ?_ ?_
    · change 24 ≤ (s.sp - 4#32 - 4#32).toNat
      rw [BitVec.sub_sub]
      change 24 ≤ (s.sp - 8#32).toNat
      rw [BitVec.toNat_sub_of_le (by change 8 ≤ s.sp.toNat; omega)]
      change 24 ≤ s.sp.toNat - 8
      omega
    · refine WP.alloc (by decide) ?_ ?_
      · change 248 ≤ (s.sp - 4#32 - 4#32 - 24#32).toNat
        simp only [BitVec.sub_sub]
        change 248 ≤ (s.sp - 32#32).toNat
        rw [BitVec.toNat_sub_of_le (by change 32 ≤ s.sp.toNat; omega)]
        change 248 ≤ s.sp.toNat - 32
        omega
      · refine WP.seq (WP.mono (enter_save hcount hsp htop hr) fun p hp => ?_)
        refine narrow (hb p hp) ?_ ?_ ?_ hn
        · refine Covers.of_sub fun r hR => ?_
          rw [hp.step.rd, hp.step.wr, entered_wr hsp]
          simp only [bodyRd, bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with (hR | rfl) | (rfl | hR)
          · exact ⟨r, List.mem_append_left _ hR, 0, by simp⟩
          · exact ⟨ARGS (base s), List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp⟩
          · exact ⟨FR (base s), List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
          · exact ⟨r, List.mem_append_right _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR)))), 0, by simp⟩
        · refine Covers.of_sub fun r hR => ?_
          rw [hp.step.wr, entered_wr hsp]
          simp only [bodyWr, List.mem_cons] at hR
          rcases hR with rfl | hR
          · exact ⟨FR (base s), List.mem_cons_self, 0, by simp⟩
          · exact ⟨r, by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hR))), 0, by simp⟩
        · intro u _ _ _ _ hbody
          obtain ⟨hc, ho⟩ := hbody
          have lr : u.mem.readW (State.addr (base s) + 276) 32 = s.gpr .lr := by
            rw [hc.frame.readW (r := ⟨State.addr (base s) + 276, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
            · exact saved_lr hsp hp
            · intro r hR
              simp only [List.mem_append, List.mem_singleton] at hR
              rcases hR with hR | rfl
              · exact (hw r hR).sub_left (Offset.sub_base _ (by decide : 276 + 4 ≤ 280))
              · exact Offset.disjoint_base _ (by decide) (by decide)
          change abiPreserved s (finish (u.withRegions p.rd p.wr)) ∧ _
          refine ⟨⟨?_, ?_⟩, p.mem, saved_frame hsp hp, ?_⟩
          · intro r hR
            by_cases hl : r = .lr
            · subst r
              rw [finish_lr, State.withRegions_sp, hc.sp,
                addr_add (by have hb := base_top hsp; have hi := s.sp.isLt; omega)]
              exact lr
            · rw [finish_gpr _ (by intro h; subst r; simp [preserved] at hR) hl]
              exact hc.cs r hR hl
          · rw [finish_sp, State.withRegions_sp, hc.sp]
            exact BitVec.sub_add_cancel _ _
          · change P p.mem (finish (u.withRegions p.rd p.wr)).mem
              ((finish (u.withRegions p.rd p.wr)).gpr .r0)
            rw [finish_mem, finish_gpr _ (by decide) (by decide)]
            exact ho

end VG.Proof.Ed25519.Arm.Whole
