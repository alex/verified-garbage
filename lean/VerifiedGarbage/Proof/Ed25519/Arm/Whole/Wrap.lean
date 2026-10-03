import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Framework.Arm.Frame

/-! Merged from `Proof.Ed25519.Arm.Whole.WrapSaved`. -/
section
/-! Merged from `Proof.Ed25519.Arm.Whole.WrapGeometry`. -/
section
namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev base (s : State) : BitVec 32 := s.sp - 280
abbrev entered (s : State) : State := allocated 248 (allocated 24 (pushed [.r12] (pushed [.lr] s)))
abbrev bodyRd (s : State) : List Region := s.rd ++ [ARGS (base s)]
abbrev bodyWr (s : State) : List Region := FR (base s) :: s.wr
abbrev stack (s : State) : Region := ⟨State.addr (base s), 280⟩

theorem entered_sp (s : State) : (entered s).sp = base s := by
  change s.sp - 4#32 - 4#32 - 24#32 - 248#32 = s.sp - 280
  simp only [BitVec.sub_sub]
  rfl

theorem base_args (s : State) : base s + 248#32 = s.sp - 4#32 - 4#32 - 24#32 := by
  simp only [base, BitVec.sub_sub]
  change s.sp - 280#32 + 248#32 = s.sp - 32#32
  rw [show (280#32) = 32#32 + 248#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_pad (s : State) : base s + 272#32 = s.sp - 4#32 - 4#32 := by
  simp only [base, BitVec.sub_sub]
  change s.sp - 280#32 + 272#32 = s.sp - 8#32
  rw [show (280#32) = 8#32 + 272#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_lr (s : State) : base s + 276#32 = s.sp - 4#32 := by
  change s.sp - 280#32 + 276#32 = s.sp - 4#32
  rw [show (280#32) = 4#32 + 276#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_top {s : State} (h : 280 ≤ s.sp.toNat) : (base s).toNat + 280 = s.sp.toNat := by
  change (s.sp - 280#32).toNat + 280 = s.sp.toNat
  rw [BitVec.toNat_sub_of_le (by change 280 ≤ s.sp.toNat; exact h)]
  change s.sp.toNat - 280 + 280 = s.sp.toNat
  omega

theorem base_addr {s : State} (h : 280 ≤ s.sp.toNat) :
    State.addr (base s) = State.addr s.sp - 280 := by
  have e : base s + 280#32 = s.sp := BitVec.sub_add_cancel _ _
  have ha := addr_add (a := base s) (k := 280) (by rw [base_top h]; exact s.sp.isLt)
  rw [e] at ha
  rw [ha]
  exact (BitVec.add_sub_cancel _ _).symm

theorem entered_wr {s : State} (h : 280 ≤ s.sp.toNat) :
    (entered s).wr = FR (base s) :: ARGS (base s) ::
      ⟨State.addr (base s) + 272, 4⟩ :: ⟨State.addr (base s) + 276, 4⟩ :: s.wr := by
  have hb := base_top h
  have hs := s.sp.isLt
  change ⟨State.addr (entered s).sp, 248⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32 - 24#32), 24⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32), 4⟩ :: ⟨State.addr (s.sp - 4#32), 4⟩ :: s.wr = _
  rw [entered_sp, ← base_args, ← base_pad, ← base_lr,
    addr_add (by omega), addr_add (by omega), addr_add (by omega)]
  rfl

theorem entered_mem {s : State} (h : 280 ≤ s.sp.toNat) :
    (entered s).mem = (s.mem.writeW (State.addr (base s) + 276) (s.gpr .lr)).writeW
      (State.addr (base s) + 272) (s.gpr .r12) := by
  have hb := base_top h
  have hs := s.sp.isLt
  change (s.mem.writeW (State.addr (s.sp - 4#32)) (s.gpr .lr)).writeW
    (State.addr (s.sp - 4#32 - 4#32)) (s.gpr .r12) = _
  rw [← base_pad, ← base_lr, addr_add (by omega), addr_add (by omega)]
  rfl

end VG.Proof.Ed25519.Arm.Whole
end

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

theorem entered_frame {s : State} (h : 280 ≤ s.sp.toNat) :
    Frame [stack s] s.mem (entered s).mem := by
  rw [entered_mem h]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide : 276 + 4 ≤ 280) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide : 272 + 4 ≤ 280) (by decide))

theorem saved_ctx {s p : State} {n : Nat} (hs : Saved (entered s) n p) :
    Ctx (base s) s.gpr p.mem (bodyRd s) s.wr (p.withRegions (bodyRd s) (bodyWr s)) := by
  refine ⟨rfl, rfl, hs.step.sp.trans (entered_sp s), ?_, Frame.refl _ _⟩
  intro r hr hlr
  exact hs.step.regs r (by intro h; subst r; simp [preserved] at hr) hlr

theorem saved_frame {s p : State} {n : Nat} (h : 280 ≤ s.sp.toNat) (hs : Saved (entered s) n p) :
    Frame [stack s] s.mem p.mem := by
  refine (entered_frame h).trans (Frame.sub hs.frame fun r hr => ?_)
  rw [List.mem_singleton.mp hr, entered_sp]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide : 248 + 24 ≤ 280)⟩

def originalWord (s : State) (j : Nat) : BitVec 32 :=
  if j < 4 then s.gpr (argReg j)
  else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 32

theorem input_entered {s : State} {j : Nat} (hs : 280 ≤ s.sp.toNat)
    (_hj : j < 6) (ht : s.sp.toNat + 4 * (j - 4) < 2 ^ 32) :
    inputWord (entered s) j = originalWord s j := by
  unfold inputWord originalWord
  split
  · rfl
  · have e : (entered s).sp + BitVec.ofNat 32 (280 + 4 * (j - 4)) =
        s.sp + BitVec.ofNat 32 (4 * (j - 4)) := by
      rw [entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc]
      change s.sp - 280#32 + 280#32 + _ = _
      rw [BitVec.sub_add_cancel]
    rw [e]
    have hb := base_top hs
    have ae : State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4))) =
        State.addr (base s) + BitVec.ofNat 64 (280 + 4 * (j - 4)) := by
      rw [← e, entered_sp, addr_add (by omega)]
    refine (entered_frame hs).readW (r := ⟨State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4))), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr, ae]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem saved_words {s p : State} {n j : Nat} (hs : 280 ≤ s.sp.toNat)
    (hn : n ≤ 6) (ht : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hp : Saved (entered s) n p) (hj : j < n) :
    p.mem.readW (State.addr (base s) + BitVec.ofNat 64 (248 + 4 * j)) 32 = originalWord s j := by
  have h := hp.words j hj
  rw [entered_sp] at h
  refine h.trans (input_entered hs (by omega) ?_)
  by_cases h4 : j < 4
  · have hi := s.sp.isLt
    omega
  · omega

/-- Widen permissions around a body while retaining its precise write frame. -/
theorem narrow {c : Prog isa} {s : State} {rd wr : List Region} {P Q : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (hQ : ∀ u, u.rd = rd → u.wr = wr → u.sp = s.sp → Frame wr s.mem u.mem → P u →
      Q (u.withRegions s.rd s.wr)) (hn : c.noFrames = true) : WP isa c s Q := by
  obtain ⟨t, u, he, hp⟩ := h
  obtain ⟨hr, hw', hs, hf⟩ := Exec.regions he hn
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) hc hw
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  exact ⟨t, _, he', hQ u hr hw' hs hf hp⟩

theorem enter_save {s : State} {n : Nat} (hcount : n ≤ 6) (hsp : 280 ≤ s.sp.toNat)
    (htop : s.sp.toNat + 4 * (n - 4) ≤ 2 ^ 32)
    (hr : ∀ j < n, 4 ≤ j → InRegions (s.rd ++ s.wr)
      (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4) :
    WP isa (.block (saveArgs n)) (entered s) (Saved (entered s) n) := by
  have he : (entered s).sp.toNat + 280 + 4 * (n - 4) ≤ 2 ^ 32 := by
    rw [entered_sp, base_top hsp]
    exact htop
  have ha : (⟨State.addr (entered s).sp + 248, 24⟩ : Region) ∈ (entered s).wr := by
    rw [entered_sp, entered_wr hsp]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hsread : ∀ j < n, 4 ≤ j → InRegions ((entered s).rd ++ (entered s).wr)
      (State.addr ((entered s).sp + BitVec.ofNat 32 (280 + 4 * (j - 4)))) 4 := by
    intro j hj h4
    rw [entered_sp, BitVec.ofNat_add, ← BitVec.add_assoc]
    change InRegions _ (State.addr (s.sp - 280#32 + 280#32 + _)) _
    rw [BitVec.sub_add_cancel]
    obtain ⟨r, hR, hC⟩ := hr j hj h4
    refine ⟨r, ?_, hC⟩
    change r ∈ s.rd ++ (entered s).wr
    rw [entered_wr hsp]
    exact List.mem_append.mpr (List.mem_append.mp hR |>.imp id fun h =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
  exact saveArgs_ok n hcount he ha hsread

end VG.Proof.Ed25519.Arm.Whole
end

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
