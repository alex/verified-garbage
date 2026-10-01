import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapGeometry

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
