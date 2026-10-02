import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateCall

/-!
# Streaming RC2-CBC on x86 (32-bit): the update functions are correct

Untrusted: everything here is checked by Lean. From the state before the
call (`Mid`): with no complete block, the data is already appended to the
pending bytes; otherwise the CBC function runs on `out`. Then our caller's
registers are restored, and `update_post_short` or `update_post_long`
gives the contract's postcondition.
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem update_correct (d : Spec.Rc2.Direction) (s₀ : State) (hs : (updateContract d).pre s₀) :
    WP isa (update d) s₀ (fun s' => abiPreserved s₀ s' ∧ (updateContract d).post s₀ s') := by
  have hp := pre_of hs
  have hOe := hp.O_eq
  have hpl := hp.p_lt
  have hlo := hp.sp_lo
  have hOe' : (arg s₀ 5).toNat = (p s₀ + len s₀) / 8 * 8 := hp.O_eq
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  have retStk : (retR s₀).Disjoint (stkR s₀) := by
    show Region.Disjoint ⟨(E s₀).setWidth 64, 4⟩ ⟨(E s₀ - BitVec.ofNat 32 40).setWidth 64, 40⟩
    rw [Taint.sub_setWidth hlo]; exact Offset.base_disjoint_below _ (by decide)
  -- What `Common` keeps.
  have sep3 {r : Region} (h₁ : r.Disjoint (pendR s₀)) (h₂ : r.Disjoint (oR s₀)) (h₃ : r.Disjoint (scR s₀)) :
      ∀ x ∈ [pendR s₀, oR s₀, scR s₀], r.Disjoint x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    exacts [h₁, h₂, h₃]
  have schC : ∀ x ∈ [pendR s₀, oR s₀, scR s₀], (schR s₀).Disjoint x :=
    sep3 Pre.sch_pend (hp.c_o.sub_left Pre.sch_sub) (hp.c_s.sub_left Pre.sch_sub)
  have ivC : ∀ x ∈ [pendR s₀, oR s₀, scR s₀], (ivR s₀).Disjoint x :=
    sep3 Pre.iv_pend (hp.c_o.sub_left Pre.iv_sub) (hp.c_s.sub_left Pre.iv_sub)
  have retC : ∀ x ∈ [pendR s₀, oR s₀, scR s₀], (retR s₀).Disjoint x :=
    sep3 (hp.sep_pend _ (by simp)) hp.r_o hp.r_s
  -- What the call keeps.
  have sep4 {r : Region} (h₁ : r.Disjoint (ivR s₀)) (h₂ : r.Disjoint (oR s₀))
      (h₃ : r.Disjoint ⟨sA s₀, 512⟩) (h₄ : r.Disjoint (stkR s₀)) :
      ∀ x ∈ [ivR s₀, oR s₀, ⟨sA s₀, 512⟩, stkR s₀], r.Disjoint x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    exacts [h₁, h₂, h₃, h₄]
  have buf : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
  rw [update]
  refine WP.seq (WP.mono (head_ok hp) fun s hm => ?_)
  have hc := hm.common
  refine WP.seq (WP.ite _ hm.zf (fun h => WP.block_nil ?_) (fun h => ?_))
  · -- No complete block.
    have h0 : O s₀ = 0 := by simpa using h
    refine restore_ok hp hm.ebx hc.wr hc.ebx hc.esi fun t mt tb ts to => ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact tb
      · exact ts
      · rw [to _ (by decide) (by decide)]; exact hc.edi
      · rw [to _ (by decide) (by decide)]; exact hc.ebp
      · rw [to _ (by decide) (by decide)]; exact hc.esp
    · rw [mt]; exact hc.frame.readW (Region.contains_self _ _) retC (by decide)
    · have post := update_post_short (m := s₀.mem) (m' := t.mem) (ctx := cA s₀) (data := dA s₀)
        (out := oA s₀) (d := d) (p := p s₀) (len := len s₀) (by omega)
        (by rw [mt]; exact Proof.Rc2.scheduleAt_frame hc.frame _ schC)
        (by rw [mt]; exact Proof.Rc2.blockAt_frame hc.frame _ ivC)
        (by rw [mt]; exact hm.short h0)
      simp only [updateContract]
      rw [hOe']
      exact post
  · -- The CBC function on `out`.
    have h0 : O s₀ ≠ 0 := by simpa using h
    refine cbcCall_ok hp hm d fun s' rd wr cs f c₁ c₂ => ?_
    have word {e : Nat} (he : 512 ≤ e) (he' : e + 4 ≤ 576) :
        s'.mem.readW (addr (scr s₀) e) 32 = s.mem.readW (addr (scr s₀) e) 32 := by
      refine f.readW (Region.contains_self _ _) (sep4 ?_ ?_ ?_ ?_) (by decide)
      · exact (hp.c_s.sub_left Pre.iv_sub).symm.sub_left (hp.scr_sub he')
      · exact hp.o_s.symm.sub_left (hp.scr_sub he')
      · rw [hp.scr_addr he']; exact Offset.disjoint_base _ he (by omega)
      · exact hp.k_s.symm.sub_left (hp.scr_sub he')
    refine restore_ok hp (by rw [cs .ebx (by simp [calleeSaved])]; exact hm.ebx) (wr.trans hc.wr)
      (by rw [word (by decide) (by decide)]; exact hc.ebx) (by rw [word (by decide) (by decide)]; exact hc.esi)
      fun t mt tb ts to => ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact tb
      · exact ts
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.edi
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.ebp
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.esp
    · rw [mt, f.readW (Region.contains_self _ _) (sep4 (hp.r_c.sub_right Pre.iv_sub) hp.r_o
        (hp.r_s.sub_right buf) retStk) (by decide)]
      exact hc.frame.readW (Region.contains_self _ _) retC (by decide)
    · have e8 : (p s₀ + len s₀) / 8 * 8 / 8 = (p s₀ + len s₀) / 8 := Nat.mul_div_cancel _ (by decide)
      have pendS : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 136, (p s₀ + len s₀) % 8⟩ (pendR s₀) :=
        Region.sub_prefix (by have := Nat.mod_lt (p s₀ + len s₀) (by decide : 0 < 8); omega)
      have out := hm.out h0
      have pend := hm.pend h0
      rw [hOe] at out pend c₁ c₂
      rw [e8] at c₁ c₂
      have post := update_post_long (m := s₀.mem) (m₁ := s.mem) (m' := t.mem) (ctx := cA s₀) (data := dA s₀)
        (out := oA s₀) (d := d) (p := p s₀) (len := len s₀) hpl (by omega) out
        (Proof.Rc2.scheduleAt_frame hc.frame _ schC) (Proof.Rc2.blockAt_frame hc.frame _ ivC)
        (by
          show Spec.Rc2.bytesAt t.mem (cA s₀ + BitVec.ofNat 64 136) _ = _
          rw [mt, Proof.Rc2.bytesAt_frame f _ _ (by omega) (sep4
            ((Pre.iv_pend).symm.sub_left pendS) ((hp.c_o.sub_left Pre.pend_sub).sub_left pendS)
            (((hp.c_s.sub_left Pre.pend_sub).sub_left pendS).sub_right buf)
            ((hp.k_c.sub_right Pre.pend_sub).symm.sub_left pendS))]
          exact pend)
        (by
          rw [mt]
          exact Proof.Rc2.scheduleAt_frame f _ (sep4 Pre.sch_iv (hp.c_o.sub_left Pre.sch_sub)
            ((hp.c_s.sub_left Pre.sch_sub).sub_right buf) (hp.k_c.sub_right Pre.sch_sub).symm))
        (by rw [mt]; exact c₁) (by rw [mt]; exact c₂)
      simp only [updateContract]
      rw [hOe']
      exact post

end VG.Proof.Rc2.X86.Stream.Update
