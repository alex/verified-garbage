import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Steps

/-! # Streaming RC2-CBC on x86-64: an update without a complete block -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- With `out_len = 0` (so `pending_len + len < 8`), from a state `t` that
differs from the entry state `s` only in its flags. -/
theorem short_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hz : (s.gpr .r9).toNat = 0) (t : State) (ht : Keep [] s t) :
    WP isa short t (fun s' => gprPreserved s s' ∧ (updateContract d).post s s') := by
  obtain ⟨_, _, hrd, hwr, ctxData, _, _, _, _, _, _, _, _, retCtx, _, _, _, _,
    _, _, _, _, _, _, _, _, _, hp, hN⟩ := hs
  have hshort : (s.gpr .rsi).toNat + (s.gpr .rcx).toNat < 8 := by omega
  obtain ⟨t₁, run₁, rax₁, keep₁⟩ := shortArgs_ok t
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have g₁ (r : Reg) (hr : r ≠ .rax) : t₁.gpr r = s.gpr r := (keep₁.reg r (by simpa using hr)).trans (ht.reg r (by simp))
  have rd₁ : t₁.rd = s.rd := keep₁.rd.trans ht.rd
  have wr₁ : t₁.wr = s.wr := keep₁.wr.trans ht.wr
  have mem₁ : t₁.mem = s.mem := keep₁.mem.trans ht.mem
  -- The destination, `ctx + 136 + pending_len`.
  have hD : t₁.gpr .rax + BitVec.ofNat 64 136 =
      s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat) := by
    rw [rax₁, ht.reg _ (by simp), ht.reg _ (by simp), toNat_eq (s.gpr .rsi), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (s.gpr .rsi).isLt, Offset.add_add, Nat.add_comm]
  have dstSub : Region.Sub ⟨s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat), (s.gpr .rcx).toNat⟩
      ⟨s.gpr .rdi, 144⟩ := Offset.sub_base _ (by omega)
  apply WP.mono (copy_ok t₁ (src := .rdx) (dst := .rax) (cnt := .rcx) (sd := 0) (dd := 136)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := s.gpr .rdx) (D := s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat))
    (n := (s.gpr .rcx).toNat) (by rw [g₁ _ (by decide)]; exact BitVec.add_zero _) hD
    (by rw [g₁ _ (by decide)]; exact toNat_eq _) (s.gpr .rcx).isLt
    (fun i hi => by
      rw [rd₁, wr₁, hrd]
      exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by
      rw [wr₁, hwr, Offset.add_add]
      exact ⟨⟨s.gpr .rdi, 144⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (ctxData.symm.sub_right dstSub))
  rintro s' ⟨mem', g', rd', wr'⟩
  rw [mem₁] at mem'
  have frame : Frame [⟨s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat), (s.gpr .rcx).toNat⟩]
      s.mem s'.mem := by
    rw [mem']
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hr' : r ≠ .rax ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      revert hr; revert r; decide
    rw [g' r hr'.2.1 hr'.2.2, g₁ r hr'.1]
  · apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (hn := by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact retCtx.sub_right dstSub
  · show Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d _ = _ ∧ _
    rw [hN]
    refine update_post_short hshort ?_ ?_ ?_
    · exact scheduleAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega))
    · rw [show s.gpr .rdi + 128 = s.gpr .rdi + BitVec.ofNat 64 128 from rfl]
      exact blockAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega))
    · rw [show s.gpr .rdi + 136 = s.gpr .rdi + BitVec.ofNat 64 136 from rfl, bytesAt_add,
        show s.gpr .rdi + BitVec.ofNat 64 136 + BitVec.ofNat 64 (s.gpr .rsi).toNat =
          s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat) from Offset.add_add _ _ _,
        Proof.Rc2.bytesAt_frame frame _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)),
        mem']
      congr 1
      have h := bytesAt_writeBytes_self s.mem (s.gpr .rdi + BitVec.ofNat 64 (136 + (s.gpr .rsi).toNat))
        (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (by rw [bytesAt_length]; exact (s.gpr .rcx).isLt)
      rwa [bytesAt_length] at h

end VG.Proof.Rc2.X86_64.Stream
