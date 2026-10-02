import VerifiedGarbage.Proof.TripleDes.X86.Key.Body

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd
open VG.Proof.Rc2.X86 (addr32)

def preparedKey (s : State) : State := s.setReg .ebp (scratchArg s 4)
abbrev scratchR (s : State) : Region := ⟨addr32 (scratchArg s 4), 512⟩
abbrev savedR (s : State) : Region := ⟨addr32 (scratchArg s 4), 16⟩

structure HeadPre (s : State) : Prop where
  permissions : Permissions (preparedKey s)
  scratchFit : (scratchArg s 4).toNat + 512 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4
  lenRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4
  saveWrites : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) 4
  argsSave : (⟨argAddr s 0, 16⟩ : Region).Disjoint (savedR s)
  keyScratch : (keyR s).Disjoint (scratchR s)
  outputScratch : (outputR s).Disjoint (scratchR s)

structure ExpandPost (original s : State) : Prop where
  result : Spec.TripleDes.scheduleAt s.mem (addr32 (scheduleArg original)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt original.mem (addr32 (keyArg original)) (keyLength original))
  saved : ∀ r ∈ VG.Impl.TripleDes.X86.savedRegs, s.gpr r = original.gpr r
  sp : s.gpr .esp = original.gpr .esp
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  frame : Frame [outputR original, scratchR original] original.mem s.mem

theorem expandKey_ok (s : State) (hp : HeadPre s) :
    WP isa Impl.TripleDes.X86.Key.expandKey s (ExpandPost s) := by
  rw [Impl.TripleDes.X86.Key.expandKey]
  apply WP.seq
  apply WP.mono (saveWithArg_ok s 4 hp.argRead hp.scratchFit hp.saveWrites)
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  have ghostSP : (preparedKey s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have args₁ := VG.Proof.Rc2.X86.arguments_frame 4 h₁.frame sp₁
    (by have h := hp.permissions.spFit; rw [ghostSP] at h; exact h)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.argsSave)
  have ghostArgs : ∀ i, arg (preparedKey s) i = arg s i := by
    intro i; unfold arg argAddr; rw [ghostSP]; rfl
  have permissions₁ : Permissions s₁ := hp.permissions.congr
    (fun i hi => (args₁ i hi).trans (ghostArgs i).symm)
    (by rw [preparedKey, gpr_setReg_self]; exact h₁.bp)
    (sp₁.trans ghostSP.symm) h₁.rd h₁.wr
  have init : Components s₁ s₁ 0 :=
    ⟨fun _ h => by omega, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  apply body_ok s₁ s₁ permissions₁ init
    (by rw [h₁.rd, h₁.wr, sp₁]; exact hp.lenRead)
  intro s₂ h₂
  have bp₂ : s₂.gpr .ebp = scratchArg s 4 := h₂.bp.trans h₁.bp
  have args₂ (i : Nat) (hi : i < 4) : arg s₂ i = arg s i :=
    (h₂.args i hi).trans (args₁ i hi)
  have output₁ : outputR s₁ = outputR s := by
    unfold outputR
    change Region.mk (addr32 (s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32)) 384 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  have outputArg₁ : scheduleArg s₁ = scheduleArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 3) 32 = _
    rw [← argument_word s₁ 2, args₁ 2 (by decide), argument_word s 2]; rfl
  have keyArg₁ : keyArg s₁ = keyArg s := by
    change s₁.mem.readW (wordAddr (s₁.gpr .esp) 1) 32 = _
    rw [← argument_word s₁ 0, args₁ 0 (by decide), argument_word s 0]; rfl
  have len₁ : keyLength s₁ = keyLength s := by unfold keyLength; rw [args₁ 1 (by decide)]
  have scratchSub (i : Nat) (hi : i < 4) :
      Region.Sub ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩ (scratchR s) :=
    Offset.sub_base _ (by omega_using [hi])
  have saved₂ : Saved s s₂ := by
    intro i hi
    rw [bp₂]
    have hm := h₂.frame.readW (a := addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i)) (w := 32)
      (r := ⟨addr32 (scratchArg s 4) + BitVec.ofNat 64 (4 * i), 4⟩)
      (Region.contains_self _ _) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [output₁]; exact (hp.outputScratch.sub_right (scratchSub i hi)).symm
        · obtain rfl := List.mem_singleton.mp hr
          have sep := savedSlot_work_disjoint s₁ i hi
          rw [h₁.bp] at sep
          exact sep) (by decide)
    have saved₁ := h₁.saved i hi
    rw [h₁.bp] at saved₁
    exact hm.trans saved₁
  have reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr)
      (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, bp₂]
    obtain ⟨r, hr, hc⟩ := hp.saveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.mono (blockRestore_ok s s₂ saved₂ (by rw [bp₂]; exact hp.scratchFit) reads₂)
  intro s₃ h₃
  have initialBytes := VG.Proof.TripleDes.bytesAt_eq_of_frame (addr32 (keyArg s)) (keyLength s)
    h₁.frame (by
      have fit := permissions₁.keyFit
      rw [keyArg₁, len₁] at fit
      have bound := (keyArg s).isLt
      omega_using [fit, bound]) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact hp.keyScratch.sub_right (Region.sub_prefix (by decide)))
  have result := h₂.schedule
  rw [outputArg₁, keyArg₁, len₁] at result
  rw [← VG.Proof.TripleDes.expandKey_memory s₁.mem (addr32 (keyArg s)) (keyLength s)
    (by have valid := permissions₁.valid; rw [len₁] at valid; exact valid), initialBytes] at result
  refine ⟨?_, h₃.saved, h₃.sp.trans (h₂.sp.trans sp₁), h₃.rd.trans (h₂.rd.trans h₁.rd),
    h₃.wr.trans (h₂.wr.trans h₁.wr), ?_⟩
  · rw [h₃.mem]; exact result
  · rw [h₃.mem]
    have first : Frame [outputR s, scratchR s] s.mem s₁.mem := h₁.frame.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨scratchR s, by simp, Region.sub_prefix (by decide)⟩)
    exact first.trans (h₂.frame.sub (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [output₁]; exact ⟨outputR s, by simp, fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        refine ⟨scratchR s, by simp, ?_⟩
        rw [workRegion, h₁.bp]
        exact Offset.sub_base _ (by decide)))

end VG.Proof.TripleDes.X86.Key
