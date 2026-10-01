import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Contract

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.cbc d) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 512) : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.AArch64.Cbc.cbc]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s (writes 264 (by decide)) (writes 272 (by decide)) (writes 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at iv₂ count₂ data₂ buf₂ flag₂
  have key₂ := (keep₂.reg .x0 (by decide)).trans (g₁ .x0)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := scheduleAt_frame scratchFrame (s.gpr .x0) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (s.gpr .x1) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (s.gpr .x2) (s.gpr .x3).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .x3).toNat := by
    constructor
    · simp only [keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .x3).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .x2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 8 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x2 + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v₁ : s₃.mem.readW (s₃.gpr .x2 + BitVec.ofNat 64 264) 64 = s.gpr .x23 := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_rbx] at h
    rw [buf₃]; exact h
  have v₂ : s₃.mem.readW (s₃.gpr .x2 + BitVec.ofNat 64 272) 64 = s.gpr .x24 := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_rbp] at h
    rw [buf₃]; exact h
  have v₃ : s₃.mem.readW (s₃.gpr .x2 + BitVec.ofNat 64 280) 64 = s.gpr .x30 := by
    have h := h₃.scratchRead hp₂ 280 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_link] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, rbx₄, rbp₄, link₄, keep₄⟩ := restore_ok s₃ (s.gpr .x23) (s.gpr .x24) (s.gpr .x30)
    (reads 264 (by decide)) (reads 272 (by decide)) (reads 280 (by decide)) v₁ v₂ v₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hb : r = .x23
    · subst r; exact rbx₄
    · by_cases hp : r = .x24
      · subst r; exact rbp₄
      · by_cases hl : r = .x30
        · subst r; exact link₄
        · have saved : ∀ r ∈ preserved, r ≠ .x30 → r ∈ savedAcrossCall := by decide
          rw [keep₄.reg r (by simp [hb, hp, hl]), h₃.callee r (saved r hr hl) hp]
          have sep : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ∉ [.x23, .x24, .x1, .x2] := by decide
          exact (keep₂.reg r (sep r hr hb hp)).trans (g₁ r)
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt s hs
  change Exec isa Impl.Rc2.AArch64.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he⟩, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.Rc2.AArch64.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 0) := by
  refine Verified.of_correct encrypt_correct (encrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    contract, publicRegs_five] [satState] using satState

theorem decrypt_verified : Verified target Impl.Rc2.AArch64.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 0) := by
  refine Verified.of_correct decrypt_correct (decrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    contract, publicRegs_five] [satState] using satState

end VG.Proof.Rc2.AArch64.Cbc
