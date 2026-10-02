import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Spill
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
  rw [save_eq]
  refine Spill.save_ok (by decide) (fun p hp => writes p.2 (by revert p; decide)) ?_
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok { s with mem := savedMem s }
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have key₂ : s₂.gpr .x0 = s.gpr .x0 := keep₂.reg .x0 (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem
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
  have hsv : Spill.Saved (s₃.gpr .x2) s.gpr saved s₃.mem := fun p hp => by
    have hb : 264 ≤ p.2 ∧ p.2 + 8 ≤ 512 := by revert p; decide
    have h := h₃.scratchRead hp₂ p.2 hb.1 hb.2
    rw [buf₂, mem₂] at h
    rw [buf₃, h]
    exact Spill.saveMem_saved (by decide) _ _ _ p hp
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (fun p hp => reads p.2 (by revert p; decide)) hsv) fun s₄ h₄ => ?_
  constructor
  · intro r hr
    by_cases hs : r ∈ saved.map Prod.fst
    · exact h₄.gpr_of (.inl hs)
    have hb : r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x30 := by
      simpa only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] using hs
    have hsa : ∀ r ∈ preserved, r ≠ .x30 → r ∈ savedAcrossCall := by decide
    have sep : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ∉ [.x23, .x24, .x1, .x2] := by decide
    rw [h₄.other r hs, h₃.callee r (hsa r hr hb.2.2) hb.2.1]
    exact keep₂.reg r (sep r hr hb.1 hb.2.1)
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [h₄.mem]; exact out
    · rw [h₄.mem]; exact iv

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
