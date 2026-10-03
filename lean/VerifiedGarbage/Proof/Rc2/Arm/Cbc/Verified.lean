import VerifiedGarbage.Proof.Rc2.Arm.Cbc.ConstantTime

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.Arm.Cbc.cbc d) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    _ivArgs, _dataArgs, _bufArgs, keyFit, ivFit, bufFit, _spFit, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 512) : InRegions s.wr (State.addr (stackArg s 0) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.Arm.Cbc.cbc]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .r12) := keep₀.reg r (by simpa using hr)
  have writes₀ (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions s₀.wr (State.addr (s₀.gpr .r12) + BitVec.ofNat 64 i) 4 := by
    rw [keep₀.wr, buf₀]; exact writes i hi
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit)
    (writes₀ 264 (by decide)) (writes₀ 268 (by decide)) (writes₀ 272 (by decide))
    (writes₀ 276 (by decide)) (writes₀ 280 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  rw [g₁, g₀ .r1 (by decide)] at iv₂
  rw [g₁, g₀ .r3 (by decide)] at count₂ flag₂
  rw [g₁, g₀ .r2 (by decide)] at data₂
  rw [g₁, buf₀] at buf₂
  have key₂ := (keep₂.reg .r0 (by decide)).trans ((g₁ .r0).trans (g₀ .r0 (by decide)))
  have rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  have wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  have mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  have initialKey := scheduleAt_frame scratchFrame (State.addr (s.gpr .r0)) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (State.addr (s.gpr .r1)) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (State.addr (s.gpr .r2)) (s.gpr .r3).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .r3).toNat := by
    constructor
    · rw [key₂]; exact keyFit
    · rw [iv₂]; exact ivFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · simp only [Covers, keyR, ivR, dataR, bufR, key₂, iv₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simp only [Covers, ivR, dataR, bufR, iv₂, data₂, buf₂, wr₂, hwr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind, hc⟩
    · simpa only [keyR, ivR, key₂, iv₂] using keyIv
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [ivR, dataR, iv₂, data₂] using ivData
    · simpa only [ivR, bufR, iv₂, buf₂] using ivBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .r3).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .r2 (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 4 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 i) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v0 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 264) 32 = s.gpr .r4 := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r4, g₀ .r4 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v1 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 268) 32 = s.gpr .r5 := by
    have h := h₃.scratchRead hp₂ 268 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r5, g₀ .r5 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v2 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 272) 32 = s.gpr .r6 := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r6, g₀ .r6 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v3 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 276) 32 = s.gpr .r7 := by
    have h := h₃.scratchRead hp₂ 276 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_r7, g₀ .r7 (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  have v4 : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 280) 32 = s.gpr .lr := by
    have h := h₃.scratchRead hp₂ 280 (by decide) (by decide)
    rw [buf₂, mem₂, ← buf₀, savedMem_lr, g₀ .lr (by decide)] at h
    rw [buf₀] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s₃ s.gpr (by rw [buf₃]; exact bufFit)
    (reads 264 (by decide)) v0    (reads 268 (by decide)) v1    (reads 272 (by decide)) v2    (reads 276 (by decide)) v3    (reads 280 (by decide)) v4
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hs : r ∈ callerSaved
    · exact saved₄ r hs
    · have kept : ∀ r ∈ preserved, r ∉ callerSaved →
          r ∈ savedAcrossCall ∧ r ≠ .r5 ∧ r ∉ [.r4, .r5, .r1, .r2] ∧ r ≠ .r12 := by decide
      obtain ⟨hc, hn, ht, h12⟩ := kept r hr hs
      rw [keep₄.reg r hs, h₃.callee r hc hn, keep₂.reg r ht, g₁ r]
      exact g₀ r h12
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.Arm.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt s hs
  change Exec isa Impl.Rc2.Arm.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.Arm.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt s hs
  change Exec isa Impl.Rc2.Arm.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem encrypt_verified : Verified target Impl.Rc2.Arm.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 0) := by
  refine Verified.of_correct encrypt_correct (cbc_constantTime .encrypt) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, contract]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem decrypt_verified : Verified target Impl.Rc2.Arm.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 0) := by
  refine Verified.of_correct decrypt_correct (cbc_constantTime .decrypt) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, contract]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.Rc2.Arm.Cbc
