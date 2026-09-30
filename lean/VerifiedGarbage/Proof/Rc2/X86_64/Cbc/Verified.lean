import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Contract

/-! # Verified RC2-CBC encryption and decryption -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem cbc_body_correct (d : Spec.Rc2.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.cbc d) s (fun s' => gprPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyIv, keyData, keyBuf, ivData, ivBuf, dataBuf,
    retIv, retData, retBuf, stackKey, stackIv, stackData, stackBuf, fit⟩ := hs
  have writes (i : Nat) (hi : i + 8 ≤ 512) : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 i) 8 := by
    rw [hwr]
    exact ⟨⟨s.gpr .r8, 512⟩, by simp, Offset.contains_base _ hi (by omega)⟩
  rw [Impl.Rc2.X86_64.Cbc.cbc]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s (writes 264 (by decide)) (writes 272 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, iv₂, count₂, data₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at iv₂ count₂ data₂ buf₂ flag₂
  have key₂ := (keep₂.reg .rdi (by decide)).trans (g₁ .rdi)
  have sp₂ := (keep₂.reg .rsp (by decide)).trans (g₁ .rsp)
  have rd₂ := keep₂.rd.trans keep₁.rd
  have wr₂ := keep₂.wr.trans keep₁.wr
  have mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  have scratchFrame : Frame [⟨s.gpr .r8, 512⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  have initialKey := scheduleAt_frame scratchFrame (s.gpr .rdi) (by simpa using keyBuf)
  have initialIv := blockAt_frame scratchFrame (s.gpr .rsi) (by simpa using ivBuf)
  have initialData := blocksAt_frame scratchFrame (s.gpr .rdx) (s.gpr .rcx).toNat (by simpa using dataBuf)
  have hp₂ : StepPre s₂ (s.gpr .rcx).toNat := by
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
    · simpa only [stackR, keyR, sp₂, key₂] using stackKey
    · simpa only [stackR, ivR, sp₂, iv₂] using stackIv
    · simpa only [stackR, dataR, sp₂, data₂] using stackData
    · simpa only [stackR, bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .rcx).toNat (by omega) hp₂
    (by simpa using count₂) (by rw [count₂]; exact flag₂))
  intro s₃ h₃
  have rd₃ := h₃.rd.trans rd₂
  have wr₃ := h₃.wr.trans wr₂
  have buf₃ := (h₃.reg .rdx (by decide) (by decide) (by decide)).trans buf₂
  have reads (i : Nat) (hi : i + 8 ≤ 512) :
      InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdx + BitVec.ofNat 64 i) 8 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have v₁ : s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 264) 64 = s.gpr .rbx := by
    have h := h₃.scratchRead hp₂ 264 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_rbx] at h
    rw [buf₃]; exact h
  have v₂ : s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 272) 64 = s.gpr .rbp := by
    have h := h₃.scratchRead hp₂ 272 (by decide) (by decide)
    rw [buf₂, mem₂, savedMem_rbp] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, rbx₄, rbp₄, keep₄⟩ := restore_ok s₃ (s.gpr .rbx) (s.gpr .rbp)
    (reads 264 (by decide)) (reads 272 (by decide)) v₁ v₂
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      by_cases hb : r = .rbx
      · subst r; exact rbx₄
      · by_cases hp : r = .rbp
        · subst r; exact rbp₄
        · rw [keep₄.reg r (by simp [hb, hp]), h₃.callee r hr hp]
          have sep : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .rbp → r ∉ [.rbx, .rbp, .rsi, .rdx] := by decide
          exact (keep₂.reg r (sep r hr hb hp)).trans (g₁ r)
    · let rs : List Region := [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩,
        ⟨s.gpr .r8, 512⟩, below (s.gpr .rsp) 8]
      have loopFrame : Frame rs s₂.mem s₃.mem := by
        have h := h₃.mem
        simp only [loopWrites, ivR, dataR, stackR, iv₂, data₂, buf₂, sp₂] at h
        apply h.sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨s.gpr .rsi, 8⟩, by simp [rs], fun _ h => h⟩
        · exact ⟨⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩, by simp [rs], fun _ h => h⟩
        · exact ⟨⟨s.gpr .r8, 512⟩, by simp [rs], Region.sub_prefix (by decide)⟩
        · exact ⟨below (s.gpr .rsp) 8, by simp [rs], fun _ h => h⟩
      have frame : Frame rs s.mem s₄.mem := by
        rw [keep₄.mem]
        exact (scratchFrame.mono (by simp [rs])).trans loopFrame
      apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (hn := by decide)
      have stackSep : (Region.mk (s.gpr .rsp) 8).Disjoint (below (s.gpr .rsp) 8) :=
        Offset.base_disjoint_below _ (by decide : 8 + 8 ≤ 2 ^ 64)
      simpa only [rs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
        And.intro retIv (And.intro retData (And.intro retBuf stackSep))
  · have out := h₃.data
    have iv := h₃.iv
    rw [key₂, iv₂, data₂, initialKey, initialIv, initialData] at out iv
    constructor
    · rw [keep₄.mem]; exact out
    · rw [keep₄.mem]; exact iv

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.X86_64.Cbc.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .encrypt s hs
  change Exec isa Impl.Rc2.X86_64.Cbc.encrypt s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.Rc2.X86_64.Cbc.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := cbc_body_correct .decrypt s hs
  change Exec isa Impl.Rc2.X86_64.Cbc.decrypt s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_six (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.Rc2.X86_64.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 8) := by
  refine Verified.of_correct encrypt_correct (encrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcEncryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    contract, publicRegs_six] [satState] using satState

theorem decrypt_verified : Verified target Impl.Rc2.X86_64.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 8) := by
  refine Verified.of_correct decrypt_correct (decrypt_constantTime _) ?_
  sig_implies [Spec.Rc2.cbcDecryptContract, Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argRegs,
    contract, publicRegs_six] [satState] using satState

end VG.Proof.Rc2.X86_64.Cbc
