import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Tail
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.ConstantTime
import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! # The AdvSIMD bitsliced ECB functions meet their contracts -/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame ecb_blocks)
open VG.Proof.TripleDes.AArch64.Ecb (contract)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem publicRegs_four (s₁ s₂ : State) :
    VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [VG.Proof.TripleDes.AArch64.PublicRegs]

/-- Every block becomes its encryption or decryption. -/
theorem ecb_correct (d : Direction) {s : State} (E : Env s) :
    WP isa (ecb d) s (fun s' => ∀ b < (s.gpr .x2).toNat, blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (scheduleAt s.mem (s.gpr .x0)) d (blockAt s.mem (wAt (s.gpr .x1) b))) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  let k := n % 128
  have hl := E.len
  have hfit := E.fit
  rw [Impl.TripleDes.AArch64.BitsliceNeon.ecb]
  apply WP.seq
  apply WP.mono (wide_ok d E)
  intro s₁ w
  have g := w.gpr
  have h0 : s₁.gpr .x0 = S := g _ (by simp [WideRegs])
  have h3 : s₁.gpr .x3 = s.gpr .x3 := g _ (by simp [WideRegs])
  have h1 : s₁.gpr .x1 = wAt D (n - k) := w.x1
  have sub₁ : Region.Sub ⟨s₁.gpr .x1, 8 * k⟩ ⟨D, 8 * n⟩ := by
    rw [h1]; exact Offset.sub_base _ (by omega)
  have T : TailEnv s₁ k := by
    refine ⟨Nat.mod_lt _ (by decide), w.x2, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · rw [w.wr, E.wr, h1, wAt_wAt]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [w.wr, E.wr, h3]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [w.rd, w.wr, h0]; exact E.keyIn i hi
    · rw [h0]; exact E.keyData.sub_right sub₁
    · rw [h0, h3]; exact E.keyBuf
    · rw [h3]; exact E.dataBuf.sub_left sub₁
  apply WP.mono (tail_ok d T)
  intro s' t
  intro b hb
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩ := E.dataBuf
  by_cases hbk : b < n - k
  · rw [← w.done b hbk]
    refine blockAt_frame t.frame fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h1]; exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · rw [h3]; exact dataB.sub_left (Offset.sub_base _ (by omega))
  · obtain ⟨j, rfl⟩ : ∃ j, b = n - k + j := ⟨b - (n - k), by omega⟩
    have e := t.out j (by omega)
    rw [h1, wAt_wAt, h0] at e
    rw [e]
    have hK : scheduleAt s₁.mem S = scheduleAt s.mem S :=
      VG.Proof.TripleDes.scheduleAt_eq_of_frame S w.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact E.keyData.sub_right (Region.sub_prefix (by omega))
    have hB : blockAt s₁.mem (wAt D (n - k + j)) = blockAt s.mem (wAt D (n - k + j)) :=
      blockAt_frame w.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base D (by omega) (by omega)
    rw [hK, hB]

theorem ecb_contract (d : Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (ecb d) s (fun s' => (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  exact WP.mono (ecb_correct d ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩) fun s' h =>
    ecb_blocks _ _ _ _ _ _ h

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, hp, hg⟩ := WP.gprs (ecb_contract .encrypt s hs) (rs := preserved)
    (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, hp, hg⟩ := WP.gprs (ecb_contract .decrypt s hs) (rs := preserved)
    (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨hg, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem encrypt_verified : Verified target encrypt (Spec.TripleDes.ecbEncryptContract abi 0) := by
  refine Verified.of_correct encrypt_correct (encrypt_constantTime _) ?_
  sig_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target decrypt (Spec.TripleDes.ecbDecryptContract abi 0) := by
  refine Verified.of_correct decrypt_correct (decrypt_constantTime _) ?_
  sig_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.AArch64.BitslicedNeon
