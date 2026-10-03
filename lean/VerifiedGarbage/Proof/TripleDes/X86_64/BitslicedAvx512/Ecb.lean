import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Wide

/-!
# The AVX-512 function

The batches of 512 blocks (`wide_ok`), then the 64-block code on the blocks
left (`Bitsliced.ecb_ok`): every block becomes its encryption or decryption
(`ecb_ok`).
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512 VG.Spec.TripleDes
open VG.Proof.TripleDes.X86_64.Bitsliced (blockOut wAt wAt_wAt blockAt_frame EcbPre EcbPost ecb_blocks)

theorem ecb_ok (d : Direction) {s : State} (hrd : s.rd = [⟨s.gpr .rdi, 384⟩])
    (hwr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 1024⟩])
    (keyData : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (keyBuf : (⟨s.gpr .rdi, 384⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩)
    (retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 1024⟩)
    (fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64) :
    WP isa (ecb d) s (fun s' => gprPreserved s s' ∧
      blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
        Spec.TripleDes.ecb (scheduleAt s.mem (s.gpr .rdi)) d
          (blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  let k := n - n % 512
  have E : WideEnv s := by
    refine ⟨by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [hwr]; exact List.mem_cons_self, fun i hi => ?_, dataBuf, keyBuf, keyData, fit⟩
    rw [hrd]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
  have hl := E.len
  rw [Impl.TripleDes.X86_64.BitsliceAvx512.ecb]
  apply WP.seq
  apply WP.mono (wide_ok d E)
  intro s₁ w
  have g : ∀ r, WideRegs r → s₁.gpr r = s.gpr r := w.gpr
  have hc := g .rcx (by simp [WideRegs, PassRegs])
  have hdi := g .rdi (by simp [WideRegs, PassRegs])
  have hsp := g .rsp (by simp [WideRegs, PassRegs])
  have hm : (s₁.gpr .rdx).toNat = n % 512 := by
    rw [w.rdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD₁ : s₁.gpr .rsi = wAt D k := w.rsi
  have sub₁ : Region.Sub ⟨s₁.gpr .rsi, 8 * (s₁.gpr .rdx).toNat⟩ ⟨D, 8 * n⟩ := by
    rw [hD₁, hm]; exact Offset.sub_base _ (by omega)
  have pre₁ : EcbPre s₁ := by
    refine ⟨by rw [hc, w.wr, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun i hi => ?_,
      fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w.wr, hwr, hD₁, wAt_wAt]
      rw [hm] at hi
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [hdi, w.rd, w.wr, hrd]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [hdi]; exact keyData.sub_right sub₁
    · rw [hdi, hc]; exact keyBuf
    · rw [hc]; exact dataBuf.sub_left sub₁
    · rw [hsp]; exact retData.sub_right sub₁
    · rw [hsp, hc]; exact retBuf
    · rw [hD₁, hm]
      have hfit : D.toNat + 8 * n ≤ 2 ^ 64 := fit
      have hk : k + n % 512 = n := by omega
      simp only [wAt, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega)]
      by_cases hw : D.toNat + 8 * k < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hw]; omega
      · rw [show D.toNat + 8 * k = 2 ^ 64 by omega, Nat.mod_self]; omega
  apply WP.mono (VG.Proof.TripleDes.X86_64.Bitsliced.ecb_ok d pre₁)
  intro s' t
  have scr₁ : VG.Proof.TripleDes.X86_64.Bitsliced.scratchR s₁ = scratchR s := by
    simp only [VG.Proof.TripleDes.X86_64.Bitsliced.scratchR, scratchR, hc]
  have tf := t.frame
  rw [scr₁] at tf
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [t.gpr.1 r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w.rbx
    all_goals exact g _ (by simp [WideRegs, PassRegs])
  · rw [← hsp, t.gpr.2, hsp]
    refine w.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retBuf
    · exact retData.sub_right (Region.sub_prefix (by omega))
  · apply ecb_blocks
    intro b hb
    have dataB : (⟨D, 8 * n⟩ : Region).Disjoint (scratchR s) := dataBuf
    by_cases hbk : b < k
    · rw [← w.done b hbk]
      refine blockAt_frame tf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dataB.sub_left (Offset.sub_base _ (by omega))
      · rw [hD₁, hm]
        exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = k + j := ⟨b - k, by omega⟩
      have e := t.done j (by rw [hm]; omega)
      rw [hD₁, wAt_wAt, hdi] at e
      rw [e]
      have hK : scheduleAt s₁.mem S = scheduleAt s.mem S :=
        VG.Proof.TripleDes.scheduleAt_eq_of_frame S w.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact keyBuf
          · exact keyData.sub_right (Region.sub_prefix (by omega))
      have hB : blockAt s₁.mem (wAt D (k + j)) = blockAt s.mem (wAt D (k + j)) :=
        blockAt_frame w.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dataB.sub_left (Offset.sub_base _ (by omega))
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB]

end VG.Proof.TripleDes.X86_64.BitslicedAvx512
