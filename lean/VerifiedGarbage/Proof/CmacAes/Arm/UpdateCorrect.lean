import VerifiedGarbage.Proof.CmacAes.Arm.UpdateLoop

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd wp_ldr eval_eq)

/-! ## Restoring the registers -/

theorem saved_eq : saved = saved.take 7 ++ [(.r10, 2088)] := rfl

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2096) :
    m.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = (savedMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ (N s₀) s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hsc := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s.rd ++ s.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact ⟨scrR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₂ ld ho m₁ _ _ sp₁ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hb := saved_bound p (by rw [saved_eq]; exact hp')
    exact ⟨by omega, by rw [h.r10]; omega, by rw [h.r10]; exact inS _ (by omega)⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      rw [ld p (by rw [← saved_eq]; exact hp'), h.r10, sl _ _ hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r = .r11 := by decide
      rw [hk r hr hs, ho _ (by decide), h.r11]
  · rw [sp₁, h.sp]
  · show Spec.Aes.bytesAt s₂.mem (State.addr (St s₀)) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [m₁, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

/-! ## The whole function -/

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁) (hz : s₁.z = decide (N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop body .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega) h

theorem update_wp {s₀ : State} (h0 : updateArm.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.Arm
