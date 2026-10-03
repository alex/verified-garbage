import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop

/-!
# AES-CMAC on x86: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (eval_e)

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2080) :
    m.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem UPre.ret_stk {s₀ : State} (_hp : UPre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

/-- The return address, which nothing writes. -/
theorem ret_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  (UPre.big_of hf).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact hp.ret_stk) (by decide)

theorem epilogue_wp {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv s₀ (N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (UPre.big_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact ret_read hp h.frame
  · show Spec.Aes.bytesAt s₂.mem ((St s₀).setWidth 64) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [r₂.mem, u₁.mem, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem mid_wp {s₀ : State} (hp : UPre s₀) {s₁ : State} (h : LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body v.callee) .ne)) s₁ (LInv s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok v hp (by omega) h

theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp v hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.CmacAes.X86
