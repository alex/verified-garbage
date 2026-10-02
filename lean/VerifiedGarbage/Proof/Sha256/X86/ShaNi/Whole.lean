import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Load

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (Pre pre_of st scr bp nb esp₀ stR scrR retR H₀
  save_ok common_zero restore_ok saved_frame)
open VG.Spec.Sha256 (stateAt compressBlocks)

theorem state_write_frame (p : Addr) (m : Mem) (x y : BitVec 128) :
    Frame [⟨p, 32⟩] m ((m.writeW p x).writeW (p + BitVec.ofNat 64 16) y) := by
  have c0 : (⟨p, 32⟩ : Region).Contains p 16 := by
    simpa only [BitVec.add_zero] using
      (Offset.contains_base p (d := 0) (n := 16) (k := 32) (by decide) (by decide))
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) x c0).writeW
    (List.mem_singleton_self _) y (Offset.contains_base _ (by decide) (by decide))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha256.X86.ShaNi.compress s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha256.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp)
    fun s₁ ⟨hesi, hedi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (load_ok hp (common_zero hp hesi hesp hrd hwr hm))
    fun s₂ ⟨hc₀, hg, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_)
  · refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0)
      (by simp only [eval, hzf, hz]) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      refine loop_ok hp hpos { hc₀ with edi := ?_, ebp := ?_ }
      · rw [hg _ (by decide) (by decide), hedi]; simp [VG.Proof.Sha256.X86.blkAddr]
      · rw [hg _ (by decide) (by decide), hebp]; simp [nb]
  · rw [WP.block_append_iff]
    have out0 : InRegions s₃.wr ((st s₀).setWidth 64) 16 :=
      ⟨stR s₀, by simp [hc.wr, hp.wr], by simpa only [BitVec.add_zero] using
        (Offset.contains_base ((st s₀).setWidth 64) (d := 0) (n := 16) (k := 32) (by decide) (by decide))⟩
    have out16 : InRegions s₃.wr ((st s₀).setWidth 64 + BitVec.ofNat 64 16) 16 :=
      ⟨stR s₀, by simp [hc.wr, hp.wr], Offset.contains_base _ (by decide) (by decide)⟩
    refine WP.mono (store_ok s₃ _ hc.x1 hc.x2 (by rw [hc.ebx]; exact hp.st_fits)
      (by rw [hc.ebx]; exact out0) (by rw [hc.ebx]; exact out16))
      fun s₄ ⟨⟨x, y, hm₄⟩, hstate, hg₄, hrd₄, hwr₄⟩ => ?_
    have hf : Frame [stR s₀] s₃.mem s₄.mem := by
      rw [hm₄, hc.ebx]; exact state_write_frame _ _ _ _
    have hfFull : Frame [stR s₀, scrR s₀] s₃.mem s₄.mem := hf.sub
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact ⟨stR s₀, by simp, fun _ h => h⟩)
    have hs : VG.Proof.Sha256.X86.Common s₀ (nb s₀) s₄ :=
      ⟨(congrFun hg₄ _).trans hc.esi, (congrFun hg₄ _).trans hc.esp,
        hrd₄.trans hc.rd, hwr₄.trans hc.wr, hc.frame.trans hfFull,
        by rw [hc.ebx] at hstate; exact hstate,
        saved_frame hp hc.saved (.inr hf)⟩
    refine WP.mono (restore_ok hp hs) fun s₅ ⟨hr, hm₅⟩ => ⟨⟨hr, ?_⟩, ?_⟩
    · rw [hm₅]
      exact hs.frame.readW (Region.contains_self _ _)
        (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
    · show stateAt s₅.mem _ = _
      rw [hm₅]; exact hs.state

end VG.Proof.Sha256.X86.ShaNi
