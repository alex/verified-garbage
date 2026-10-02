import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep relTaint vectorRelTaintStep)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi init setup squeezeStepWith rejNTT4With)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop retZ zeroPoly)

theorem sample_ctFor {k : Nat} (hk : k < 4) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hcheck : (taint.check (Taint.ofRegs [.x19,.x21])
      (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) hint).isSome = true) :
    RelCT isa (Rel2 r4K.pre r4K.pub Ready) (sample k) fun _ _ => True := by
  unfold sample
  refine RelCT.seq (relTaintStep (J' := fun σ => ArgReady σ k) [.x19,.x21]
    (fun _ _ hp h => args_ready hk hp h) (fun σ τ s t _ _ hq hs ht => ?_) hcheck) ?_
  · refine ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],fun r hr => ?_⟩
    rcases mem2 hr with rfl | rfl
    · rw [hs.env.x19,ht.env.x19,hq.2.2.1]
    · rw [hs.env.x21,ht.env.x21,hq.2.1]
  refine RelCT.seq (relTaintStep (J' := fun σ => ZeroReady σ k) [.x26]
    (fun _ _ hp h => zero_ready hk hp h) (fun σ τ s t _ _ hq hs ht =>
      ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => by
        rw [List.mem_singleton.mp hr,hs.x26,ht.x26,poly_pub hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := Ready) (fun _ _ hp h => loop_ready hp hk h) (loop_ct hk)) ?_
  exact relTaint [] (fun _ _ _ _ _ _ hq hs ht =>
    ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],by simp⟩) (by taint_decide)

theorem sample_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub Ready) (sample k) fun _ _ => True := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact sample_ctFor (by decide) (by taint_decide)

theorem init_ct : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ s => s = σ))
    (.block (init++setup)) (Rel2 r4K.pre r4K.pub (fun σ => Phase σ 0 0)) := by
  refine vectorRelTaintStep [.x0,.x1,.x2] (fun σ s hp hs => ?_)
    (fun _ _ _ _ _ _ hq hs ht => ?_) (by taint_decide)
  · subst s
    rw [WP.block_append_iff]
    exact WP.mono (init_ok hp) fun _ ⟨he,h0,h1⟩ => setup_ok he h0 h1
  · subst hs ht
    exact ⟨hq.2.2.2.1,fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact hq.1
      · exact hq.2.1
      · exact hq.2.2.1⟩

theorem squeeze_ctFor (sha3 : Bool) {hint : VG.Taint.Hint VectorTaint.T}
    (hcheck : (VectorTaint.taint.check (VectorTaint.ofRegs [.x22,.x23,.x24,.x25,.x26,.x27,.x28])
      (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) hint).isSome = true) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => Phase σ 0 0))
    (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) (Rel2 r4K.pre r4K.pub Ready) := by
  refine vectorRelTaintStep (hc := hint) [.x22,.x23,.x24,.x25,.x26,.x27,.x28]
    (fun _ _ hp h => WP.mono (squeeze_ok sha3 hp h) fun _ ht =>
      ⟨ht.env,fun k hk j hj => ht.out k hk j (by simpa using hj)⟩)
    (fun σ τ s t _ _ hq hs ht => ?_) ?_
  · refine ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],fun r hr => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hs.x22,ht.x22]; unfold stateP at'; rw [hq.2.2.1]
    · rw [hs.x23,ht.x23]; unfold stateP at'; rw [hq.2.2.1]
    · change s.gpr (bReg 0) = t.gpr (bReg 0)
      rw [hs.ptrs 0 (by decide),ht.ptrs 0 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · change s.gpr (bReg 1) = t.gpr (bReg 1)
      rw [hs.ptrs 1 (by decide),ht.ptrs 1 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · change s.gpr (bReg 2) = t.gpr (bReg 2)
      rw [hs.ptrs 2 (by decide),ht.ptrs 2 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · change s.gpr (bReg 3) = t.gpr (bReg 3)
      rw [hs.ptrs 3 (by decide),ht.ptrs 3 (by decide)]; unfold bufAt at'; rw [hq.2.2.1]
    · exact BitVec.eq_of_toNat_eq (hs.count.trans ht.count.symm)
  · exact hcheck
theorem squeeze_ct (sha3 : Bool) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => Phase σ 0 0))
    (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) (Rel2 r4K.pre r4K.pub Ready) := by
  cases sha3 <;> exact squeeze_ctFor _ (by taint_decide)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
