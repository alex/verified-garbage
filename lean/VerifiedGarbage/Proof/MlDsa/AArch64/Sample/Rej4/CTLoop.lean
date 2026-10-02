import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTBase

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relMem byte_zero)
open VG.Proof.MlDsa.Sample (polyR coeff_contains G_length)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

def lrd (σ : State) (k : Nat) : List Region := [⟨bufP σ k,1008⟩]
def lwr (σ : State) (k : Nat) : List Region := [polyR (polyP σ k)]

theorem buf_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : bufP σ k = bufP τ k := by
  unfold bufP at'
  rw [hq.2.2.1]

theorem poly_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : polyP σ k = polyP τ k := by
  unfold polyP
  rw [hq.2.1]

theorem loop_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => ZeroReady σ k)) rnLoop fun _ _ => True := by
  refine relMem (fun σ => lrd σ k) (fun σ => lwr σ k) [.x25,.x26]
    (fun σ τ _ _ hq => by simp only [lrd,lwr,buf_pub hq,poly_pub hq]; exact ⟨trivial,trivial⟩)
    (fun σ s hp h => ?_) (fun σ s hp h => ?_)
    (fun σ τ s t _ _ hq hs ht => ?_) (by taint_decide)
  · rw [h.ready.env.rd,h.ready.env.wr,hp.rd,hp.wr]
    refine ⟨Covers.of_sub (fun r hr => ?_),Covers.of_sub (fun r hr => ?_)⟩
    · simp only [lrd,lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR σ,by simp,VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf+1008*k,rfl,
          by dsimp only [oBuf,scrR]; omega⟩
      · exact ⟨aR σ,by simp,1024*k,rfl,by dsimp only [aR,polyR]; omega⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨aR σ,by simp,1024*k,rfl,by dsimp only [aR,polyR]; omega⟩
  · have h := zero_lpre hp hk h
    obtain ⟨tr,u,he,_⟩ := VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (G_length _ _)
      (s₀ := s.withRegions (lrd σ k) (lwr σ k))
      ⟨h.buf,fun j hj => VG.Proof.MlKem.AArch64.in_rd (VG.Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        fun i hi => VG.Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        h.disj,h.x25,h.x26⟩
    exact ⟨tr,u,he⟩
  · refine ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => ?_,fun x hx => ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · rw [hs.x25,ht.x25]
        unfold at'
        rw [hq.2.2.1]
      · rw [hs.x26,ht.x26,poly_pub hq]
    · obtain ⟨r,hr,hc⟩ := hx
      simp only [lrd,lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · obtain ⟨j,hj,rfl⟩ := VG.Proof.MlKem.AArch64.Sample.at_off hc
        rw [hs.ready.out k hk j hj,buf_pub hq,ht.ready.out k hk j hj]
        exact congrArg (fun b : List Byte => b.getD j 0) (X_pub hq hk)
      · rw [byte_zero hs.zero hc,byte_zero ht.zero (by rw [← poly_pub hq]; exact hc)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
