import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep vectorRelTaint)
open VG.Proof.MlKem.AArch64 (wp_movz wp_nil)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi rejNTT4With)

theorem start_parsed {σ s : State} (hp : Pre σ) (h : Ready σ s) :
    WP isa (.block [.movz .x .x27 1 0]) s (Parsed σ 0) := by
  refine wp_movz fun t ht et => wp_nil ⟨?_,?_,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  · exact h.polyStep hp (k := 0) (by decide) (by rw [ht.mem]; exact Frame.refl _ _)
      ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
  · rw [et]; rfl

theorem parsed_ct {k : Nat} (hk : k < 4) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => Parsed σ k))
    (sample k) (Rel2 r4K.pre r4K.pub (fun σ => Parsed σ (k+1))) :=
  relStep (fun _ _ hp h => parsed_step hp hk h)
    (RelCT.mono (sample_ct hk) (fun _ _ ⟨σ,τ,hp,hp',hq,h,h'⟩ =>
      ⟨σ,τ,hp,hp',hq,h.ready,h'.ready⟩) (fun _ _ _ => trivial))

theorem body_ct : RelCT isa (Rel2 r4K.pre r4K.pub Ready)
    (.seq (.block [.movz .x .x27 1 0])
      (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi))))))
    fun _ _ => True := by
  refine RelCT.seq (relTaintStep (J' := fun σ => Parsed σ 0) []
    (fun _ _ hp h => start_parsed hp h) (fun _ _ _ _ _ _ hq hs ht =>
      ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],by simp⟩) (by taint_decide)) ?_
  refine RelCT.seq (parsed_ct (by decide : 0 < 4)) ?_
  refine RelCT.seq (parsed_ct (by decide : 1 < 4)) ?_
  refine RelCT.seq (parsed_ct (by decide : 2 < 4)) ?_
  refine RelCT.seq (parsed_ct (by decide : 3 < 4)) ?_
  exact vectorRelTaint [.x19] (fun _ _ _ _ _ _ hq hs ht =>
    ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => by
      rw [List.mem_singleton.mp hr,hs.ready.env.x19,ht.ready.env.x19,hq.2.2.1]⟩) (by taint_decide)

theorem ct (sha3 : Bool) : ConstantTime isa r4K.pre r4K.pub (rejNTT4With sha3) := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.mono (Q := fun _ _ => True) (P := Rel2 r4K.pre r4K.pub (fun σ s => s = σ)) ?_
      (fun s t h => ⟨s,t,h.1,h.2.1,h.2.2,rfl,rfl⟩) (fun _ _ _ => trivial))
  exact RelCT.seq init_ct (RelCT.seq (squeeze_ct sha3) body_ct)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
