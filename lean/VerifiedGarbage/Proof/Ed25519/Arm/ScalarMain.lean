import VerifiedGarbage.Proof.Ed25519.Arm.ScalarSetup
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarLoop
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish

/-! The complete scalar-reduction function, including its ABI and bytes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalar_region_sub {b : BitVec 32} {r : Region} (h : r ∈ scalarRegions b) :
    r.Sub ⟨State.addr b, 8192⟩ := by
  simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact Offset.sub_base _ (by decide)

theorem scalarReduce_correct {s : State} (h : ScalarReducePre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  have hR : SR = 256 := rfl
  have hD : SD = 320 := rfl
  unfold scalarReduce
  refine WP.seq (WP.mono (scalarReduceSetup_ok h) fun u ⟨hcu, pu, su, ou, ku, fu⟩ => ?_)
  have wide : (⟨State.addr (s.gpr .r1), 64⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (scalarReduceEngine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base wide (by omega) (by omega))
    (fun r hr => h.wide_ws.sub_right (scalar_region_sub hr))) fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (.inl (by change _ ≤ _; omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) 32 = s.gpr .r0 := by
    rw [kv.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), ou]
    simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (scalarFinish_ok (kv.ctx hcu) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kv.rest.gpr _ (by decide), ku.gpr _ (by decide)]
  · change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.encodeLE 32 _
    rw [bt, vv]
    apply congrArg (Spec.Ed25519.encodeLE 32)
    apply congrArg (fun bs => Spec.Ed25519.decodeLE bs % Spec.Ed25519.L)
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 64⟩) (fun r hr => ?_) (by decide : 64 ≤ 2 ^ 64)
      (List.mem_range.mp hn)
    rw [List.mem_singleton.mp hr]
    exact h.wide_ws.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Ed25519.Arm
