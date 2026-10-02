import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseSetup
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseFinish

/-! Base-point multiplication, output encoding, and the complete ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBase_correct {s : State} (h : ScalarBasePre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  refine WP.seq (WP.mono (scalarBaseSetup_ok h) fun u ⟨hcu, pu, su, ou, ku, fu⟩ => ?_)
  have input : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (scalarBaseEngine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base input (by omega) (by omega)) h.scalar_ws)
    fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 :=
    (kv.word 48 (.inl rfl) (by decide)).trans ou
  refine WP.mono (scalarBaseFinish_ok (kv.ctx hcu) lv ov h.f0
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
  · have hb : Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r1)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)
      rw [List.mem_singleton.mp hr]
      exact h.scalar_ws.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.scalarBase _
    rw [bt, vv, hb, Spec.Ed25519.scalarBase, encodedValue_spec]

end VG.Proof.Ed25519.Arm
