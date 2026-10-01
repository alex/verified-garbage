import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddContract
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddInputs
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddEngine
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddFinish

/-! The complete scalar multiply-add function and ARM calling convention. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarMulAdd_correct {s : State} (h : ScalarMulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  let b := stackArg s 0
  let ptr := fun i => s.gpr (scalarArgReg (i + 1))
  have hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [b]
  have ha : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 :=
    ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩
  unfold scalarMulAdd
  refine WP.seq (WP.append (scalarMulAddArgs_ok ha h.fs hw) fun u ⟨hcu, su, au, ku, fu⟩ => ?_)
  refine WP.mono (scalarMulAddInputs_ok (p := ptr) (q := s.gpr .r0) hcu
    (fun i hi => by
      have e := au (i + 1) (by omega)
      rw [show 32 + 4 * (i + 1) = 36 + 4 * i by omega] at e
      exact e)
    (fun i hi => (h.input hi).1)
    (fun i hi => by rw [ku.rd, ku.wr]; exact (h.input hi).2.1)
    (fun i hi => (h.input hi).2.2) (au 0 (by decide))) fun v ⟨kv, fv, iv, ov⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  refine WP.seq (WP.mono (scalarMulAddEngine_ok hcv (iv 0 (by decide)).1
    (iv 1 (by decide)).1 (iv 2 (by decide)).1) fun w ⟨kw, fw, lw, vw, ow⟩ => ?_)
  have sw : ScalarSaved (State.addr b) s.gpr w.mem :=
    (su.frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)).frame
      fw fun r hr i hi => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (scalarMulAddFinish_ok (hcv.of_rest kw (by decide)) lw (ow.trans ov) h.f0
    (by rw [kw.wr, kv.wr, ku.wr, h.wr]; simp) h.out_ws sw) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kw.sp, kv.sp, ku.sp]⟩, ?_⟩
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
    · rw [kt.gpr _ (by decide), kw.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide)]
  · have inputs : ∀ i < 3, V v.mem (State.addr b) (64 + 64 * i) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (ptr i)) 32) := by
      intro i hi
      rw [(iv i hi).2]
      apply congrArg Spec.Ed25519.decodeLE
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun k hk => fu.bytes (R := ⟨State.addr (ptr i), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hk)
      rw [List.mem_singleton.mp hr]
      exact (h.input hi).2.2.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.encodeLE 32 _
    rw [bt, vw, inputs 0 (by decide), inputs 1 (by decide), inputs 2 (by decide)]
    rfl

end VG.Proof.Ed25519.Arm
