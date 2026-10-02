import VerifiedGarbage.Proof.Ed25519.Arm.ScalarWideAdd
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec

/-! Serialize all 512 product bits for the same checked reduction engine. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarPackWide_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (la : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536) :
    WP isa (.block scalarPackWide) s fun t =>
      Rest [.r3, .r12] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 512, 64⟩] s.mem t.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 512 ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr b + BitVec.ofNat 64 512) 64) =
        val16 (accw ACC s.mem (State.addr b)) 32 := by
  have hA : ACC = 1472 := rfl
  have ll : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega)
  have lh : Lim s.mem (State.addr b) (ACC + 64) := by
    intro k hk
    change wd s.mem (State.addr b) (ACC + 64 + 4 * k) < _
    rw [show ACC + 64 + 4 * k = ACC + 4 * (16 + k) by omega]
    exact la _ (by omega)
  have afit := hc.fit
  have ep : State.addr (b + BitVec.ofNat 32 512) = State.addr b + BitVec.ofNat 64 512 :=
    addr_add (by omega)
  have pf : (b + BitVec.ofNat 32 512).toNat = b.toNat + 512 := by
    rw [toNat_add_lt (by rw [toNat_imm (by decide)]; omega), toNat_imm (by decide)]
  rw [scalarPackWide, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  have pu : u.gpr .r12 = b + BitVec.ofNat 32 512 := by rw [hu.gpr]; change s.gpr .r0 + _ = _; rw [hc.r0]; rfl
  refine WP.append (packField_ok (p := b + BitVec.ofNat 32 512) (a := ACC) (dst := 0) hcu
    (by decide) (hu.mem ▸ ll) (by decide) pu (by rw [pf]; omega)
    (fun i hi => by rw [ep, Offset.add_add]; exact hcu.inW (by omega))
    (by rw [ep, BitVec.add_zero]; exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have fv' : Frame [⟨State.addr b + BitVec.ofNat 64 512, 32⟩] s.mem v.mem := by
    simpa only [ep, BitVec.add_zero, hu.mem] using fv
  have hvh : ∀ k < 16, limb v.mem (State.addr b) (ACC + 64) k = limb s.mem (State.addr b) (ACC + 64) k :=
    limb_frame fv' fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by decide)
  have lvh : Lim v.mem (State.addr b) (ACC + 64) := fun k hk => by rw [hvh k hk]; exact lh k hk
  refine WP.mono (packField_ok (p := b + BitVec.ofNat 32 512) (a := ACC + 64) (dst := 32) hcv
    (by decide) lvh (by decide) ((kv.gpr _ (by decide)).trans pu) (by rw [pf]; omega)
    (fun i hi => by rw [ep, Offset.add_add]; exact hcv.inW (by omega))
    (by rw [ep, Offset.add_add]; exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)))
    fun t ⟨kt, ft, vt⟩ => ?_
  have ft' : Frame [⟨State.addr b + BitVec.ofNat 64 544, 32⟩] v.mem t.mem := by
    simpa only [ep, Offset.add_add] using ft
  have vlo : packedV t.mem (State.addr b + BitVec.ofNat 64 512) = V s.mem (State.addr b) ACC := by
    rw [packedV_frame ft' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide))]
    simpa only [ep, BitVec.add_zero, hu.mem] using vv
  have vhi : packedV t.mem (State.addr b + BitVec.ofNat 64 544) = V s.mem (State.addr b) (ACC + 64) := by
    have ve : V v.mem (State.addr b) (ACC + 64) = V s.mem (State.addr b) (ACC + 64) := val16_congr hvh
    simpa only [ep, Offset.add_add, ve] using vt
  refine ⟨(hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_,
    (kt.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans pu), ?_⟩
  · exact (fv'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (ft'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · change Spec.Ed25519.decodeLE (Spec.X25519.bytesAt t.mem _ (32 + 32)) = _
    rw [VG.Proof.X25519.bytesAt_add, decodeLE_append, VG.Proof.X25519.length_bytesAt]
    change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem _ 32) +
      256 ^ 32 * Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem _ 32) = _
    rw [scalar_packed_decode, scalar_packed_decode, Offset.add_add, vlo, vhi, scalarWide_split]
    rfl

end VG.Proof.Ed25519.Arm
