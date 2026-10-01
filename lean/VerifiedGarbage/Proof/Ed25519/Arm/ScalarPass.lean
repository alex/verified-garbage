import VerifiedGarbage.Proof.Ed25519.Arm.ScalarNat
import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-! Carry passes for doubling a remainder and subtracting the subgroup order. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem scalarDoublePass_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    {bit : Nat} (hb : bit < 2) (h5 : (s.gpr .r5).toNat = bit) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SR scalarDoubleSrc)) s
      (PassInv .r0 SR s (fun k => 2 * limb s.mem (State.addr b) SR k) bit 16) := by
  have hR : SR = 256 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; omega) (by omega) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarDoubleSrc
  refine ldr0_ok hct (by omega) fun u hu => wp_dp (op2_reg _ _) fun v hv => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨?_, (hu.rest (by decide)).trans (hv.rest (by decide)), by rw [hv.mem, hu.mem]⟩
  rw [hv.gpr]
  show (u.gpr .r3 + u.gpr .r3).toNat = _
  rw [toNat_add_lt (by rw [he]; have := hl k hk; omega), he]
  omega

theorem scalarSubtractPass_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    (h5 : (s.gpr .r5).toNat = 1) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SD scalarSubtractSrc)) s
      (PassInv .r0 SD s (fun k => limb s.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
  have hR : SR = 256 := rfl
  have hT : SD = 320 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; have := scalarComplement_lt k; omega) (by decide) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarSubtractSrc
  refine ldr0_ok hct (by omega) fun u hu => wp_movw fun v hv =>
    wp_dp (op2_reg _ _) fun w hw => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have hc2 : (v.gpr .r2).toNat = scalarComplement k := by
    rw [hv.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (scalarComplement_lt k)]
    exact Nat.mod_eq_of_lt (by have := scalarComplement_lt k; omega)
  refine ⟨?_, (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))), by
    rw [hw.mem, hv.mem, hu.mem]⟩
  rw [hw.gpr]
  show (v.gpr .r3 + v.gpr .r2).toNat = _
  rw [hv.other .r3 (by decide), toNat_add_lt (by rw [he, hc2]; have := hl k hk; have := scalarComplement_lt k; omega), he, hc2]

end VG.Proof.Ed25519.Arm
