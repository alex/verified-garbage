import VerifiedGarbage.Proof.Ed25519.Arm.Packed

/-! Untrusted: load a compact field into bounded sixteen-bit limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem toNat_setWidth8 (v : BitVec 8) : (v.setWidth 32).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]

theorem unpackField_ok {b p : BitVec 32} {o src : Nat} {s0 : State} (hc : Ctx b s0)
    (ho : o + 64 ≤ 4096) (hs : src + 32 ≤ 4096) (hp : s0.gpr .r12 = p)
    (hfit : p.toNat + src + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 (src + i)) 1)
    (hsep : (⟨State.addr p + BitVec.ofNat 64 src, 32⟩ : Region).Disjoint
      ⟨State.addr b + BitVec.ofNat 64 o, 64⟩) :
    WP isa (.block (unpackField o src)) s0 fun t => Rest [.r2, .r3] s0 t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s0.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o = packedV s0.mem (State.addr p + BitVec.ofNat 64 src) := by
  let O := State.addr p + BitVec.ofNat 64 src
  refine WP.mono (fill_regs_ok (ws := [.r2, .r3]) (by decide) (src := unpackSrc src)
    (f := packedLimb s0.mem O) hc ho (fun k hk s h => ?_))
    fun t ht => ⟨ht.rest, ht.frame, fun k hk => by rw [ht.outs k hk]; exact packedLimb_lt _ _ _,
      val16_congr ht.outs⟩
  have hp' : s.gpr .r12 = p := (h.rest.gpr _ (by decide)).trans hp
  have href : ∀ i < 32, s.mem (O + BitVec.ofNat 64 i) = s0.mem (O + BitVec.ofNat 64 i) :=
    fun i hi => h.frame.bytes (fun r hm => by
      rw [List.mem_singleton.mp hm]
      exact hsep.sub_right (Region.sub_prefix (by omega))) (by decide : 32 ≤ 2 ^ 64) hi
  unfold unpackSrc
  refine wp_ldrb (a := O + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [hp', addr_add (by omega)]; simp only [O, Offset.add_add])
    (by rw [h.rest.rd, h.rest.wr]; simpa only [O, Offset.add_add] using hr (2 * k) (by omega))
    fun s1 u1 => ?_
  refine wp_ldrb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u1.other _ (by decide), hp', addr_add (by omega)]; simp only [O, Offset.add_add, Nat.add_assoc])
    (by rw [u1.rd, u1.wr, h.rest.rd, h.rest.wr]
        simpa only [O, Offset.add_add, Nat.add_assoc] using hr (2 * k + 1) (by omega))
    fun s2 u2 => wp_dp (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have el : (s2.gpr .r3).toNat = byteN s0.mem O (2 * k) := by
    rw [u2.other _ (by decide), u1.gpr, toNat_setWidth8, href _ (by omega)]
    rfl
  have eh : (s2.gpr .r2 <<< 8).toNat = 256 * byteN s0.mem O (2 * k + 1) := by
    rw [u2.gpr, u1.mem, toNat_shl, toNat_setWidth8, href _ (by omega)]
    have := (s0.mem (O + BitVec.ofNat 64 (2 * k + 1))).isLt
    simp only [byteN]
    omega
  refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [u3.mem, u2.mem, u1.mem]⟩
  rw [u3.gpr]
  change (s2.gpr .r3 + (s2.gpr .r2 <<< 8)).toNat = _
  rw [toNat_add_lt (by
    rw [el, eh]
    exact Nat.lt_trans (packedLimb_lt _ _ _) (by decide)), el, eh]
  rfl

end VG.Proof.Ed25519.Arm
