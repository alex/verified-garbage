import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Arm.Freeze

/-! Canonical point encoding in sixteen bounded limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem parity_limb {m : Mem} {base : Addr} {o : Nat} (hl : Lim m base o) :
    V m base o % 2 = limb m base o 0 % 2 := by
  have he := val16_div hl (k := 0) (by decide)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at he
  rw [← he, Nat.mod_mod_of_dvd _ (by decide)]
  rfl

theorem pointSign_ok {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) :
    WP isa (.block pointSign) s fun t => IKeep b s t ∧ t.mem = s.mem ∧
      (t.gpr .r10).toNat = (V s.mem (State.addr b) FR % 2) * 32768 := by
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 =>
    wp_mov (op2_lsl (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ⟨⟨(u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
    by rw [hm]; exact Frame.refl _ _⟩, hm, ?_⟩
  rw [u3.gpr, toNat_shl, u2.gpr]
  change (((s1.gpr .r3 &&& 1).toNat) * 32768) % 2 ^ 32 = _
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, u1.gpr]
  have he : (s.mem.readW (State.addr b + BitVec.ofNat 64 FR) 32).toNat =
      limb s.mem (State.addr b) FR 0 := rfl
  rw [he, ← parity_limb hl, Nat.mod_eq_of_lt (by omega)]

theorem encodeSign_ok {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : V s.mem (State.addr b) FR = y) (hs : (s.gpr .r10).toNat = (x % 2) * 32768) :
    WP isa (.block encodeSign) s fun t => Keep b s t ∧ Lim t.mem (State.addr b) FR ∧
      V t.mem (State.addr b) FR = y + (x % 2) * 2 ^ 255 := by
  have hR : FR = 1472 := rfl
  have hy' : val16 (limb s.mem (State.addr b) FR) 15 +
      2 ^ 240 * limb s.mem (State.addr b) FR 15 = y := hv
  have hb : limb s.mem (State.addr b) FR 15 < 32768 := by omega
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  have hr2 : Rest [.r3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have he : (s2.gpr .r3).toNat = limb s.mem (State.addr b) FR 15 + (x % 2) * 32768 := by
    rw [u2.gpr]
    change (s1.gpr .r3 + s1.gpr .r10).toNat = _
    rw [u1.other .r10 (by decide), u1.gpr]
    have hread : (s.mem.readW (State.addr b + BitVec.ofNat 64 (FR + 60)) 32).toNat =
        limb s.mem (State.addr b) FR 15 := rfl
    rw [toNat_add_lt (by rw [hread, hs]; omega), hread, hs]
  refine str0_ok (hc.of_rest hr2 (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have hm : t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (FR + 60)) (s2.gpr .r3) := by
    rw [ht.mem, u2.mem, u1.mem]
  have epre : ∀ k < 15, limb t.mem (State.addr b) FR k = limb s.mem (State.addr b) FR k := by
    intro k hk
    rw [limb, hm, wd_write_other _ _ _ (by omega) (by omega) (by omega)]
    rfl
  have elast : limb t.mem (State.addr b) FR 15 =
      limb s.mem (State.addr b) FR 15 + (x % 2) * 32768 := by
    rw [limb, hm, wd_write_self, he]
  refine ⟨⟨(hr2.trans (ht.rest _)).mono (by decide), ?_⟩, ?_, ?_⟩
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  · intro k hk
    rcases Nat.lt_or_ge k 15 with hk' | hk'
    · rw [epre k hk']; exact hl k hk
    · rw [show k = 15 by omega, elast]; omega
  · rw [V, val16_succ, val16_congr epre, elast]
    change val16 (limb s.mem (State.addr b) FR) 15 +
      2 ^ 240 * (limb s.mem (State.addr b) FR 15 + (x % 2) * 32768) = _
    omega

theorem pointEncode_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa pointEncode s fun t => IKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      V t.mem (State.addr base) FR =
        (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  refine WP.seq (WP.mono (pointAffine_ok hc hl) fun a ⟨ka, la, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (freeze_ok (ka.ctx hc) la 0) fun b ⟨kb, lb, eb, lxb, bx⟩ => ?_
  have kab : IKeep base s b := ka.trans (IKeep.of_keep kb)
  rw [WP.block_append_iff]
  refine WP.mono (pointSign_ok (kab.ctx hc) lxb) fun c ⟨kc, mc, cx⟩ => ?_
  have kabc := kab.trans kc
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok (kabc.ctx hc) (by rw [mc]; exact lb) 1)
    fun d ⟨kd, _, _, lyd, dy⟩ => ?_
  have kabcd := kabc.trans (IKeep.of_keep kd)
  have dx : (d.gpr .r10).toNat =
      ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 32768 := by
    rw [kd.rest.gpr .r10 (by decide), cx, bx, ax]
  rw [mc, eb, ay] at dy
  refine WP.mono (encodeSign_ok (kabcd.ctx hc) lyd _ _
    (Nat.lt_trans (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨kt, lt, vt⟩ => ?_
  exact ⟨kabcd.trans (IKeep.of_keep kt), lt, vt⟩

end VG.Proof.Ed25519.Arm
