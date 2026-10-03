import VerifiedGarbage.Proof.Ed25519.X86.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86.FreezeField
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec

/-! Place the affine x parity in the high bit of the canonical y encoding. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem sign_word (w : BitVec 32) :
    (w &&& 1).rotateRight 1 = BitVec.ofNat 32 ((w.toNat % 2) * 2 ^ 31) := by
  have he : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 32 by omega)]
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> decide

theorem field_parity (m : Mem) (x : BitVec 32) (o : Nat) : fe m x o % 2 = wv m x o % 2 := by
  rw [fe, num_shift]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.add_mod, Nat.mul_mod,
    show 2 ^ 32 % 2 = 0 from by decide, Nat.zero_mul, Nat.mod_mod]
  omega

theorem pointSign_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block pointSign) s fun t => IKeep x s t ∧ t.mem = s.mem ∧
      t.gpr .esi = BitVec.ofNat 32 ((fe s.mem x 64 % 2) * 2 ^ 31) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha =>
    Wp.wp_andi fun b hb => Wp.wp_ror (by decide) fun t ht => WP.block_nil ?_
  refine ⟨(IKeep.of_counter ha).trans ((IKeep.of_counter hb).trans (IKeep.of_counter ht)),
    by rw [ht.mem, hb.mem, ha.mem], ?_⟩
  rw [ht.gpr, hb.gpr, ha.gpr, field_parity]
  exact sign_word _

theorem fe_last_write {x : BitVec 32} (m : Mem) (w : BitVec 32) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    fe (m.writeW (addr x 124) w) x 96 =
      num (fun k => wv m x (96 + 4 * k)) 7 + 2 ^ 224 * w.toNat := by
  rw [fe, num_succ]
  have h : num (fun k => wv (m.writeW (addr x 124) w) x (96 + 4 * k)) 7 =
      num (fun k => wv m x (96 + 4 * k)) 7 := num_congr fun k hk => by
    apply congrArg BitVec.toNat
    exact wd_write_ne _ _ (by omega) (by omega) (Or.inl (by omega))
  rw [h]
  change _ + 2 ^ 224 * (wd (m.writeW (addr x 124) w) x 124).toNat = _
  rw [wd_write_self]

theorem encodeSign_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (parity y : Nat) (hp : parity ≤ 1) (hy : y < 2 ^ 255) (hv : fe s.mem x 96 = y)
    (hs : s.gpr .esi = BitVec.ofNat 32 (parity * 2 ^ 31)) :
    WP isa (.block encodeSign) s fun t => FieldKeep x s t ∧ fe t.mem x 96 = y + parity * 2 ^ 255 := by
  have top : wv s.mem x 124 < 2 ^ 31 := by
    have h := num_digit 7 (f := fun k => wv s.mem x (96 + 4 * k)) (n := 8)
      (fun k _ => BitVec.isLt _) (by decide)
    change fe s.mem x 96 / 2 ^ 224 % 2 ^ 32 = wv s.mem x 124 at h
    rw [hv] at h
    omega
  change (s.mem.readW (addr x 124) 32).toNat < 2 ^ 31 at top
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_add fun b hb _ => ?_
  have kb := (updKeep ha).trans (updKeep hb)
  have cb := kb.ctx hc
  refine Wp.wp_stm cb.edi (cb.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have val : (b.gpr .eax).toNat = wv s.mem x 124 + parity * 2 ^ 31 := by
    rw [hb.gpr, ha.gpr, ha.other .esi (by decide), hs, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show parity * 2 ^ 31 < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨kb.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩, ?_⟩
  · rw [ht.mem, hb.mem, ha.mem]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, hb.mem, ha.mem, fe_last_write _ _ hc.fit, val]
    have hsum : fe s.mem x 96 = num (fun k => wv s.mem x (96 + 4 * k)) 7 + 2 ^ 224 * wv s.mem x 124 := rfl
    rw [hsum] at hv
    omega

end VG.Proof.Ed25519.X86
