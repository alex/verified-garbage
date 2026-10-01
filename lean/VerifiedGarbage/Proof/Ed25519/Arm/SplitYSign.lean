import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeKeep

/-! Untrusted: separate bit 255 while retaining all bounded field limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem bitNat_eq {q : Nat} (hq : q ≤ 1) : (q == 1).toNat = q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl <;> rfl

theorem splitYSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.block splitYSign) s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      V t.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % 2 ^ 255 ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1).toNat := by
  let f := limb s.mem (State.addr base) (offset 1)
  have hoff : offset (1 : Slot) = 128 := rfl
  have mf := mask15_facts (hl 1)
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have e2 : (s2.gpr .r2).toNat = f 15 / 32768 := by rw [u2.gpr, toNat_shr, u1.gpr]; rfl
  refine str0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 => ?_
  have m3 : s3.mem = s.mem.writeW (State.addr base + BitVec.ofNat 64 60) (s2.gpr .r2) := by
    rw [u3.mem, u2.mem, u1.mem]
  have f3 : Frame [⟨State.addr base + BitVec.ofNat 64 60, 4⟩] s.mem s3.mem := by
    rw [m3]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have r3 : Rest [.r2, .r3, .r4] s s3 := r2.trans (u3.rest _)
  refine wp_movw fun s4 u4 => wp_dp (op2_reg _ _) fun s5 u5 => ?_
  have r5 : Rest [.r2, .r3, .r4] s s5 := r3.trans ((u4.rest (by decide)).trans (u5.rest (by decide)))
  have e5 : (s5.gpr .r3).toNat = f 15 % 32768 := by
    rw [u5.gpr]
    change (s4.gpr .r3 &&& s4.gpr .r4).toNat = _
    rw [BitVec.toNat_and, u4.gpr, u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.gpr]
    change f 15 &&& (2 ^ 15 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  refine str0_ok (hc.of_rest r5 (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have mt : t.mem = s3.mem.writeW (State.addr base + BitVec.ofNat 64 (offset 1 + 60)) (s5.gpr .r3) := by
    rw [ht.mem, u5.mem, u4.mem]
  have ft : Frame [⟨State.addr base + BitVec.ofNat 64 (offset 1), 64⟩] s3.mem t.mem := by
    rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr base) (d := offset 1 + 60) (n := 4) (e := offset 1) (k := 64)
        (by decide) (by decide) (by decide))
  have ys : ∀ k < 16, limb s3.mem (State.addr base) (offset 1) k = f k :=
    limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  have yt : ∀ k < 16, limb t.mem (State.addr base) (offset 1) k = mask15 f k := by
    intro k hk
    rw [limb, mt]
    by_cases hk15 : k = 15
    · subst hk15
      rw [wd_write_self, e5]
      rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      change limb s3.mem (State.addr base) (offset 1) k = _
      rw [ys k hk]
      simp only [mask15, hk15, ite_false]
  have lt : AllLim t.mem base := (field_update 1 (smallFrame_lim f3 (by decide) hl) (frame_o ft)
    (fun k hk => by rw [yt k hk]; exact mf.2.2.1 k hk)).1
  refine ⟨⟨(r5.trans (ht.rest _)).mono (by decide), ?_⟩, lt, ?_, ?_⟩
  · exact (f3.mono (fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)).trans
      (ft.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · rw [V, val16_congr yt]
    have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
    have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
    omega
  · apply BitVec.eq_of_toNat_eq
    have hz : wd t.mem (State.addr base) 60 = (s2.gpr .r2).toNat := by
      rw [wd_frame ft (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)),
        wd, m3, Mem.readW_writeW_self32]
    change wd t.mem (State.addr base) 60 = _
    rw [hz, e2, toNat_imm (by have := Bool.toNat_le (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1); omega)]
    have he : V s.mem (State.addr base) (offset 1) / 2 ^ 255 = f 15 / 32768 := by
      have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
      have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
      omega
    rw [he, bitNat_eq mf.2.2.2]

end VG.Proof.Ed25519.Arm
