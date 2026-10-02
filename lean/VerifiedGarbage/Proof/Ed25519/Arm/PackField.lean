import VerifiedGarbage.Proof.Ed25519.Arm.Packed

/-! Store bounded field limbs in a compact 32-byte buffer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PackInv (p : Addr) (f : Nat → Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3] s0 s
  frame : Frame [⟨p, 2 * k⟩] s0.mem s.mem
  b0 : ∀ i < k, s.mem (p + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (f i)
  b1 : ∀ i < k, s.mem (p + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (f i / 256)

theorem packField_ok {b p : BitVec 32} {a dst : Nat} {s0 : State} (hc : Ctx b s0)
    (ha : a + 64 ≤ 4096) (hl : Lim s0.mem (State.addr b) a) (hd : dst + 32 ≤ 4096)
    (hp : s0.gpr .r12 = p) (hfit : p.toNat + dst + 32 ≤ 2 ^ 32)
    (hw : ∀ i < 32, InRegions s0.wr (State.addr p + BitVec.ofNat 64 (dst + i)) 1)
    (hsep : (⟨State.addr b + BitVec.ofNat 64 a, 64⟩ : Region).Disjoint
      ⟨State.addr p + BitVec.ofNat 64 dst, 32⟩) :
    WP isa (.block (packField a dst)) s0 fun t => Rest [.r3] s0 t ∧
      Frame [⟨State.addr p + BitVec.ofNat 64 dst, 32⟩] s0.mem t.mem ∧
      packedV t.mem (State.addr p + BitVec.ofNat 64 dst) = V s0.mem (State.addr b) a := by
  let O := State.addr p + BitVec.ofNat 64 dst
  refine WP.mono (wp_range_flatMap (M := isa) (PackInv O (limb s0.mem (State.addr b) a) s0)
    (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega, fun _ h => by omega⟩)
    fun t ht => ⟨ht.rest, ht.frame, packedV_eq hl ht.b0 ht.b1⟩
  have hcs := hc.of_rest h.rest (by decide)
  have hp' : s.gpr .r12 = p := (h.rest.gpr _ (by decide)).trans hp
  have he : wd s.mem (State.addr b) (a + 4 * k) = limb s0.mem (State.addr b) a k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.sub_left (Offset.sub _ (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
  unfold packStep
  refine ldr0_ok hcs (by omega) fun s1 u1 => ?_
  have e1 : (s1.gpr .r3).toNat = limb s0.mem (State.addr b) a k := by rw [u1.gpr]; exact he
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [u1.other _ (by decide), hp', addr_add (by omega)]; simp only [O, Offset.add_add])
    (by rw [u1.wr, h.rest.wr]; simpa only [O, Offset.add_add] using hw (2 * k) (by omega))
    fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hp', addr_add (by omega)]
        simp only [O, Offset.add_add, Nat.add_assoc])
    (by rw [u3.wr, u2.wr, u1.wr, h.rest.wr]
        simpa only [O, Offset.add_add, Nat.add_assoc] using hw (2 * k + 1) (by omega))
    fun t ht => WP.block_nil ?_
  have hm : t.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * k)) ((s1.gpr .r3).setWidth 8)).writeW
      (O + BitVec.ofNat 64 (2 * k + 1)) ((s1.gpr .r3 >>> 8).setWidth 8) := by
    rw [ht.mem, u3.gpr, u2.gpr, u3.mem, u2.mem, u1.mem]
  have ne : ∀ i j : Nat, i < 32 → j < 32 → i ≠ j → O + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans
    ((u3.rest (by decide)).trans (ht.rest _)))), ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]; exact h.b0 i hi
    · rw [ite_eq_left rfl]; exact byte_eq e1
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega)),
        ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
      exact h.b1 i hi
    · rw [ite_eq_left rfl]; exact byte_eq (by rw [toNat_shr, e1])

end VG.Proof.Ed25519.Arm
