import VerifiedGarbage.Proof.Ed25519.Arm.ScalarAddPass
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarWide

/-! Add the 256-bit scalar to all 512 product bits, carrying across both halves. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarWide_split (m : Mem) (b : BitVec 32) :
    val16 (accw m (State.addr b)) 32 = V m (State.addr b) ACC + 2 ^ 256 * V m (State.addr b) (ACC + 64) := by
  rw [show (32 : Nat) = 16 + 16 from rfl, val16_append]
  have he : val16 (fun k => accw m (State.addr b) (16 + k)) 16 = V m (State.addr b) (ACC + 64) := by
    apply val16_congr
    intro k _
    unfold accw limb
    rw [show ACC + 4 * (16 + k) = ACC + 64 + 4 * k by omega]
  rw [he]
  rfl

theorem scalarWideAdd_ok {b : BitVec 32} {r : Nat} (hr : r + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (lr : Lim s.mem (State.addr b) r)
    (la : ∀ k < 32, accw s.mem (State.addr b) k < 65536) :
    WP isa (.block (scalarWideAdd r)) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      (∀ k < 32, accw t.mem (State.addr b) k < 65536) ∧
      val16 (accw t.mem (State.addr b)) 32 + 2 ^ 512 * (t.gpr .r5).toNat =
        val16 (accw s.mem (State.addr b)) 32 + V s.mem (State.addr b) r := by
  have hA : ACC = 1472 := rfl
  have ll : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega)
  have lh : Lim s.mem (State.addr b) (ACC + 64) := by
    intro k hk
    have he : limb s.mem (State.addr b) (ACC + 64) k = accw s.mem (State.addr b) (16 + k) := by
      unfold limb accw; rw [show ACC + 64 + 4 * k = ACC + 4 * (16 + k) by omega]
    rw [he]; exact la _ (by omega)
  rw [scalarWideAdd, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Rest [.r5, .r6] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 := hc.of_rest k2 (by decide)
  refine WP.append (scalarAddPass_ok (x := ACC) (y := r) (by decide) (by omega) (Or.inr (Or.inr hr))
    hc2 (m2 ▸ ll) (m2 ▸ lr) (by decide : 0 < 65536) (by rw [u2.gpr]; rfl)
    (by rw [u2.other _ (by decide), u1.gpr])) fun s3 h3 => ?_
  obtain ⟨f3, l3, v3⟩ := scalarPass_result hc2 h3
  have hc3 := hc2.of_rest h3.rest (by decide)
  have hs3 : Lim s3.mem (State.addr b) (ACC + 64) :=
    fun k hk => by
      rw [limb_frame f3 (fun z hz j hj => by
        rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk, m2]
      exact lh k hk
  have hi3 : V s3.mem (State.addr b) (ACC + 64) = V s.mem (State.addr b) (ACC + 64) := by
    apply val16_congr
    intro k hk
    rw [limb_frame f3 (fun z hz j hj => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk, m2]
  have carry3 : (s3.gpr .r5).toNat < 65536 := by
    rw [h3.r5]
    exact chain_lt (fun k hk => by have := ll k hk; have := lr k hk; rw [m2]; omega)
      (by decide) 16 (Nat.le_refl _)
  refine WP.mono (scalarCarryPass_ok (x := ACC + 64) (by decide) hc3 hs3 carry3 rfl
    (by rw [h3.rest.gpr _ (by decide), u2.other _ (by decide), u1.gpr])) fun t ht => ?_
  obtain ⟨ft, lt, vt⟩ := scalarPass_result hc3 ht
  have lrt : ∀ k < 16, limb t.mem (State.addr b) ACC k = limb s3.mem (State.addr b) ACC k :=
    limb_frame ft fun z hz j hj => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have vlo : V t.mem (State.addr b) ACC = V s3.mem (State.addr b) ACC := val16_congr lrt
  refine ⟨(k2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans (ht.rest.mono (by decide))), ?_, ?_, ?_⟩
  · have f3' : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem s3.mem := by
      rw [← m2]
      exact f3.sub fun z hz => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hz]; exact Region.sub_prefix (by decide)⟩
    exact f3'.trans (ft.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact Offset.sub _ (by decide) (by decide)⟩)
  · intro k hk
    rcases Nat.lt_or_ge k 16 with hk16 | hk16
    · rw [show accw t.mem (State.addr b) k = limb t.mem (State.addr b) ACC k from rfl, lrt k hk16]
      exact l3 k hk16
    · have he : accw t.mem (State.addr b) k = limb t.mem (State.addr b) (ACC + 64) (k - 16) := by
        unfold accw limb; rw [show ACC + 4 * k = ACC + 64 + 4 * (k - 16) by omega]
      rw [he]; exact lt _ (by omega)
  · rw [val16_add, Nat.add_zero, m2] at v3
    change V s3.mem (State.addr b) ACC + _ = V s.mem (State.addr b) ACC + V s.mem (State.addr b) r at v3
    change V t.mem (State.addr b) (ACC + 64) + _ = V s3.mem (State.addr b) (ACC + 64) + _ at vt
    rw [hi3] at vt
    rw [scalarWide_split, scalarWide_split, vlo]
    omega

end VG.Proof.Ed25519.Arm
