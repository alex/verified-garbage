import VerifiedGarbage.Impl.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg

/-! Establish the limb bounds for the whole field workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
variable {b : BitVec 32}

/-- Stores of register `r` into the `n` words from `o`. -/
theorem stores_ok {r : Reg} {o n : Nat} (ho : o + 4 * n ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (storeN r o n)) s fun s' =>
      (∀ j < n, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold storeN
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine str0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h3]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem initFields_ok {s : State} (hc : Ctx b s) :
    WP isa (.block initFields) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      ∀ i : Slot, env t.mem b i = 0 := by
  rw [initFields, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  refine WP.mono (stores_ok (r := .r3) (o := 64) (n := 352) (by decide)
    (hc.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide)))
    fun t ⟨hout, hf, _, hr⟩ => ?_
  have he : ∀ (i : Slot) k, k < 16 → limb t.mem (State.addr b) (offset i) k = 0 := by
    intro i k hk
    have h := hout (16 * i.val + k) (by omega)
    rw [hu.gpr] at h
    have hd : 64 + 4 * (16 * i.val + k) = offset i + 4 * k := by
      simp only [offset]
      omega
    rw [hd] at h
    exact h
  refine ⟨⟨(hu.rest (by decide)).trans (hr.mono (by decide)), ?_⟩,
    fun i k hk => by rw [he i k hk]; decide, fun i => ?_⟩
  · rw [← hu.mem]
    exact hf.sub fun r hmem => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hmem]; exact Region.sub_prefix (by decide)⟩
  · change VG.Proof.X25519.toFe (val16 (limb t.mem (State.addr b) (offset i)) 16) = 0
    rw [val16_congr (he i), val16_zero_fn]
    rfl

end VG.Proof.Ed25519.Arm
