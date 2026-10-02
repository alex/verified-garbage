import VerifiedGarbage.Impl.Ed25519.Arm.FieldCheck
import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-! Summing sixteen bounded limbs cannot overflow and detects zero. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def limbSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => limbSum f n + f n

theorem limbSum_bound {f : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536) :
    limbSum f n ≤ 65535 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun k hk => hf k (by omega))
    have hn := hf n (by omega)
    simp only [limbSum, Nat.mul_succ]
    omega

theorem limbSum_zero (f : Nat → Nat) (n : Nat) : limbSum f n = 0 ↔ val16 f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [limbSum, val16_succ, Nat.add_eq_zero_iff, Nat.mul_eq_zero,
      Nat.ne_of_gt (Nat.two_pow_pos _), false_or, ih]

structure SumInv (b : BitVec 32) (o : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  value : (s.gpr .r9).toNat = limbSum (limb s₀.mem (State.addr b) o) k

theorem sumLimbs_ok {b : BitVec 32} {s₀ : State} (hc : Ctx b s₀) (o : Nat) (ho : o + 64 ≤ 4096)
    (hl : Lim s₀.mem (State.addr b) o) (hz : (s₀.gpr .r9).toNat = 0) :
    WP isa (.block ((List.range 16).flatMap (sumLimb o))) s₀ fun t => Rest [.r3, .r9] s₀ t ∧
      t.mem = s₀.mem ∧ (t.gpr .r9).toNat = limbSum (limb s₀.mem (State.addr b) o) 16 := by
  refine WP.mono (wp_range_flatMap (M := isa) (SumInv b o s₀) (fun k s hk h => ?_)
    16 (Nat.le_refl _) s₀ ⟨Rest.refl _ _, rfl, hz⟩) fun t ht => ⟨ht.rest, ht.mem, ht.value⟩
  refine ldr0_ok (hc.of_rest h.rest (by decide)) (by omega) fun u hu =>
    wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (u.gpr .r3).toNat = limb s₀.mem (State.addr b) o k := by rw [hu.gpr, h.mem]; rfl
  have es : (u.gpr .r9).toNat = limbSum (limb s₀.mem (State.addr b) o) k := by
    rw [hu.other _ (by decide), h.value]
  refine ⟨h.rest.trans ((hu.rest (by decide)).trans (ht.rest (by decide))),
    by rw [ht.mem, hu.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (u.gpr .r9 + u.gpr .r3).toNat = _
  rw [toNat_add_lt (by
    rw [es, el]
    have := limbSum_bound (fun j hj => hl j (by omega) : ∀ j < k, limb s₀.mem (State.addr b) o j < 65536)
    have := hl k hk
    omega), es, el]
  rfl

theorem wordsZero_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (o : Nat) (ho : o + 64 ≤ 4096)
    (hl : Lim s.mem (State.addr b) o) :
    WP isa (.block (wordsZero o)) s fun t => Rest [.r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr b) o = 0) := by
  unfold wordsZero
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (sumLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) o ho
    (by rw [hu.mem]; exact hl) (by rw [hu.gpr]; rfl)) fun v ⟨vr, vm, vv⟩ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (vr.trans (ht.rest _)), by rw [ht.mem, vm, hu.mem], ?_⟩
  have ve : v.gpr .r9 = BitVec.ofNat 32 (limbSum (limb s.mem (State.addr b) o) 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [vv, hu.mem, toNat_imm (by have := limbSum_bound hl; omega)]
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he, ve, ofNat_beq_zero (by have := limbSum_bound hl; omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact limbSum_zero _ _

end VG.Proof.Ed25519.Arm
