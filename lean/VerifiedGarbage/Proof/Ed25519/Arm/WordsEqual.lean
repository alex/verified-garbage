import VerifiedGarbage.Impl.Ed25519.Arm.FieldCheck
import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-! Compare bounded fields before modular reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem val16_inj {f g : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536)
    (hg : ∀ k < n, g k < 65536) : (∀ k < n, f k = g k) ↔ val16 f n = val16 g n := by
  refine ⟨val16_congr, fun h k hk => ?_⟩
  exact (val16_div hf hk).symm.trans ((congrArg (fun x => x / 2 ^ (16 * k) % 65536) h).trans (val16_div hg hk))

structure EqualInv (base : BitVec 32) (a b : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  zero : s.gpr .r9 = 0#32 ↔ ∀ i < k, limb s₀.mem (State.addr base) a i = limb s₀.mem (State.addr base) b i

theorem equalLimbs_ok {base : BitVec 32} {s₀ : State} (hc : Ctx base s₀) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096) (hz : s₀.gpr .r9 = 0#32) :
    WP isa (.block ((List.range 16).flatMap (equalLimb a b))) s₀ fun t =>
      EqualInv base a b s₀ 16 t := by
  refine wp_range_flatMap (M := isa) (EqualInv base a b s₀) (fun k s hk h => ?_) 16 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, ⟨fun _ _ h => by omega, fun _ => hz⟩⟩
  have hcs := hc.of_rest h.rest (by decide)
  refine ldr0_ok hcs (by omega) fun s1 u1 =>
    ldr0_ok (hcs.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)) (by omega) fun s2 u2 =>
    wp_dp (op2_reg _ _) fun s3 u3 => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (s2.gpr .r3).toNat = limb s₀.mem (State.addr base) a k := by
    rw [u2.other _ (by decide), u1.gpr, h.mem]; rfl
  have er : (s2.gpr .r2).toNat = limb s₀.mem (State.addr base) b k := by
    rw [u2.gpr, u1.mem, h.mem]; rfl
  have eqv : s2.gpr .r3 = s2.gpr .r2 ↔ limb s₀.mem (State.addr base) a k = limb s₀.mem (State.addr base) b k :=
    ⟨fun h => el.symm.trans ((congrArg BitVec.toNat h).trans er),
      fun h => BitVec.eq_of_toNat_eq (el.trans (h.trans er.symm))⟩
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (ht.rest (by decide))))), by rw [ht.mem, u3.mem, u2.mem, u1.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (s3.gpr .r9 ||| s3.gpr .r3 = 0#32) ↔ _
  rw [BitVec.or_eq_zero_iff, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.zero,
    u3.gpr]
  change (_ ∧ (s2.gpr .r3 ^^^ s2.gpr .r2 = 0#32)) ↔ _
  rw [BitVec.xor_eq_zero_iff, eqv]
  constructor
  · rintro ⟨hpre, hlast⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hpre i hi
    · exact hlast
  · intro h
    exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

theorem wordsEqual_ok {base : BitVec 32} {s : State} (hc : Ctx base s) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096)
    (hla : Lim s.mem (State.addr base) a) (hlb : Lim s.mem (State.addr base) b) :
    WP isa (.block (wordsEqual a b)) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr base) a = V s.mem (State.addr base) b) := by
  unfold wordsEqual
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (equalLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) a b ha hb hu.gpr)
    fun v hv => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (hv.rest.trans (ht.rest _)), by rw [ht.mem, hv.mem, hu.mem], ?_⟩
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (v.gpr .r9 = 0#32) ↔ _
  rw [hv.zero, hu.mem]
  exact val16_inj hla hlb

end VG.Proof.Ed25519.Arm
