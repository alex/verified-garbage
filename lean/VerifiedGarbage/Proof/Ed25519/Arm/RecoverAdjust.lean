import VerifiedGarbage.Impl.Ed25519.Arm.FieldCheck
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Ed25519.Arm.Freeze
import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode

/-! Merged from `Proof.Ed25519.Arm.RecoverParity`. -/
section
/-! Merged from `Proof.Ed25519.Arm.FieldCheck`. -/
section
/-! Merged from `Proof.Ed25519.Arm.WordsZero`. -/
section
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
end

/-! Canonical representatives give exact field comparisons. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fieldZero_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b) (a : Slot) :
    WP isa (fieldZero a) s fun t => Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = env s.mem b ∧
      t.z = decide (env s.mem b a = 0) := by
  refine WP.seq (WP.mono (freeze_ok hc hl a) fun u ⟨uk, ul, ue, uf, uv⟩ => ?_)
  refine WP.mono (wordsZero_ok (uk.ctx hc) FR (by decide) uf) fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m b) tm).trans ue, ?_⟩
  rw [tz, uv]
  have he : (env s.mem b a).val = 0 ↔ env s.mem b a = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (a b : Slot) :
    WP isa (fieldEqual a b) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      (∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i) ∧
      t.z = decide (env s.mem base a = env s.mem base b) := by
  refine WP.seq (WP.mono (fieldCode_ok [.sub 21 a b] hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (fieldZero_ok (uk.ctx hc) ul 21) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨uk.trans tk, tl, fun i hi => ?_, ?_⟩
  · rw [te, ue]
    exact Function.update_of_ne hi _ _
  · rw [tz, ue]
    change decide (env s.mem base a - env s.mem base b = 0) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      fun _ _ => ⟨fun _ => by grind, fun _ => by grind⟩]

end VG.Proof.Ed25519.Arm
end

/-! Sign checks use the canonical x-coordinate and the saved sign bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem IKeep.sign {base : BitVec 32} {s t : State} (h : IKeep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem Keep.sign {base : BitVec 32} {s t : State} (h : Keep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := (IKeep.of_keep h).sign

theorem parity_match (x : Nat) (b : Bool) : decide (x % 2 = b.toNat) = ((x % 2 == 1) == b) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (b : Bool)
    (hl : Lim s.mem (State.addr base) FR)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block recoverParity) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = ((V s.mem (State.addr base) FR % 2 == 1) == b) := by
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ldr0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : (s3.gpr .r9).toNat = V s.mem (State.addr base) FR % 2 := by
    rw [u3.other _ (by decide), u2.gpr]
    change (s1.gpr .r3 &&& (1 : BitVec 32)).toNat = _
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, u1.gpr]
    exact (parity_limb hl).symm
  have es : s3.gpr .r2 = BitVec.ofNat 32 b.toNat := by rw [u3.gpr, u2.mem, u1.mem]; exact hb
  refine ⟨r2.trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans (ht.rest _))),
    by rw [ht.mem, u4.mem, u3.mem, u2.mem, u1.mem], ?_⟩
  have sub0 : s4.gpr .r9 - (0 : BitVec 32) = s4.gpr .r9 := BitVec.sub_zero _
  rw [hz, sub0, u4.gpr]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 == 0) = _
  rw [← parity_match]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 = 0#32) ↔ _
  rw [BitVec.xor_eq_zero_iff]
  have en : (s3.gpr .r2).toNat = b.toNat := by rw [es, toNat_imm (by cases b <;> decide)]
  constructor
  · intro h
    exact he.symm.trans ((congrArg BitVec.toNat h).trans en)
  · intro h
    exact BitVec.eq_of_toNat_eq (he.trans (h.trans en.symm))

end VG.Proof.Ed25519.Arm
end

/-! Choose the encoded sign and finish the extended coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov .r9 (.imm b.toNat)]) s fun t =>
      Rest [.r9] s t ∧ t.mem = s.mem ∧ t.gpr .r9 = BitVec.ofNat 32 b.toNat := by
  refine wp_mov (op2_imm (by cases b <;> decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

theorem recoverSuccess_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa recoverSuccess s fun t => Keep base s t ∧ AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (env s.mem base 0) (env s.mem base 1) := by
  refine WP.seq (WP.mono (fieldCode_ok recoverSuccessOps hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (returnFlag_ok u true) fun t ⟨tr, tm, tv⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm ▸ ul, tv, ?_⟩
  rw [tm, ue]
  rfl

theorem adjustBranch_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hz : s.z = (((env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) s fun t =>
      Keep base s t ∧ AllLim t.mem base ∧ env t.mem base 0 = signedX (env s.mem base 0) b ∧
      env t.mem base 1 = env s.mem base 1 := by
  apply WP.ite (((env s.mem base 0).val % 2 == 1) == b) (by simp only [VG.Arm.eval, hz])
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, hl, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc hl) fun t ⟨tk, tl, te⟩ => ?_
    refine ⟨tk, tl, ?_, ?_⟩
    · rw [te]
      change 0 - env s.mem base 0 = signedX (env s.mem base 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [te]; rfl

theorem recoverAdjustSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa recoverAdjustSign s fun t => Keep base s t ∧ AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (signedX (env s.mem base 0) b) (env s.mem base 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hc hl 0) fun a ⟨ak, al, ae, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_
  have ck : Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
  have ce : env c.mem base = env s.mem base := (congrArg (fun m => env m base) cm).trans ae
  have ch : c.z = (((env c.mem base 0).val % 2 == 1) == b) := by rw [cz, av, ce]
  refine WP.seq (WP.mono (adjustBranch_ok (ck.ctx hc) (cm ▸ al) b ch) fun d ⟨dk, dl, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok ((ck.trans dk).ctx hc) dl) fun t ⟨tk, tl, tr, tp⟩ => ?_
  exact ⟨(ck.trans dk).trans tk, tl, tr, by rw [tp, dx, dy, ce]⟩

end VG.Proof.Ed25519.Arm
