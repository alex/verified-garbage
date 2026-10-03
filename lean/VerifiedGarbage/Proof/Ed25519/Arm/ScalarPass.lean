import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Proof.Ed25519.Arm.Field

/-! Merged from `Proof.Ed25519.Arm.ScalarNat`. -/
section
/-! Radix-65536 arithmetic for subgroup-order reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG.Proof.X25519.Arm VG.Spec.Ed25519 VG.Impl.Ed25519.Arm

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 65536 := by
  unfold scalarComplement; omega

theorem scalarComplement_val : val16 scalarComplement 16 + L + 1 = 2 ^ 256 := by decide

theorem scalarDouble_val {f : Nat → Nat} {bit : Nat}
    (hf : val16 f 16 < L) (hb : bit < 2) :
    val16 (out (fun k => 2 * f k) bit) 16 = 2 * val16 f 16 + bit := by
  have h := chain_val (fun k => 2 * f k) bit 16
  rw [val16_cmul] at h
  have bound := order_bound
  have hc : chain (fun k => 2 * f k) bit 16 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (fun k => 2 * f k) bit 16) with hz | hp
    · exact hz
    · have := Nat.le_mul_of_pos_right (2 ^ 256) hp
      change _ + 2 ^ 256 * _ = _ at h
      omega
  rw [hc, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem scalarSubtract_facts {f : Nat → Nat} (hf : val16 f 16 < 2 * L) :
    chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 ∧
    val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
      (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 % L := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := scalarComplement_val
  have hL := order_pos
  have hB := order_bound
  have hout := val16_lt (f := out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  have hcarry : chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 := by
    have : 2 ^ 256 * chain (fun k => f k + scalarComplement k) 1 16 < 2 ^ 256 * 2 := by omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  refine ⟨hcarry, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcarry with hz | ho
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 :=
      val16_congr fun _ _ => by rw [hz]; rfl
    rw [he, Nat.mod_eq_of_lt (by rw [hz] at hv; omega)]
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 =
        val16 (out (fun j => f j + scalarComplement j) 1) 16 :=
      val16_congr fun _ _ => by rw [ho]; rfl
    rw [he]
    have heq : val16 f 16 = val16 (out (fun j => f j + scalarComplement j) 1) 16 + L := by
      rw [ho] at hv; omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem scalarCompare_carry {f : Nat → Nat} (hf : val16 f 16 < 2 ^ 256) :
    chain (fun k => f k + scalarComplement k) 1 16 = if val16 f 16 < L then 0 else 1 := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := scalarComplement_val
  have hl := order_pos
  have hout := val16_lt (f := out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  split <;> omega

/-- Consume the low n bits of a word, in descending order. -/
def scalarConsumeBits (v n r : Nat) : Nat :=
  (List.range n).reverse.foldl (fun a j => (2 * a + v / 2 ^ j % 2) % L) r

theorem scalarConsumeBits_succ (v n r : Nat) :
    scalarConsumeBits v (n + 1) r = scalarConsumeBits v n ((2 * r + v / 2 ^ n % 2) % L) := by
  simp only [scalarConsumeBits, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem scalarConsumeBits_eq (v n r : Nat) (hr : r < L) :
    scalarConsumeBits v n r = (2 ^ n * r + v % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [scalarConsumeBits, List.range_zero, List.reverse_nil, List.foldl_nil,
      Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [scalarConsumeBits_succ, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a x z : Nat) : (a * (x % L) + z) % L = (a * x + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul]
    simp only [Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega

end VG.Proof.Ed25519.Arm
end

/-! Carry passes for doubling a remainder and subtracting the subgroup order. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem scalarDoublePass_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    {bit : Nat} (hb : bit < 2) (h5 : (s.gpr .r5).toNat = bit) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SR scalarDoubleSrc)) s
      (PassInv .r0 SR s (fun k => 2 * limb s.mem (State.addr b) SR k) bit 16) := by
  have hR : SR = 256 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; omega) (by omega) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarDoubleSrc
  refine ldr0_ok hct (by omega) fun u hu => wp_dp (op2_reg _ _) fun v hv => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨?_, (hu.rest (by decide)).trans (hv.rest (by decide)), by rw [hv.mem, hu.mem]⟩
  rw [hv.gpr]
  show (u.gpr .r3 + u.gpr .r3).toNat = _
  rw [toNat_add_lt (by rw [he]; have := hl k hk; omega), he]
  omega

theorem scalarSubtractPass_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    (h5 : (s.gpr .r5).toNat = 1) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SD scalarSubtractSrc)) s
      (PassInv .r0 SD s (fun k => limb s.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
  have hR : SR = 256 := rfl
  have hT : SD = 320 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; have := scalarComplement_lt k; omega) (by decide) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarSubtractSrc
  refine ldr0_ok hct (by omega) fun u hu => wp_movw fun v hv =>
    wp_dp (op2_reg _ _) fun w hw => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have hc2 : (v.gpr .r2).toNat = scalarComplement k := by
    rw [hv.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (scalarComplement_lt k)]
    exact Nat.mod_eq_of_lt (by have := scalarComplement_lt k; omega)
  refine ⟨?_, (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))), by
    rw [hw.mem, hv.mem, hu.mem]⟩
  rw [hw.gpr]
  show (v.gpr .r3 + v.gpr .r2).toNat = _
  rw [hv.other .r3 (by decide), toNat_add_lt (by rw [he, hc2]; have := hl k hk; have := scalarComplement_lt k; omega), he, hc2]

end VG.Proof.Ed25519.Arm
