import VerifiedGarbage.Proof.Bignum.X86_64.Exp

/-!
# Multiword arithmetic on x86-64: `vg_rsa_public`'s check of the modulus

`invalid` sets ZF iff the `k` bytes of `m` make a valid modulus
(`Spec.Rsa.modulusValid`), for `64 ≤ k ≤ 1024` (`invalid_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem os2ip_foldl (a : Nat) (bs : List Byte) :
    bs.foldl (fun x b => 256 * x + b.toNat) a = a * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
  induction bs generalizing a with
  | nil => simp [Spec.Rsa.os2ip]
  | cons b bs ih =>
    show bs.foldl _ (256 * a + b.toNat) = a * 256 ^ (bs.length + 1) + bs.foldl _ (256 * 0 + b.toNat)
    rw [ih, ih (256 * 0 + b.toNat), Nat.pow_succ, Nat.add_mul, Nat.mul_zero, Nat.zero_add, Nat.mul_assoc,
      Nat.mul_comm (256 ^ bs.length) 256, Nat.add_assoc, Nat.mul_left_comm]

theorem os2ip_cons (b : Byte) (bs : List Byte) :
    Spec.Rsa.os2ip (b :: bs) = b.toNat * 256 ^ bs.length + Spec.Rsa.os2ip bs := by
  show List.foldl (fun x (b : Byte) => 256 * x + b.toNat) (256 * 0 + b.toNat) bs = _
  rw [os2ip_foldl, Nat.mul_zero, Nat.zero_add]

theorem os2ip_lt (bs : List Byte) : Spec.Rsa.os2ip bs < 256 ^ bs.length := by
  rw [← pre_len]; exact pre_lt bs (Nat.le_refl _)

theorem pow256_eq (a : Nat) : (256 : Nat) ^ a = 2 ^ (8 * a) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

theorem pow256_64 : (256 : Nat) ^ 64 = 2 ^ 512 := (pow256_eq 64).trans (congrArg (2 ^ ·) rfl)

theorem modulusValid_nat {n0 r l P k : Nat} (hn0 : n0 < 256) (hr : r < P) (hP : P = 256 ^ (k - 1))
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hodd : (n0 * P + r) % 2 = l % 2) :
    Spec.Rsa.modulusValid (n0 * P + r) k =
      !(decide (n0 < 1) || decide (l % 2 < 1) || decide ((k - 64) * 256 + n0 < 128)) := by
  unfold Spec.Rsa.modulusValid
  by_cases h0 : n0 = 0
  · subst h0
    simp only [Nat.zero_mul, Nat.zero_add, ← hP, show ¬ P ≤ r by omega, decide_false, Bool.and_false,
      show (0 < 1) = True from propext ⟨fun _ => trivial, fun _ => by decide⟩, decide_true, Bool.true_or,
      Bool.not_true]
  have hge : P ≤ n0 * P + r := Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by omega))
  have hlt : n0 * P + r < 2 ^ 8192 := by
    have h1 : n0 * P + r < 256 * P := by
      have := Nat.mul_le_mul_right P (show n0 + 1 ≤ 256 by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h2 : 256 * P = 2 ^ (8 * k) := by
      rw [hP, ← pow256_eq, ← Nat.pow_succ']; congr 1; omega
    have h3 := (fun B (hB : 8 * k ≤ B) => Nat.pow_le_pow_right (n := 2) (by decide) hB) 8192 (by omega)
    omega
  have h511 : decide (2 ^ 511 ≤ n0 * P + r) = !decide ((k - 64) * 256 + n0 < 128) := by
    by_cases hk64 : k = 64
    · subst hk64
      have hP' : P = 2 ^ 504 := hP.trans ((pow256_eq _).trans (congrArg (2 ^ ·) rfl))
      rw [hP'] at hr ⊢
      rw [show (64 - 64) * 256 + n0 = n0 by omega]
      by_cases h128 : 128 ≤ n0
      · simp only [show 2 ^ 511 ≤ n0 * 2 ^ 504 + r by omega, show ¬ n0 < 128 by omega, decide_true,
          decide_false, Bool.not_false]
      · simp only [show ¬ 2 ^ 511 ≤ n0 * 2 ^ 504 + r by omega, show n0 < 128 by omega, decide_true,
          decide_false, Bool.not_true]
    · have hP' : 2 ^ 512 ≤ P := by
        rw [hP, ← pow256_64]; exact Nat.pow_le_pow_right (by decide) (by omega)
      simp only [show 2 ^ 511 ≤ n0 * P + r by omega, show ¬ (k - 64) * 256 + n0 < 128 by omega, decide_true,
        decide_false, Bool.not_false]
  rw [← hP]
  simp only [h511, show P ≤ n0 * P + r from hge, show n0 * P + r < 2 ^ 8192 from hlt, show ¬ n0 < 1 by omega,
    decide_true, decide_false, Bool.and_true, Bool.false_or, Bool.not_or]
  by_cases hl : l % 2 = 1
  · simp [hl, hodd]
  · simp [show l % 2 = 0 by omega, hodd]

/-- `m` is a valid modulus iff its first byte is not zero, its last byte is
odd, and `256 (k - 64) + m[0] ≥ 128`, for `64 ≤ k ≤ 1024`. -/
theorem modulusValid_iff {nb : List Byte} {k : Nat} (hlen : nb.length = k) (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k =
      !(decide ((nb[0]'(by omega)).toNat < 1) || decide ((nb[k - 1]'(by omega)).toNat % 2 < 1) ||
        decide ((k - 64) * 256 + (nb[0]'(by omega)).toNat < 128)) := by
  have hodd : Spec.Rsa.os2ip nb % 2 = (nb[k - 1]'(by omega)).toNat % 2 := by
    have := pre_succ nb (i := k - 1) (by omega)
    rw [show k - 1 + 1 = nb.length by omega, pre_len] at this
    omega
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, nb = b :: bs := by
    cases nb with
    | nil => simp at hlen; omega
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hl : bs.length = k - 1 := by simp at hlen; omega
  rw [os2ip_cons, hl] at hodd ⊢
  have hr := os2ip_lt bs
  rw [hl] at hr
  exact modulusValid_nat b.isLt hr rfl hk hk' hodd

theorem ofInt_m1 : BitVec.ofInt 64 (-1) = -(1#64) := by decide

/-- The masks of borrows, or'ed. -/
theorem mask_or' (a b : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool a)) |||
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool b)) = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (a || b)) := by
  cases a <;> cases b <;> decide

theorem mask_beq (a : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool a) == 0) = !a := by
  cases a <;> decide

theorem sw_toNat (b : Byte) : (BitVec.setWidth 64 b).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem sw_and1 (b : Byte) : (BitVec.setWidth 64 b &&& 1).toNat = b.toNat % 2 := by
  rw [BitVec.toNat_and, sw_toNat, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = 64#64 := by decide
theorem sx128 : (BitVec.signExtend 64 (128 : BitVec 32)).toNat = 128 := by decide

theorem ror_k {k : Nat} (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    ((BitVec.ofNat 64 k - 64#64).rotateRight 56).toNat = (k - 64) * 256 := by
  have e : BitVec.ofNat 64 k - 64#64 = BitVec.ofNat 64 (k - 64) := by
    rw [show (64#64) = BitVec.ofNat 64 64 from rfl, show k = (k - 64) + 64 by omega, ← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel, Nat.add_sub_cancel]
  rw [e, ror56_toNat _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

theorem invalid_ok {s : State} {np : Addr} {k : Nat} {nb : List Byte}
    (hdx : s.gpr .rdx = np) (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 i) 1)
    (hb : ∀ i (h : i < k), s.mem (np + BitVec.ofNat 64 i) = nb[i]'(by omega)) :
    WP isa (.block invalid) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbp, .rsi] s t := by
  refine WP.mono (WP.keep [.rax, .rbp, .rsi] (Q := fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hr0 : InRegions (s.rd ++ s.wr) np 1 := by have := hrd 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have hb0 : s.mem np = nb[0]'(by omega) := by have := hb 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have hlast : np + BitVec.ofNat 64 k * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = np + BitVec.ofNat 64 (k - 1) := by
    have e : BitVec.ofNat 64 k = BitVec.ofNat 64 (k - 1) + 1#64 := by
      rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]; congr 1; omega
    rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, e, ofInt_m1, ← BitVec.sub_eq_add_neg,
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  unfold invalid
  xrun [State.ea, at0, hdx, hcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hr0, hb0, hlast,
    hrd (k - 1) (by omega), hb (k - 1) (by omega)]
  have hn0 := (nb[0]'(by omega)).isLt
  rw [mask_or', mask_or', BitVec.and_self, mask_beq, modulusValid_iff hlen hk hk', sw_toNat, sw_and1,
    show BitVec.toNat (1 : BitVec 64) = 1 from rfl, sx64, sx128, BitVec.toNat_add, ror_k hk hk', sw_toNat, Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]

end VG.Proof.Bignum.X86_64
