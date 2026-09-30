import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_expand_mask_poly`

Untrusted: everything here is checked by Lean. Coefficient `k` of a group
reads the 32-bit word at byte `⌊ck/8⌋` of the group, whose bits from
`ck mod 8` on are those of the output from bit `ci` on (`word_bits`: only
its first 3 bytes matter); it stores `γ₁` minus their low `c` bits modulo `q`
(`etaF_eq`) to `a[i]` (`emCoef_ok`). A group stores 4 coefficients
(`emBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt coeffAt)

/-! ## Values -/

/-- `(g - x) mod q`, computed with a mask from the borrow. -/
theorem etaF_eq {g x : BitVec 32} (hg : g.toNat < q) (hx : x.toNat < q + g.toNat) :
    etaF g x = zw (ofInt ((g.toNat : Int) - x.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat]
  simp only [ofInt, Fin.val_ofNat]
  simp only [q] at hg hx ⊢
  unfold etaF
  by_cases h : g.toNat < x.toNat
  · rw [decide_eq_true h, show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true) &&& qImm) = qImm by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show qImm.toNat = 8380417 from rfl]
    omega
  · rw [decide_eq_false h, show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false) &&& qImm) = 0 by decide,
      BitVec.toNat_add, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-- Bit `j` of a 32-bit little-endian word. -/
theorem readW32_getLsbD (m : Mem) (a : Addr) {j : Nat} (hj : j < 32) :
    (m.readW a 32).getLsbD j = (m (a + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [Mem.readW_byte m a (by omega), BitVec.getLsbD_extractLsb']
  simp only [show j % 8 < 8 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- The `c` bits from bit `sh` of the word at `a` are those of `X` from bit
`8o + sh`, if its first 3 bytes are those of `X` from byte `o`. -/
theorem word_bits (m : Mem) (a : Addr) (X : List Byte) {o sh c : Nat} (hc : sh + c ≤ 24)
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (o + b) 0) :
    (m.readW a 32).toNat / 2 ^ sh % 2 ^ c = leNat X / 2 ^ (8 * o + sh) % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · simp only [hj, decide_true, Bool.true_and]
    rw [← BitVec.getLsbD, readW32_getLsbD m a (j := j + sh) (by omega), hb ((j + sh) / 8) (by omega),
      testBit_leNat, show (j + (8 * o + sh)) / 8 = o + (j + sh) / 8 by omega,
      show (j + (8 * o + sh)) % 8 = (j + sh) % 8 by omega]
  · simp [hj]

/-! ## A coefficient -/

/-- The value stored for coefficient `i` of `c` bits from the output `X`. -/
abbrev emV (X : List Byte) (c i : Nat) : BitVec 32 :=
  zw (ofInt (((2 ^ (c - 1) : Nat) : Int) - (leNat X / 2 ^ (i * c) % 2 ^ c : Nat)))

theorem emCoef_run (c k : Nat) (hk : c * k % 8 < 8) (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) 4)
    (h1 : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (emCoef c k)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 (4 * k))
        (etaF (BitVec.ofNat 32 (2 ^ (c - 1)))
          (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) 32 >>> (c * k % 8) &&&
            BitVec.ofNat 32 (2 ^ c - 1)))) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by
    unfold writesOnly emCoef
    split <;> rfl)
  by_cases hs : c * k % 8 = 0
  · simp only [emCoef, hs, ite_true, List.nil_append, List.cons_append]
    xrun [h0, h1]
    rw [BitVec.ushiftRight_zero]; rfl
  · simp only [emCoef, hs, ite_false, List.cons_append, List.nil_append]
    xrun [h0, h1, show 1 ≤ c * k % 8 by omega, show c * k % 8 ≤ 31 by omega]
    rfl

/-- The widths of the coefficients. -/
def emOk (c : Nat) : Prop := c = 18 ∨ c = 20

/-- The value of a coefficient, from the word read and the output `X`. -/
theorem emCoef_val {c : Nat} (hc : emOk c) (m : Mem) (a : Addr) (X : List Byte) {g k : Nat}
    (hb : ∀ b < 3, m (a + BitVec.ofNat 64 b) = X.getD (c / 2 * g + c * k / 8 + b) 0) :
    etaF (BitVec.ofNat 32 (2 ^ (c - 1))) (m.readW a 32 >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)) =
      emV X c (4 * g + k) := by
  have hc' : c ≤ 20 := by rcases hc with rfl | rfl <;> omega
  have hsh : c * k % 8 + c ≤ 24 := by rcases hc with rfl | rfl <;> omega
  have e1 : (m.readW a 32 >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)).toNat =
      leNat X / 2 ^ ((4 * g + k) * c) % 2 ^ c := by
    rw [BitVec.toNat_and, shr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ c - 1) (by
      have : 2 ^ c ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hc'; omega), Nat.and_two_pow_sub_one_eq_mod,
      word_bits m a X hsh hb]
    have e : 8 * (c / 2 * g + c * k / 8) + c * k % 8 = (4 * g + k) * c := by
      rcases hc with rfl | rfl <;> omega
    rw [e]
  have e2 : (BitVec.ofNat 32 (2 ^ (c - 1))).toNat = 2 ^ (c - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have : 2 ^ (c - 1) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega); omega)]
  have hp : 2 ^ c = 2 * 2 ^ (c - 1) := by
    rw [← Nat.pow_succ']; congr 1; rcases hc with rfl | rfl <;> rfl
  rw [etaF_eq (by rw [e2]; rcases hc with rfl | rfl <;> decide) (by
    rw [e1, e2]; have := Nat.mod_lt (leNat X / 2 ^ ((4 * g + k) * c)) (Nat.two_pow_pos c)
    have : 2 ^ (c - 1) < q := by rcases hc with rfl | rfl <;> decide
    omega), e1, e2]

/-! ## A group of 4 coefficients -/

theorem emOk_le {c : Nat} (hc : emOk c) : c / 2 * 63 + c * 3 / 8 ≤ 637 := by rcases hc with rfl | rfl <;> decide

/-- The facts a group needs. -/
structure GPre (c : Nat) (X : List Byte) (out aP : Addr) (g : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * g)
  rdi : s.gpr .rdi = aP + BitVec.ofNat 64 (16 * g)
  g_lt : g < 64
  bytes : ∀ j < 640, s.mem (out + BitVec.ofNat 64 j) = X.getD j 0
  rd : ∀ j ≤ 637, InRegions (s.rd ++ s.wr) (out + BitVec.ofNat 64 j) 4
  wr : pR aP ∈ s.wr
  apart : ∀ j < 640, ¬ (pR aP).Contains (out + BitVec.ofNat 64 j) 1

/-- The 4 coefficients of group `g`. -/
theorem emGroup_ok {c : Nat} (hc : emOk c) {X : List Byte} {out aP : Addr} {g : Nat} {s : State}
    (h : GPre c X out aP g s) :
    WP isa (.block ((List.range 4).flatMap (emCoef c))) s fun s' =>
      Keep [.rax, .rdx] s s' ∧ Frame [pR aP] s.mem s'.mem ∧
        (∀ k < 4, coeffAt s'.mem aP (4 * g + k) = emV X c (4 * g + k)) ∧
        (∀ i < 256, (i < 4 * g ∨ 4 * g + 4 ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i) := by
  have hg := h.g_lt
  have hle := emOk_le hc
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k s' => Keep [.rax, .rdx] s s' ∧
      Frame [pR aP] s.mem s'.mem ∧ (∀ j < k, coeffAt s'.mem aP (4 * g + j) = emV X c (4 * g + j)) ∧
      (∀ i < 256, (i < 4 * g ∨ 4 * g + k ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i))
    (fun k s' hk ⟨k', hf, hst, hsame⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩) fun s' h => h
  have hsi : s'.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * g) := by rw [k'.gpr (by decide), h.rsi]
  have hdi : s'.gpr .rdi = aP + BitVec.ofNat 64 (16 * g) := by rw [k'.gpr (by decide), h.rdi]
  have ha : s'.gpr .rdi + BitVec.ofNat 64 (4 * k) = coeffAddr aP (4 * g + k) := by
    rw [hdi, offAdd]; congr 2; omega
  have hr : s'.gpr .rsi + BitVec.ofNat 64 (c * k / 8) = out + BitVec.ofNat 64 (c / 2 * g + c * k / 8) := by
    rw [hsi, offAdd]
  have hkk : c * k / 8 ≤ c * 3 / 8 := Nat.div_le_div_right (Nat.mul_le_mul_left c (by omega))
  have hg' : c / 2 * g ≤ c / 2 * 63 := Nat.mul_le_mul_left _ (by omega)
  refine WP.mono (emCoef_run c k (by omega) s' (by rw [hr, k'.2.1, k'.2.2]; exact h.rd _ (by omega))
    (by rw [ha, k'.2.2]; exact ⟨_, h.wr, coeff_contains _ (by omega)⟩)) fun s'' ⟨hm, k''⟩ => ?_
  have hv := emCoef_val hc s'.mem (s'.gpr .rsi + BitVec.ofNat 64 (c * k / 8)) X (g := g) (k := k) (fun b hb => by
    rw [hr, offAdd, hf _ fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.apart _ (by omega)]
    exact h.bytes _ (by omega))
  rw [ha, hv] at hm
  refine ⟨k'.trans k'' |>.mono (by simp), ?_, fun j hj => ?_, fun i hi hi' => ?_⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by omega))
  · rw [hm, coeffAt_writeW _ _ (by omega) (by omega)]
    by_cases e : j = k
    · subst e; rw [ifT rfl]
    · rw [ifF (by omega)]; exact hst j (by omega)
  · rw [hm, coeffAt_writeW _ _ hi (by omega), ifF (by omega)]
    exact hsame i hi (by omega)

theorem sxHalf {c : Nat} (hc : emOk c) : BitVec.signExtend 64 (BitVec.ofNat 32 (c / 2)) = BitVec.ofNat 64 (c / 2) := by
  rcases hc with rfl | rfl <;> decide

/-- An iteration: a group, and the pointers and counter advanced. -/
theorem emBody_ok {c : Nat} (hc : emOk c) {X : List Byte} {out aP : Addr} {g : Nat} {s : State}
    (h : GPre c X out aP g s) :
    WP isa (.block (emBody c)) s fun s' =>
      Keep [.rax, .rdx, .rsi, .rdi, .rcx] s s' ∧ Frame [pR aP] s.mem s'.mem ∧
        (∀ k < 4, coeffAt s'.mem aP (4 * g + k) = emV X c (4 * g + k)) ∧
        (∀ i < 256, (i < 4 * g ∨ 4 * g + 4 ≤ i) → coeffAt s'.mem aP i = coeffAt s.mem aP i) ∧
        s'.gpr .rsi = out + BitVec.ofNat 64 (c / 2 * (g + 1)) ∧ s'.gpr .rdi = aP + BitVec.ofNat 64 (16 * (g + 1)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  unfold emBody
  rw [WP.block_append_iff]
  refine WP.mono (emGroup_ok hc h) fun s1 ⟨k1, hf1, hst1, hsame1⟩ => ?_
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx] (Q := fun s' => s'.mem = s1.mem ∧
      s'.gpr .rsi = s1.gpr .rsi + BitVec.ofNat 64 (c / 2) ∧ s'.gpr .rdi = s1.gpr .rdi + BitVec.ofNat 64 16 ∧
      s'.gpr .rcx = s1.gpr .rcx - 1 ∧ s'.zf = some (s1.gpr .rcx - 1 == 0)) (by xrun [sxHalf hc]; rfl)
    (by rfl)) fun s2 ⟨⟨hm2, hsi2, hdi2, hcx2, hz2⟩, k2⟩ => ?_
  have hcx1 : s1.gpr .rcx = s.gpr .rcx := k1.gpr (by decide)
  refine ⟨k1.trans k2 |>.mono (by simp), by rw [hm2]; exact hf1, fun k hk => by rw [hm2]; exact hst1 k hk,
    fun i hi hi' => by rw [hm2]; exact hsame1 i hi hi', ?_, ?_, by rw [hcx2, hcx1], by rw [hz2, hcx1]⟩
  · rw [hsi2, k1.gpr (by decide), h.rsi, offAdd, Nat.mul_succ]
  · rw [hdi2, k1.gpr (by decide), h.rdi, offAdd, Nat.mul_succ]

end VG.Proof.MlDsa.X86_64.Sample
