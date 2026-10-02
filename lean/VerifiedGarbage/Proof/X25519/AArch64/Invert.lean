import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.X25519.Invert

/-! Kernel-checked ref10 inversion chain, reusing the ladder's dead slots. -/
namespace VG.Proof.X25519.AArch64
open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519

abbrev invRegs : List Reg := fieldRegs ++ [.x23]
def IQ : List Nat := [1, 2, 5, 6, 7, 14]
def cbnds (n : Nat) : Option Nat := if n ∈ IQ then some 18 else none
structure CI (b : Addr) (s₀ s : State) (v : Nat → Fe) : Prop where
  sc : Sc b s
  sl : Sl s.mem b v cbnds
  kp : Kp invRegs s₀ s
  fr : Frame [slotArea b] s₀.mem s.mem

theorem Inv.of_sl {b : Addr} {s : State} {v : Nat → Fe} {bnds : Nat → Option Nat}
    (hs : Sc b s) (h : Sl s.mem b v bnds) : Inv b s s v bnds := ⟨hs, h, Kp.refl _ _, Frame.refl _ _⟩
def cmul (o a c : Nat) (v : Nat → Fe) := Function.update v o (v a * v c)
def ccopy (o a : Nat) (v : Nat → Fe) := Function.update v o (v a)
def csqn (o a n : Nat) (v : Nat → Fe) := Function.update v o (VG.Proof.X25519.sqn (v a) n)
def CS (b : Addr) (c : Prog isa) (f : (Nat → Fe) → Nat → Fe) : Prop :=
  ∀ s₀ s v, CI b s₀ s v → WP isa c s fun t => CI b s₀ t (f v)

theorem cbnds_update {o : Nat} (ho : o ∈ IQ) : Function.update cbnds o (some 18) = cbnds := by
  funext n
  by_cases h : n = o
  · subst n; simp [cbnds, ho]
  · simp [Function.update_of_ne h]
theorem iq_lt {n : Nat} (h : n ∈ IQ) : n < 15 := by simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem cmul_ok (b : Addr) (o a c : Nat) (ho : o ∈ IQ) (ha : a ∈ IQ) (hc : c ∈ IQ) :
    CS b (.block (mul (slot o) (slot a) (slot c))) (cmul o a c) := by
  intro s₀ s v h
  refine WP.mono (mul_inv (Inv.of_sl h.sc h.sl) (iq_lt ho) (iq_lt ha) (iq_lt hc)
    (ka := 18) (kc := 18) (by simp [cbnds, ha]) (by simp [cbnds, hc]) (by decide) (by decide)) fun t ht => ?_
  exact ⟨ht.sc, by rw [cbnds_update ho] at ht; exact ht.sl,
    (h.kp.trans ht.kp).sub (List.append_subset.mpr ⟨List.Subset.refl _, List.subset_append_left _ _⟩), h.fr.trans ht.fr⟩
theorem ccopy_ok (b : Addr) (o a : Nat) (ho : o ∈ IQ) (ha : a ∈ IQ) :
    CS b (.block (copy (slot o) (slot a))) (ccopy o a) := by
  intro s₀ s v h
  refine WP.mono (copy_inv (Inv.of_sl h.sc h.sl) (iq_lt ho) (iq_lt ha)
    (ka := 18) (by simp [cbnds, ha])) fun t ht => ?_
  exact ⟨ht.sc, by rw [cbnds_update ho] at ht; exact ht.sl,
    (h.kp.trans ht.kp).sub (List.append_subset.mpr ⟨List.Subset.refl _, List.subset_append_left _ _⟩), h.fr.trans ht.fr⟩
theorem CS.seq {b : Addr} {p q : Prog isa} {f g} (hp : CS b p f) (hq : CS b q g) :
    CS b (.seq p q) (fun v => g (f v)) := by
  intro s₀ s v h
  exact WP.seq (WP.mono (hp s₀ s v h) fun t ht => hq s₀ t (f v) ht)
theorem CS.append {b : Addr} {p q : List Instr} {f g} (hp : CS b (.block p) f) (hq : CS b (.block q) g) :
    CS b (.block (p ++ q)) (fun v => g (f v)) := by
  intro s₀ s v h
  exact WP.block_append (WP.mono (hp s₀ s v h) fun t ht => hq s₀ t (f v) ht)

theorem counter_ok {b : Addr} {s₀ s : State} {v : Nat → Fe} (h : CI b s₀ s v) (n : Nat) (hn : n < 65536) :
    WP isa (.block [.movz .x .x23 n 0]) s fun t => CI b s₀ t v ∧ t.gpr .x23 = BitVec.ofNat 64 n := by
  refine WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ?_⟩
  exact ⟨⟨sc_wx _ _ h.sc (by decide), h.sl,
    (h.kp.trans (kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by simp [invRegs]⟩), h.fr⟩,
    by rw [gpr_wx_self]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩
theorem dec_ok {b : Addr} {s₀ s : State} {v : Nat → Fe} {n : Nat} (h : CI b s₀ s v)
    (he : s.gpr .x23 = BitVec.ofNat 64 (n + 1)) (_hn : n < 65536) :
    WP isa (.block [.subImm .x .x23 .x23 1]) s fun t => CI b s₀ t v ∧ t.gpr .x23 = BitVec.ofNat 64 n := by
  refine WP.block_cons_iff.mpr ⟨_, exec_subImm_x (d := .x23) (n := .x23) (imm := 1) (by decide), WP.block_nil ?_⟩
  exact ⟨⟨sc_wx _ _ h.sc (by decide), h.sl,
    (h.kp.trans (kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by simp [invRegs]⟩), h.fr⟩,
    by rw [gpr_wx_self, read_x, he, BitVec.ofNat_add, BitVec.add_sub_cancel]⟩

theorem csqn_ok (b : Addr) (o a n : Nat) (ho : o ∈ IQ) (ha : a ∈ IQ) (hn : 1 ≤ n) (hn' : n < 65536) :
    CS b (Impl.X25519.AArch64.sqn (slot o) (slot a) n) (csqn o a n) := by
  intro s₀ s v h
  refine WP.seq (WP.block_append (WP.mono (ccopy_ok b o a ho ha s₀ s v h) fun t ht =>
    WP.mono (counter_ok ht n hn') fun u ⟨hu, eu⟩ => ?_))
  refine WP.loop (M := isa) (fun k t => 1 ≤ k ∧ k ≤ n ∧
    CI b s₀ t (Function.update v o (VG.Proof.X25519.sqn (v a) (n-k))) ∧
    t.gpr .x23 = BitVec.ofNat 64 k) ?_ n u ⟨hn, Nat.le_refl _, by simpa [ccopy, VG.Proof.X25519.sqn] using hu, eu⟩
  intro k t ⟨hk, hkn, ht, et⟩
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
  refine WP.block_append (WP.mono (mul_inv (Inv.of_sl ht.sc ht.sl) (iq_lt ho) (iq_lt ho) (iq_lt ho)
    (ka := 18) (kc := 18) (by simp [cbnds, ho]) (by simp [cbnds, ho]) (by decide) (by decide)) fun u hu => ?_)
  have eu : u.gpr .x23 = BitVec.ofNat 64 (k+1) := by rw [hu.kp.gpr _ (by decide), et]
  have hi : CI b s₀ u (Function.update v o (VG.Proof.X25519.sqn (v a) (n-k))) := by
    refine ⟨hu.sc, ?_, (ht.kp.trans hu.kp).sub (List.append_subset.mpr
      ⟨List.Subset.refl _, List.subset_append_left _ _⟩), ht.fr.trans hu.fr⟩
    rw [cbnds_update ho] at hu
    have he : Function.update (Function.update v o (VG.Proof.X25519.sqn (v a) (n-(k+1)))) o
        ((Function.update v o (VG.Proof.X25519.sqn (v a) (n-(k+1)))) o *
         (Function.update v o (VG.Proof.X25519.sqn (v a) (n-(k+1)))) o) =
        Function.update v o (VG.Proof.X25519.sqn (v a) (n-k)) := by
      rw [Function.update_self, Function.update_idem, show n-k = n-(k+1)+1 by omega]
      rfl
    rw [he] at hu
    exact hu.sl
  refine WP.mono (dec_ok hi eu (by omega)) fun t ⟨ht, et⟩ => ?_
  have hev : isa.eval (.nonzero .x .x23) t = some (BitVec.ofNat 64 k != 0) := by simp [eval, read_x, et]
  by_cases hk0 : k = 0
  · subst k
    exact .inl ⟨by rw [hev]; rfl, by simpa [csqn] using ht⟩
  · refine .inr ⟨?_, k, by omega, by omega, by omega, ht, et⟩
    rw [hev]
    apply congrArg some
    apply bne_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2^64)] at this
    exact hk0 this

def chainEnv (v : Nat → Fe) : Nat → Fe := cmul 14 14 5 (csqn 14 14 5 (cmul 14 6 14 (csqn 6 6 50 (cmul 6 7 6 (csqn 7 6 100 (cmul 6 6 14 (csqn 6 14 50 (cmul 14 6 14 (csqn 6 6 10 (cmul 6 7 6 (csqn 7 6 20 (cmul 6 6 14 (csqn 6 14 10 (cmul 14 6 14 (csqn 6 14 5 (cmul 14 14 6 (cmul 6 5 5 (cmul 5 5 14 (cmul 14 2 14 (csqn 14 5 2 (cmul 5 2 2 (v))))))))))))))))))))))

theorem chain_spec (b : Addr) : CS b invChain chainEnv := by
  have h : CS b _ _ := (CS.seq (cmul_ok b 5 2 2 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 14 5 2 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (CS.append (CS.append (CS.append (cmul_ok b 14 2 14 (by decide) (by decide) (by decide)) (cmul_ok b 5 5 14 (by decide) (by decide) (by decide))) (cmul_ok b 6 5 5 (by decide) (by decide) (by decide))) (cmul_ok b 14 14 6 (by decide) (by decide) (by decide)))
    (CS.seq (csqn_ok b 6 14 5 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 14 6 14 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 6 14 10 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 6 6 14 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 7 6 20 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 6 7 6 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 6 6 10 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 14 6 14 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 6 14 50 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 6 6 14 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 7 6 100 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 6 7 6 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 6 6 50 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (cmul_ok b 14 6 14 (by decide) (by decide) (by decide))
    (CS.seq (csqn_ok b 14 14 5 (by decide) (by decide) (by decide) (by decide))
    (cmul_ok b 14 14 5 (by decide) (by decide) (by decide))))))))))))))))))))
  exact h

theorem chain_eval (v : Nat → Fe) : chainEnv v 14 = VG.Proof.X25519.invert (v 2) := by
  simp (config := {decide := true}) only [chainEnv, cmul, csqn, Function.update_apply, ite_true, ite_false]
  rfl

theorem chain_keep (v : Nat → Fe) : chainEnv v 1 = v 1 := by
  simp (config := {decide := true}) only [chainEnv, cmul, csqn, Function.update_apply, ite_true, ite_false]

def fbnds (n : Nat) : Option Nat := if n = 1 ∨ n = 14 then some 18 else none

theorem invert_ok {b : Addr} {s : State} {v : Nat → Fe} {bnds : Nat → Option Nat} {z : Fe}
    (hs : Sc b s) (hsl : Sl s.mem b v bnds) (hz : v 2 = z)
    (hb2 : bnds 2 = some 18) (hb1 : bnds 1 = some 18) :
    WP isa Impl.X25519.AArch64.invert s fun t => Sc b t ∧
      Sl t.mem b (Function.update v 14 (pow z (P-2))) fbnds ∧
      Kp invRegs s t ∧ Frame [slotArea b] s.mem t.mem := by
  unfold Impl.X25519.AArch64.invert
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy_inv (Inv.of_sl hs hsl)
    (o := 5) (a := 2) (by decide) (by decide) hb2) fun t₁ h₁ => ?_))
  refine WP.block_append (WP.mono (copy_inv h₁ (o := 6) (a := 2) (by decide) (by decide)
    (ka := 18) (by simp [hb2])) fun t₂ h₂ => ?_)
  refine WP.block_append (WP.mono (copy_inv h₂ (o := 7) (a := 2) (by decide) (by decide)
    (ka := 18) (by simp [hb2])) fun t₃ h₃ => ?_)
  refine WP.mono (copy_inv h₃ (o := 14) (a := 2) (by decide) (by decide)
    (ka := 18) (by simp [hb2])) fun t₄ h₄ => ?_
  have hi : CI b s t₄ (ccopy 14 2 (ccopy 7 2 (ccopy 6 2 (ccopy 5 2 v)))) := ⟨h₄.sc, h₄.sl.weaken (fun n hn k hk => by
    simp only [cbnds] at hk
    split at hk
    · cases hk
      rename_i hq
      simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [hb1, hb2], rfl⟩
    · cases hk), h₄.kp.sub (List.subset_append_left _ _), h₄.fr⟩
  refine WP.mono (chain_spec b s t₄ _ hi) fun t ht => ⟨ht.sc, ?_, ht.kp, ht.fr⟩
  intro n hn k hk
  simp only [fbnds] at hk
  split at hk
  · cases hk
    rename_i hq
    rcases hq with rfl | rfl
    · have h := ht.sl 1 (by decide) 18 (by decide)
      simpa [chain_keep, ccopy, Function.update_of_ne] using h
    · have h := ht.sl 14 (by decide) 18 (by decide)
      simpa [chain_eval, ccopy, VG.Proof.X25519.invert_eq, hz] using h
  · cases hk

end VG.Proof.X25519.AArch64
