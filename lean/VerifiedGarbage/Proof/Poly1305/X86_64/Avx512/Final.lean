import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final

/-!
# Poly1305 on x86-64 with AVX-512: the accumulator in, and the lanes summed

`loadH` splits the accumulator into quadword 0 of `H`; after the last group,
`sumLanes` adds the quadwords into quadword 0 and carries. The rest
(`fullCarry`, `reduce` and `storeH`) is `vg_poly1305_blocks_avx2`'s code, on
quadword 0 (see `Avx2/Final.lean`), whose quadwords are those of `Avx2.qw`
(`qz_qw`).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr hN)
open VG.Spec.Poly1305 (P)

/-! ## `loadH` -/

def ldS : Sym := (Sym.init.run false loadH).get (by decide +kernel)
theorem ldS_eq : Sym.init.run false loadH = some ldS := (Option.some_get _).symm
theorem ldS_y : ∀ i < 5, ldS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env)
theorem ldS_0 : ∀ k < 8, (ldS.reg (xi (hreg 0))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_1 : ∀ k < 8, (ldS.reg (xi (hreg 1))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_2 : ∀ k < 8, (ldS.reg (xi (hreg 2))).natw E k =
    ((if k = 0 then E.g .r11 else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
      (if k = 0 then E.g .r10 else 0) / 2 ^ 52) := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_3 : ∀ k < 8, (ldS.reg (xi (hreg 3))).natw E k =
    (if k = 0 then E.g .r11 else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_4 : ∀ k < 8, (ldS.reg (xi (hreg 4))).natw E k =
    ((if k = 0 then E.g .r11 else 0) / 2 ^ 40 ||| (if k = 0 then E.g .rax else 0) * 2 ^ 24 % 2 ^ 64) := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end

/-- What `loadH` leaves: the accumulator in quadword 0 of `H`, zeros in the
others, and `Y` as it was. -/
structure LoadHPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, hval s' k = if k = 0 then hN s else 0
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 26

theorem loadH_ok {s : State} (hax : (s.gpr .rax).toNat < 4) : WP isa (.block loadH) s (LoadHPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) ldS_eq) fun s' h => ?_
  have e : ∀ k < 8, hv s' k 0 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = ((if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (if k = 0 then (s.gpr .r10).toNat else 0) / 2 ^ 52) ∧
      hv s' k 3 = (if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = ((if k = 0 then (s.gpr .r11).toNat else 0) / 2 ^ 40 |||
        (if k = 0 then (s.gpr .rax).toNat else 0) * 2 ^ 24 % 2 ^ 64) := fun k hk =>
    ⟨by rw [hv, h.natw _ hk, ldS_0 _ k hk]; rfl, by rw [hv, h.natw _ hk, ldS_1 _ k hk]; rfl,
      by rw [hv, h.natw _ hk, ldS_2 _ k hk]; rfl, by rw [hv, h.natw _ hk, ldS_3 _ k hk]; rfl,
      by rw [hv, h.natw _ hk, ldS_4 _ k hk]; rfl⟩
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  have e4 : ((s.gpr .r11).toNat / 2 ^ 40 ||| (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64) =
      (s.gpr .r11).toNat / 2 ^ 40 + 2 ^ 24 * (s.gpr .rax).toNat := by
    rw [show (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64 = 2 ^ 24 * (s.gpr .rax).toNat by omega, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, ldS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4 ⊢
      rw [e4] at a4
      have := Limbs26.split_val l (s.gpr .r11).toNat
      rw [hval, Limbs26.val, a0, a1, a2, a3, a4, hN]
      omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4 ⊢
      rw [hval, Limbs26.val, a0, a1, a2, a3, a4]; rfl
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4
      rw [e4] at a4
      rw [Limbs26.split_or l] at a2
      rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; omega
      · rw [a1]; omega
      · rw [a2]; omega
      · rw [a3]; omega
      · rw [a4]; omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4
      rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; decide
      · rw [a1]; decide
      · rw [a2]; decide
      · rw [a3]; decide
      · rw [a4]; decide

/-! ## `sumLanes` -/

def sumB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1⟩

def smS : Sym := (Sym.init.run false sumLanes).get (by decide +kernel)
theorem smS_eq : Sym.init.run false sumLanes = some smS := (Option.some_get _).symm

theorem smS_ok : ∀ i < 5, ∀ k < 8, (smS.reg (xi (hreg i))).ok sumB k = true ∧
    (smS.reg (xi (hreg i))).bnd sumB k < (if i = 1 then 2 ^ 27 else 2 ^ 26) := by
  decide +kernel

/-- The sum of the quadwords of `H`, limb by limb, as `sumLanes` adds them. -/
def lsum (h : Nat → Nat → Nat) (i : Nat) : Nat :=
  h 0 i + h 4 i + (h 2 i + h 6 i) + (h 1 i + h 5 i + (h 3 i + h 7 i))

theorem smS_nat (E : Env) : ∀ i < 5, (smS.reg (xi (hreg i))).nat E 0 =
    Limbs26.carry (lsum fun k j => E.v (xi (hreg j)) k) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem sumB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27) :
    EnvOK s sumB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [sumB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [sumB]; omega
  · have := BitVec.isLt (s.gpr g)
    simp only [sumB]
    split
    · subst g; rw [hr8]; decide
    · omega

theorem lsum_val (h : Nat → Nat → Nat) :
    Limbs26.val (lsum h) = Limbs26.val (h 0) + Limbs26.val (h 2) + Limbs26.val (h 4) + Limbs26.val (h 6) +
      Limbs26.val (h 1) + Limbs26.val (h 3) + Limbs26.val (h 5) + Limbs26.val (h 7) := by
  simp only [Limbs26.val, lsum]; omega

/-- What `sumLanes` leaves in quadword 0 of `H`: the sum of the quadwords,
carried. -/
structure SumPost (s s' : State) : Prop where
  vec : vec s s' = s'
  h : hval s' 0 ≡ bsum s [MOD P]
  hb : ∀ i < 5, hv s' 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26
  hball : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27

theorem sumLanes_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27) :
    WP isa (.block sumLanes) s (SumPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) smS_eq) fun s' h => ?_
  have hE := sumB_env hr8 hb
  have e : ∀ i < 5, hv s' 0 i = Limbs26.carry (lsum (hv s)) 0x3ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (smS_ok i hi 0 (by decide)).1
    simp only [hv] at e ⊢
    rw [e, smS_nat _ i hi]
    simp only [envOf, hr8, xr_xi]
    rfl
  refine ⟨h.eq, ?_, fun i hi => ?_, fun k hk i hi => ?_⟩
  · rw [hval, Avx2.val_congr e, bsum]
    have := Limbs26.carry_val (lsum (hv s))
    rw [lsum_val] at this
    simp only [hval]
    rw [← this, Nat.ModEq, Nat.add_mul_mod_self_left]
  · obtain ⟨-, b⟩ := h.nat hE (by decide) (smS_ok i hi 0 (by decide)).1
    exact Nat.lt_of_le_of_lt b (smS_ok i hi 0 (by decide)).2
  · obtain ⟨-, b⟩ := h.nat hE hk (smS_ok i hi k hk).1
    have := (smS_ok i hi k hk).2
    simp only [hv]
    split at this <;> omega

/-! ## Quadword 0 as `vg_poly1305_blocks_avx2` sees it -/

theorem hv_avx2 (s : State) {k : Nat} (hk : k < 4) (i : Nat) : Avx2.hv s k i = hv s k i := by
  simp only [Avx2.hv, hv, qz_qw _ _ hk]

end VG.Proof.Poly1305.X86_64.Avx512
