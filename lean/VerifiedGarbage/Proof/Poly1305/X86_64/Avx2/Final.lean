import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Powers

/-!
# Poly1305 on x86-64 with AVX2: the accumulator in and out

Untrusted: everything here is checked by Lean. `loadH` splits the
accumulator into lane 0 of `H`; after the last group, `sumLanes` adds the
lanes into lane 0 and carries, `fullCarry` and `reduce` reduce it modulo
`p`, and `storeH` joins its limbs into words.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2
open VG.Spec.Poly1305 (P)

/-! ## `loadH` -/

def ldS : Sym := (Sym.init.run false loadH).get (by decide +kernel)
theorem ldS_eq : Sym.init.run false loadH = some ldS := (Option.some_get _).symm
theorem ldS_y : ∀ i < 5, ldS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env)
theorem ldS_0 : ∀ k < 4, (ldS.reg (xi (hreg 0))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_1 : ∀ k < 4, (ldS.reg (xi (hreg 1))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_2 : ∀ k < 4, (ldS.reg (xi (hreg 2))).natw E k =
    ((if k = 0 then E.g .r11 else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
      (if k = 0 then E.g .r10 else 0) / 2 ^ 52) := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_3 : ∀ k < 4, (ldS.reg (xi (hreg 3))).natw E k =
    (if k = 0 then E.g .r11 else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem ldS_4 : ∀ k < 4, (ldS.reg (xi (hreg 4))).natw E k =
    ((if k = 0 then E.g .r11 else 0) / 2 ^ 40 ||| (if k = 0 then E.g .rax else 0) * 2 ^ 24 % 2 ^ 64) := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
end

/-- The accumulator's words, in `r10`, `r11` and `rax`, as a number. -/
def hN (s : State) : Nat :=
  (s.gpr .r10).toNat + 2 ^ 64 * (s.gpr .r11).toNat + 2 ^ 128 * (s.gpr .rax).toNat

/-- What `loadH` leaves: the accumulator in lane 0 of `H`, zeros in the
other lanes, and `Y` as it was. -/
structure LoadHPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k
  h : ∀ k < 4, Limbs26.val (hv s' k) = if k = 0 then hN s else 0
  hb : ∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 26

theorem loadH_ok {s : State} (hax : (s.gpr .rax).toNat < 4) : WP isa (.block loadH) s (LoadHPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) ldS_eq) fun s' h => ?_
  have e : ∀ k < 4, hv s' k 0 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
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
      rw [Limbs26.val, a0, a1, a2, a3, a4, hN]
      omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4 ⊢
      rw [Limbs26.val, a0, a1, a2, a3, a4]; rfl
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4
      rw [e4] at a4
      rw [Limbs26.split_or l] at a2
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; omega
      · rw [a1]; omega
      · rw [a2]; omega
      · rw [a3]; omega
      · rw [a4]; omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
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
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1⟩

def smS : Sym := (Sym.init.run false sumLanes).get (by decide +kernel)
theorem smS_eq : Sym.init.run false sumLanes = some smS := (Option.some_get _).symm

theorem smS_ok : ∀ i < 5, (smS.reg (xi (hreg i))).ok sumB 0 = true ∧
    (smS.reg (xi (hreg i))).bnd sumB 0 < (if i = 1 then 2 ^ 27 else 2 ^ 26) := by
  decide +kernel

/-- The sum of the lanes of `H`, limb by limb, as `sumLanes` adds them. -/
def lsum (h : Nat → Nat → Nat) (i : Nat) : Nat := h 0 i + h 2 i + (h 1 i + h 3 i)

theorem smS_nat (E : Env) : ∀ i < 5, (smS.reg (xi (hreg i))).nat E 0 =
    Limbs26.carry (lsum fun k j => E.v (xi (hreg j)) k) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem sumB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) :
    EnvOK s sumB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_⟩
  · have := BitVec.isLt (qw s r k)
    cases r <;> simp only [sumB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qw s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [sumB]; omega
  · have := BitVec.isLt (s.gpr g)
    simp only [sumB]
    split
    · subst g; rw [hr8]; decide
    · omega

theorem lsum_val (h : Nat → Nat → Nat) :
    Limbs26.val (lsum h) = Limbs26.val (h 0) + Limbs26.val (h 1) + Limbs26.val (h 2) + Limbs26.val (h 3) := by
  simp only [Limbs26.val, lsum]; omega

/-- What `sumLanes` leaves in lane 0 of `H`: the sum of the lanes, carried. -/
structure SumPost (s s' : State) : Prop where
  vec : vec s s' = s'
  h : Limbs26.val (hv s' 0) ≡
    Limbs26.val (hv s 0) + Limbs26.val (hv s 1) + Limbs26.val (hv s 2) + Limbs26.val (hv s 3) [MOD P]
  hb : ∀ i < 5, hv s' 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26

theorem sumLanes_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) :
    WP isa (.block sumLanes) s (SumPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) smS_eq) fun s' h => ?_
  have hE := sumB_env hr8 hb
  have e : ∀ i < 5, hv s' 0 i = Limbs26.carry (lsum (hv s)) 0x3ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (smS_ok i hi).1
    simp only [hv] at e ⊢
    rw [e, smS_nat _ i hi]
    simp only [envOf, hr8, xr_xi]
    rfl
  refine ⟨h.eq, ?_, fun i hi => ?_⟩
  · rw [val_congr e, ← lsum_val]
    have := Limbs26.carry_val (lsum (hv s))
    rw [← this, Nat.ModEq, Nat.add_mul_mod_self_left]
  · obtain ⟨-, b⟩ := h.nat hE (by decide) (smS_ok i hi).1
    exact Nat.lt_of_le_of_lt b (smS_ok i hi).2

/-! ## `fullCarry` and `reduce` -/

def finB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun g => match g with
    | .r8 => 2 ^ 26 - 1
    | .rax => 5
    | .r10 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1⟩

def fnS : Sym := (Sym.init.run false (fullCarry ++ reduce)).get (by decide +kernel)
theorem fnS_eq : Sym.init.run false (fullCarry ++ reduce) = some fnS := (Option.some_get _).symm

theorem fnS_ok : ∀ i < 5, (fnS.reg (xi (hreg i))).ok finB 0 = true := by
  decide +kernel

theorem fnS_nat (E : Env) : ∀ i < 5, (fnS.reg (xi (hreg i))).nat E 0 =
    Limbs26.fin (fun j => E.v (xi (hreg j)) 0) (E.g .r8) (E.g .rax) (E.g .r10) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem finB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 5)
    (hr10 : s.gpr .r10 = 0x7ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27) : EnvOK s finB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_⟩
  · have := BitVec.isLt (qw s r k)
    cases r <;> simp only [finB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qw s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [finB]; omega
  · have := BitVec.isLt (s.gpr g)
    cases g <;> simp only [finB] <;> first | omega | (rw [hr8]; decide) | (rw [hax]; decide) |
      (rw [hr10]; decide)

/-- What `fullCarry` and `reduce` leave in lane 0 of `H`: `h mod p`. -/
theorem finish_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 5)
    (hr10 : s.gpr .r10 = 0x7ffffff) (hb : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27)
    (hb0 : ∀ i < 5, hv s 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26) :
    WP isa (.block (fullCarry ++ reduce)) s fun s' => vec s s' = s' ∧
      Limbs26.val (hv s' 0) = Limbs26.val (hv s 0) % P ∧ ∀ i < 5, hv s' 0 i < 2 ^ 26 := by
  refine WP.mono (run_ok (by intro h; cases h) fnS_eq) fun s' h => ?_
  have hE := finB_env hr8 hax hr10 hb
  have e : ∀ i < 5, hv s' 0 i = Limbs26.fin (hv s 0) 0x3ffffff 5 0x7ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (fnS_ok i hi)
    simp only [hv] at e ⊢
    rw [e, fnS_nat _ i hi]
    simp only [envOf, hr8, hax, hr10, xr_xi]
    rfl
  obtain ⟨v, b⟩ := Limbs26.fin_val (hb0 0 (by decide)) (hb0 1 (by decide)) (hb0 2 (by decide))
    (hb0 3 (by decide)) (hb0 4 (by decide))
  exact ⟨h.eq, by rw [val_congr e, v], fun i hi => by rw [e i hi]; exact b i hi⟩

end VG.Proof.Poly1305.X86_64.Avx2
