import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Mul
import VerifiedGarbage.Proof.Poly1305.Limbs26

/-!
# Poly1305 on x86-64 with AVX-512: the product

Untrusted: everything here is checked by Lean. `mul` multiplies the eight
quadwords of the accumulator `H` by the low doublewords of `Y`, quadword by
quadword, and carries: `Limbs26.mul`, with the limbs small enough that
nothing wraps (as `Avx2.mul` does on four).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi hreg_ge yreg_ge vec vec_trans vec_gpr)

/-- Limb `i` of quadword `k` of `H`, and of the low doublewords of `Y`. -/
def hv (s : State) (k i : Nat) : Nat := (qz s (hreg i) k).toNat
def yl (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat % 2 ^ 32

def mulB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 28 - 1
    | _ => 2 ^ 64 - 1,
   fun r => match r with
    | .xmm11 | .xmm12 | .xmm13 | .xmm14 | .xmm15 => 2 ^ 27 - 1
    | _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1⟩

def mulS : Sym := (Sym.init.run false mul).get (by decide +kernel)

theorem mulS_eq : Sym.init.run false mul = some mulS := (Option.some_get _).symm

theorem mulS_ok : ∀ i < 5, ∀ k < 8,
    (mulS.reg (xi (hreg i))).ok mulB k = true ∧ (mulS.reg (xi (hreg i))).bnd mulB k < 2 ^ 27 := by
  decide +kernel

theorem mulS_y : ∀ i < 5, mulS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The limbs `mul` computes, from the registers it starts with. -/
theorem mulS_nat (E : Env) (k : Nat) : ∀ i < 5, (mulS.reg (xi (hreg i))).nat E k =
    Limbs26.carry (Limbs26.pd (fun i => E.v (xi (hreg i)) k % 2 ^ 32)
      (fun i => E.v (xi (yreg i)) k % 2 ^ 32)) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

structure MulPre (s : State) : Prop where
  r8 : s.gpr .r8 = 0x3ffffff
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 28
  y : ∀ k < 8, ∀ i < 5, yl s k i < 2 ^ 27

theorem MulPre.env {s : State} (hp : MulPre s) : EnvOK s mulB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.h k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    cases r <;> simp only [mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.y k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 4 (by decide))
  · have := BitVec.isLt (s.gpr g)
    simp only [mulB]
    split
    · subst g; rw [hp.r8]; decide
    · omega

/-- What `mul` leaves: `H` times the low doublewords of `Y`, carried, and the
rest but the products and `tP` as they were. -/
structure MulPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, ∀ i < 5, hv s' k i = Limbs26.mul (hv s k) (yl s k) i
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27

theorem hv_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : hv s k j = hv s k 4 := by
  simp only [hv, hreg_ge h]

theorem yl_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : yl s k j = yl s k 4 := by
  simp only [yl, yreg_ge h]

theorem hv_mod {s : State} (hp : MulPre s) {k : Nat} (hk : k < 8) :
    (fun i => (envOf s).v (xi (hreg i)) k % 2 ^ 32) = hv s k := by
  funext i
  rw [envOf_v]
  by_cases hi : i < 5
  · exact Nat.mod_eq_of_lt (Nat.lt_trans (hp.h k hk i hi) (by decide))
  · rw [hreg_ge (by omega)]
    rw [hv_ge s k (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (hp.h k hk 4 (by decide)) (by decide))

theorem yl_eq (s : State) (k : Nat) : (fun i => (envOf s).v (xi (yreg i)) k % 2 ^ 32) = yl s k := by
  funext i; rw [envOf_v]; rfl

theorem mul_ok {s : State} (hp : MulPre s) : WP isa (.block mul) s (MulPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) mulS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, mulS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    simp only [hv] at e ⊢
    rw [e, mulS_nat _ _ i hi, Limbs26.mul, hv_mod hp hk, yl_eq]
    simp only [envOf, hp.r8]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    exact Nat.lt_of_le_of_lt b (mulS_ok i hi k hk).2

end VG.Proof.Poly1305.X86_64.Avx512
