import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Macs
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Pairs
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A half's products are its coefficients

Untrusted: everything here is checked by Lean. With the first operand's half
in vectors at `aHalf h` and the second's (and its shifted copy) at `bOff h`,
lane `e` of the products aimed at a register is coefficient `q` of the product
of the halves, `cv`.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off)

/-- The memory words of a half: element `c % 2`'s half-limb `2i + c / 2` in word `c` of vector `i`,
and the shifted copy of the second operand. -/
structure HalfMem (m : Mem) (base : Addr) (h : Nat) (X Y : Nat → Nat → Nat) : Prop where
  a : ∀ i < 4, ∀ c < 4, nw m base (aHalf h + 16 * i + 4 * c) = X (c % 2) (2 * i + c / 2)
  b : ∀ j < 4, ∀ c < 4, nw m base (bHalf h + 16 * j + 4 * c) = Y (c % 2) (2 * j + c / 2)
  sh : ∀ j < 5, ∀ c < 4, nw m base (NBP + 80 * h + 16 * j + 4 * c) =
    if c < 2 then (if j = 0 then 0 else Y (c % 2) (2 * j - 1)) else (if j = 4 then 0 else Y (c % 2) (2 * j))

theorem prodVal_eq {m : Mem} {base : Addr} {h : Nat} {X Y : Nat → Nat → Nat} (hm : HalfMem m base h X Y)
    {p : Prod} (hpm : p ∈ prods) {e : Nat} (he : e < 2) :
    prodVal (fun i => m.read (off base (aHalf h + 16 * i)) 16) (fun bv => m.read (off base (bOff h bv)) 16) p e =
      X e (ia p) * Y e (ib p) := by
  obtain ⟨-, -, -, hz⟩ := prods_pos p hpm
  obtain ⟨pi, pb⟩ := prods_facts p hpm
  have hc : hp p.hi + e < 4 := by unfold hp; split <;> omega
  simp only [prodVal]
  rw [vword_ld _ _ _ hc, vword_ld _ _ _ hc, hm.a _ pi _ hc]
  have e1 : (hp p.hi + e) % 2 = e := by unfold hp; split <;> omega
  have e2 : (hp p.hi + e) / 2 = if p.hi then 1 else 0 := by unfold hp; split <;> omega
  rw [e1, e2]
  congr 1
  unfold bOff ib
  split
  · rename_i hb; rw [hm.b _ hb _ hc, e1, e2]
  · rename_i hb
    rw [show NBP + 80 * h + 16 * (p.bv - 4) + 4 * (hp p.hi + e) = NBP + 80 * h + 16 * (p.bv - 4) + 4 * (hp p.hi + e)
      from rfl, hm.sh _ (by omega) _ hc, e1]
    cases hhi : p.hi
    · have := (hz (by omega)).1 hhi
      simp only [hp, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero, show e < 2 from he, ite_true,
        show p.bv - 4 ≠ 0 by omega]
    · have := (hz (by omega)).2 hhi
      simp only [hp, ite_true, show ¬ (2 + e < 2) by omega, ite_false, show p.bv - 4 ≠ 4 by omega,
        Nat.add_sub_cancel]

theorem cast_sum {α : Type} (l : List α) (f : α → Nat) :
    (((l.map f).sum : Nat) : Int) = (l.map fun x => (f x : Int)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.sum_cons, ih]

theorem prodSum_cv {m : Mem} {base : Addr} {h : Nat} {X Y : Nat → Nat → Nat} (hm : HalfMem m base h X Y)
    {tgt : Nat → Nat} {r q : Nat} (hq : q < 15) (ht : ∀ p ∈ prods, tgt p.pos = r ↔ p.pos = q) {e : Nat} (he : e < 2) :
    prodSum (fun i => m.read (off base (aHalf h + 16 * i)) 16) (fun bv => m.read (off base (bOff h bv)) 16)
      tgt prods r e = cv (X e) (Y e) q := by
  simp only [prodSum]
  rw [List.filter_congr (q := fun p => p.pos == q) fun p hp => by simp [ht p hp],
    List.map_congr_left (g := fun p => ((X e (ia p) * Y e (ib p) : Nat) : Int)) fun p hp => by
      rw [prodVal_eq hm (List.mem_filter.mp hp).1 he],
    cv_pairs _ _ q hq]
  have hperm := (perm_q q hq).map (fun ij : Nat × Nat => ((X e ij.1 * Y e ij.2 : Nat) : Int))
  rw [List.map_map] at hperm
  rw [show (fun p => ((X e (ia p) * Y e (ib p) : Nat) : Int)) =
    (fun ij : Nat × Nat => ((X e ij.1 * Y e ij.2 : Nat) : Int)) ∘ (fun p => (ia p, ib p)) from rfl, hperm.sum_eq]
  rw [cast_sum]

end VG.Proof.Curve448.AArch64.Neon
