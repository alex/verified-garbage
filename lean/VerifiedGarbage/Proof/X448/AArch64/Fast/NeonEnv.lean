import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Mul2

/-!
# X448 on AArch64: two products in AdvSIMD, on slots

Untrusted: everything here is checked by Lean. `mul2` updates two slots as
two field operations would, and writes nothing but the two slots and the
vector working space, which `FKeep` allows.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs ofs ofs_off)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.Curve448.AArch64.Neon (NA mul2)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem mul2_word {m m' : Mem} {base : Addr} {o₁ o₂ : Nat}
    (hF : ∀ x, (ofs base x < o₁ ∨ o₁ + 64 ≤ ofs base x) → (ofs base x < o₂ ∨ o₂ + 64 ≤ ofs base x) →
      (ofs base x < NA ∨ NA + 640 ≤ ofs base x) → m' x = m x) {d : Nat}
    (h1 : d + 8 ≤ o₁ ∨ o₁ + 64 ≤ d) (h2 : d + 8 ≤ o₂ ∨ o₂ + 64 ≤ d) (h3 : d + 8 ≤ NA) :
    word m' base d = word m base d := by
  have hNA : NA = 4096 := rfl
  exact (Mem.readW_congr fun i hi => (hF _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega) (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem slot_neon (i : Index) : slot i.val % 16 = 0 ∧ slot i.val + 64 ≤ NA := by
  have := i.isLt; have hNA : NA = 4096 := rfl; simp only [slot]; omega

theorem mul2E {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o₁ a₁ b₁ o₂ a₂ b₂ : Index)
    (h12 : o₁ ≠ o₂) :
    WP isa (.block (mul2 (slot o₁.val) (slot a₁.val) (slot b₁.val) (slot o₂.val) (slot a₂.val) (slot b₂.val))) s
      fun t => FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o₁.val) ∧
        Bnd Mb t.mem base (slot o₂.val) ∧ Same base [o₁, o₂] s.mem t.mem ∧
        EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a₁ * EV s.mem base b₁))
          o₂ (EV s.mem base a₂ * EV s.mem base b₂) := by
  have hNA : NA = 4096 := rfl
  have hACC : ACC = 3584 := rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.mul2_ok hs (slot_neon a₁) (slot_neon b₁) (slot_neon a₂)
    (slot_neon b₂) (slot_neon o₁) (slot_neon o₂) (slot_sep64 h12) (hb a₁) (hb b₁) (hb a₂) (hb b₂))
    fun t ⟨m1, m2, v1, v2, fr, g, r, w⟩ => ?_
  have same : Same base [o₁, o₂] s.mem t.mem := fun i hi j hj => by
    have n1 : i ≠ o₁ := fun e => hi (by simp [e])
    have n2 : i ≠ o₂ := fun e => hi (by simp [e])
    have := slot_sep64 n1; have := slot_sep64 n2; have := (slot_neon i).2
    exact congrArg BitVec.toNat (mul2_word fr (by omega) (by omega) (by omega))
  refine ⟨⟨⟨fun r _ => congrFun g r, r, w⟩, fun p hp hq => fr p ?_ ?_ ?_⟩, fun i => ?_, m1, m2, same, ?_⟩
  · have := o₁.isLt; simp only [slot]; omega
  · have := o₂.isLt; simp only [slot]; omega
  · omega
  · by_cases e1 : i = o₁
    · subst e1; exact fun j hj => Nat.lt_of_lt_of_le (m1 j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib
    by_cases e2 : i = o₂
    · subst e2; exact fun j hj => Nat.lt_of_lt_of_le (m2 j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib
    exact same.bnd (by simp [e1, e2]) (hb i)
  · funext i
    simp only [Function.update_apply]
    by_cases e2 : i = o₂
    · rw [ite_eq_left e2]; subst e2; exact v2
    rw [ite_eq_right e2]
    by_cases e1 : i = o₁
    · rw [ite_eq_left e1]; subst e1; exact v1
    rw [ite_eq_right e1]
    exact same.env (by simp [e1, e2])

end VG.Proof.X448.AArch64.Fast
