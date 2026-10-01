import VerifiedGarbage.Proof.X448.X86.Decode

/-!
# X448 on x86 (32-bit): decoding the whole coordinate

Untrusted: everything here is checked by Lean. The 28 limb loads fill two
slots while preserving input bytes outside the working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem decoded_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 28)
    (h : ∀ j < 56, m' (off p j) = m (off p j)) : decoded m' p i = decoded m p i := by
  simp only [decoded, byteN]
  rw [h (2 * i) (by omega), h (2 * i + 1) (by omega)]

theorem decodeAll_ok {s : State} {base p : Addr} (hs : Scr s base)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block ((List.range 28).flatMap decodeLimb)) s fun t =>
      (∀ j < 28, limbs t.mem base X1 j = decoded s.mem p j) ∧
      (∀ j < 28, limbs t.mem base X3 j = decoded s.mem p j) ∧
      Outside2 base X1 112 X3 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, limbs t.mem base X1 j = decoded s.mem p j) ∧
    (∀ j < n, limbs t.mem base X3 j = decoded s.mem p j) ∧
    Outside2 base X1 (4 * n) X3 (4 * n) s.mem t.mem ∧ Keeps [.eax, .edx] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (decodeLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp : (t.gpr .esi).setWidth 64 = p := by rw [tk.1 _ (by decide)]; exact hp
    have tfit : (t.gpr .esi).toNat + 56 ≤ 2 ^ 32 := by rw [tk.1 _ (by decide)]; exact hfit
    have tr : ∀ j < 56, InRegions (t.rd ++ t.wr) (off p j) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj
    have byte : ∀ j < 56, t.mem (off p j) = s.mem (off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega)) (Or.inr (by simp only [X3, slot]; omega))
    have eq := decoded_congr hn byte
    refine WP.mono (decodeLimb_ok (hs.of_keeps tk (by decide)) hn tp tfit tr) fun u ⟨um, uk⟩ => ?_
    rw [eq] at um
    let v := BitVec.ofNat 32 (decoded s.mem p n)
    have vn : v.toNat = decoded s.mem p n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem p n) (by decide))]
    have pair := fun j (hj : j < 28) => pair_write (m := t.mem) (base := base)
      (x := X1) (y := X3) (by decide) (by decide) (by decide) hn hj v v
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact ty j (by omega)
    · rw [um]
      exact (tm.mono (by omega) (by omega)).trans (decodeLimb_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86
