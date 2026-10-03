import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr

/-!
# Limb-by-limb operations

Untrusted: everything here is checked by Lean. `limbs_loop`: eight steps,
step `i` writing limb `i` of each output slot from the unchanged inputs.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs)

/-- Byte `x` is outside every output slot (64 bytes from each of `outs`). -/
def Away (base : Addr) (outs : List Nat) (n : Nat) (x : Addr) : Prop :=
  ∀ o ∈ outs, ofs base x < o ∨ o + n ≤ ofs base x

theorem word_congr {base : Addr} {m m' : Mem} {d : Nat} (hd : d + 8 ≤ 8192)
    (h : ∀ x, d ≤ ofs base x → ofs base x < d + 8 → m' x = m x) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem limbs_loop {base : Addr} {body : Nat → List Instr} {outs : List Nat} {rs : List Reg}
    (P : State → Prop) (hP : ∀ t u, P t → Keeps rs t u → P u) (hrs : .x3 ∉ rs ∧ .x12 ∉ rs)
    (V : Nat → Nat → BitVec 64) (s : State)
    (hstep : ∀ i < 8, ∀ t, Scr t base → P t → (∀ x, Away base outs 64 x → t.mem x = s.mem x) →
      WP isa (.block (body i)) t fun u =>
        (∀ o ∈ outs, word u.mem base (o + 8 * i) = V o i) ∧
        (∀ x, (∀ o ∈ outs, ofs base x < o + 8 * i ∨ o + 8 * i + 8 ≤ ofs base x) → u.mem x = t.mem x) ∧
        Keeps rs t u)
    (hw : ∀ o ∈ outs, o + 64 ≤ 8192) (sep : ∀ o ∈ outs, ∀ o' ∈ outs, o ≠ o' → o + 64 ≤ o' ∨ o' + 64 ≤ o)
    (hs : Scr s base) (hP0 : P s) :
    WP isa (.block ((List.range 8).flatMap body)) s fun t =>
      (∀ o ∈ outs, ∀ i < 8, word t.mem base (o + 8 * i) = V o i) ∧
      (∀ x, Away base outs 64 x → t.mem x = s.mem x) ∧ Keeps rs s t := by
  let inv := fun n (t : State) =>
    Scr t base ∧ P t ∧ (∀ o ∈ outs, ∀ i < n, word t.mem base (o + 8 * i) = V o i) ∧
      (∀ x, (∀ o ∈ outs, ofs base x < o ∨ o + 8 * n ≤ ofs base x) → t.mem x = s.mem x) ∧
      Keeps rs s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨ts, tp, tv, tm, tk⟩ => ?_) 8
    (by decide) s ⟨hs, hP0, fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, Keeps.refl _ _⟩)
    fun t ⟨_, _, tv, tm, tk⟩ => ⟨tv, fun x hx => tm x hx, tk⟩
  refine WP.mono (hstep n hn t ts tp (fun x hx => tm x fun o ho => by
    have := hx o ho; omega)) fun u ⟨uv, um, uk⟩ => ⟨ts.of_keeps uk hrs, hP t u tp uk, ?_, ?_, tk.trans uk⟩
  · intro o ho i hi
    by_cases h : i = n
    · subst h; exact uv o ho
    · rw [← tv o ho i (by omega)]
      have ho64 := hw o ho
      refine word_congr (by omega) fun x h1 h2 => um x fun o' ho' => ?_
      by_cases e : o' = o
      · subst e; omega
      · have := sep o ho o' ho' (Ne.symm e)
        omega
  · intro x hx
    rw [um x (fun o ho => by have := hx o ho; omega), tm x (fun o ho => by have := hx o ho; omega)]

end VG.Proof.Curve448.AArch64.Fast
