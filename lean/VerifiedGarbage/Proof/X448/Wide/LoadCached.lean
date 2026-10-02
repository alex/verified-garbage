import VerifiedGarbage.Proof.X448.Wide.CacheRegs
import VerifiedGarbage.Proof.X448.Wide.Column

/-! Untrusted: load eight wide limbs into the cached operand registers. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem cacheLoadStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : a + 64 ≤ 8192) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld (cacheReg i) (a + 8 * i)]) s fun t =>
      t.gpr (cacheReg i) = word s.mem base (a + 8 * i) ∧
      t.mem = s.mem ∧ Keeps [cacheReg i] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.load, hs.x3, al, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem loadCached_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat}
    (ha : a + 64 ≤ 8192) (ha8 : a % 8 = 0) :
    WP isa (.block (loadCached a)) s fun t =>
      (∀ i < 8, t.gpr (cacheReg i) = word s.mem base (a + 8 * i)) ∧
      t.mem = s.mem ∧ Keeps sqrRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (cacheReg i) = word s.mem base (a + 8 * i)) ∧
    t.mem = s.mem ∧ Keeps sqrRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld (cacheReg n) (a + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (cacheLoadStep_ok (hs.of_keeps tk (by decide)) ha ha8 hn) fun u ⟨uf, um, uk⟩ => ?_
    refine ⟨?_, um.trans tm, tk.trans (uk.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact cacheReg_member hn))⟩
    intro i hi
    by_cases h : i = n
    · subst i; rw [uf, tm]
    · rw [uk.1 _ (by
        simp only [List.mem_singleton]
        intro e; exact h ((cacheReg_inj (by omega) hn).1 e))]
      exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, rfl, Keeps.refl _ _⟩

end VG.Proof.X448.Wide
