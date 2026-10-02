import VerifiedGarbage.Proof.Curve448.AArch64.Pointwise
import VerifiedGarbage.Proof.Curve448.AArch64.Square
import VerifiedGarbage.Proof.Curve448.AArch64.Swap
import VerifiedGarbage.Proof.X448.AArch64.Env
import VerifiedGarbage.Impl.X448.AArch64.Weak
/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Field operations update one
of twenty-two slots, preserving bounded limbs in every slot. The frame
excludes saved registers, the swap bit and the scalar's decoded bits.
-/

namespace VG.Proof.X448.AArch64.Weak

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.Curve448.AArch64
open VG.Impl.X448.AArch64.Weak
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe :=
  VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs m base o) 8)
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Wide.valN (limbs m base o) 8
abbrev Bounded := VG.Proof.Curve448.AArch64.Bounded
abbrev valN := VG.Proof.X448.Wide.valN
theorem valN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    VG.Proof.X448.Wide.valN f n = VG.Proof.X448.Wide.valN g n := VG.Proof.X448.Wide.valN_congr h

abbrev Index := Fin 22
abbrev Env := Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bounded m base (slot i.val)

abbrev workRegs := VG.Proof.X448.AArch64.workRegs
abbrev Keep := VG.Proof.X448.AArch64.Keep

theorem slot_bound (i : Index) : Slot (slot i.val) := by
  simp only [Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_aligned (i : Index) : slot i.val % 8 = 0 := by
  simp only [slot]; omega

theorem slot_sep {i j : Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem E_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m') :
    E m' base = Function.update (E m base) o (F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, E]
  · rw [Function.update_of_ne hi]
    simp only [E, F]
    exact congrArg toFe (valN_congr (fun j hj =>
      h.limbs (slot_sep hi) (slot_bound i) (by omega : j < 16)))

theorem bounded_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m')
    (hm : BoundedEnv m base) (ho : Bounded m' base (slot o.val)) : BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (slot_sep hi) (slot_bound i) (by omega : j < 16)]
    exact hm i j hj

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Index) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Index) (e : Env) : Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : Index) (e : Env) : Env := Function.update e o (e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (Impl.Curve448.AArch64.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opMul o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.mul_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) * F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.Curve448.AArch64.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.add_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) + F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.Curve448.AArch64.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opSub o a b (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.sub_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (slot_bound b) (slot_aligned b) (hb a) (hb b)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = F s.mem base (slot a.val) - F s.mem base (slot b.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.small (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opA24 o a (E s.mem base) :=
  WP.mono (VG.Proof.Curve448.AArch64.small_ok hs (slot_bound o) (slot_aligned o) (slot_bound a) (slot_aligned a) (hb a)) fun t ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by
      have e' : F t.mem base (slot o.val) = Spec.X448.a24 * F s.mem base (slot a.val) := e
      rw [E_update h.mem, e']; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opCopy o a (E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (Nat.le_trans (slot_bound o) (by decide))
    (Nat.le_trans (slot_bound a) (by decide)) (slot_aligned o) (slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [E_update op.mem, show F t.mem base (slot o.val) = F s.mem base (slot a.val) from
      congrArg toFe (valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      E t.mem base = opSwap x y sw (E s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (slot_bound x) (slot_bound y) (slot_aligned x) (slot_aligned y) (slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : Index, i ≠ x → i ≠ y → ∀ j < 8,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := slot_sep hix
    have ey := slot_sep hiy
    have hi := slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 128 ≤ 3584 at hi; omega)]
  have fx : E t.mem base x = if sw then E s.mem base y else E s.mem base x := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact tx
  have fy : E t.mem base y = if sw then E s.mem base x else E s.mem base y := by
    cases sw <;> apply congrArg toFe <;> apply valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg toFe (valN_congr (other i hix hiy))

end VG.Proof.X448.AArch64.Weak
