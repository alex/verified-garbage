import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.X86_64.Small
import VerifiedGarbage.Proof.X448.X86_64.Swap

/-!
# X448 on x86-64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Field operations update one
of twenty-two slots, preserving bounded limbs in every slot. The frame
excludes saved registers, the swap bit and the scalar's decoded bits.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

abbrev Index := Fin 22
abbrev Env := Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bounded m base (slot i.val)

def workRegs : List Reg := .r8 :: clob

structure Keep (base : Addr) (s t : State) : Prop where
  regs : Keeps workRegs s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : Keep base s t) (h' : Keep base t u) :
    Keep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : Keep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem slot_bound (i : Index) : Slot (slot i.val) := by
  simp only [Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_sep {i j : Index} (h : i ≠ j) : slot i.val + 128 ≤ slot j.val ∨ slot j.val + 128 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem Op.keep {base : Addr} {o : Index} {s t : State} (h : Op base (slot o.val) s t) : Keep base s t := by
  refine ⟨h.keeps.mono (fun _ hr => List.mem_cons_of_mem _ hr), ?_⟩
  intro p hp hq
  apply h.mem p _ hq
  have := o.isLt
  simp only [slot]
  omega

theorem E_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m') :
    E m' base = Function.update (E m base) o (F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, E]
  · rw [Function.update_of_ne hi]
    simp only [E, F]
    rw [h.fe (slot_sep hi) (slot_bound i)]

theorem bounded_update {base : Addr} {m m' : Mem} {o : Index} (h : FieldMem base (slot o.val) m m')
    (hm : BoundedEnv m base) (ho : Bounded m' base (slot o.val)) : BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (slot_sep hi) (slot_bound i) hj]
    exact hm i j hj

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Index) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Index) (e : Env) : Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : Index) (e : Env) : Env := Function.update e o (e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (Impl.X448.X86_64.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opMul o a b (E s.mem base) :=
  WP.mono (mul_ok hs (slot_bound o) (slot_bound a) (slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.X448.X86_64.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (add_ok hs (slot_bound o) (slot_bound a) (slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a b : Index) :
    WP isa (.block (Impl.X448.X86_64.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opSub o a b (E s.mem base) :=
  WP.mono (sub_ok hs (slot_bound o) (slot_bound a) (slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (mulSmall (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opA24 o a (E s.mem base) :=
  WP.mono (mulSmall_ok hs (slot_bound o) (slot_bound a) (hb a)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, bounded_update h.mem hb bo, by rw [E_update h.mem, e]; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o a : Index) :
    WP isa (.block (copy (slot o.val) (slot a.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = opCopy o a (E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (copy_ok hs (Nat.le_trans (slot_bound o) (by decide))
    (Nat.le_trans (slot_bound a) (by decide)) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [E_update op.mem, show F t.mem base (slot o.val) = F s.mem base (slot a.val) from
      congrArg toFe (valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap (slot x.val) (slot y.val))) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ t.gpr .rcx = s.gpr .rcx ∧
      E t.mem base = opSwap x y sw (E s.mem base) := by
  refine WP.mono (cswap_ok hs (slot_bound x) (slot_bound y) (slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : Index, i ≠ x → i ≠ y → ∀ j < 16,
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

end VG.Proof.X448.X86_64
