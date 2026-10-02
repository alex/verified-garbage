import VerifiedGarbage.Proof.X448.X86_64.Swap

/-!
# X448 on x86-64: the working space as slots

The working space as 22 slots of 64 bytes (`E`), each read as a field
element: each field operation updates one slot (`Function.update`) and the
swap two, so that a sequence of operations is a chain of updates that `simp`
evaluates at any slot. The field operations change no byte outside the slots
and the product's words, `[64, 1648)`.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

abbrev Index := Fin 22

/-- Environments: the working space's slots. -/
abbrev Env := Index → Spec.X448.Fe

/-- The working space as 22 field elements. -/
def E (m : Mem) (base : Addr) (i : Index) : Spec.X448.Fe := F m base (slot i.val)

theorem slot_lt (i : Index) : slot i.val + 56 ≤ ACC := by
  have := i.isLt; simp only [slot, ACC]; omega

theorem slot_ge (i : Index) : 64 ≤ slot i.val := by simp only [slot]; omega

theorem slot_sep {i j : Index} (h : i ≠ j) :
    slot i.val + 56 ≤ slot j.val ∨ slot j.val + 56 ≤ slot i.val := by
  have : i.val ≠ j.val := fun e => h (Fin.ext e)
  simp only [slot]; omega

theorem E_update {base : Addr} {m m' : Mem} {o : Index}
    (h : Outside2 base (slot o.val) 56 ACC 112 m m') :
    E m' base = Function.update (E m base) o (F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [E]
  · rw [Function.update_of_ne hi]
    have := slot_lt i
    simp only [ACC] at this
    show toFe (mv m' base (slot i.val) 7) = toFe (mv m base (slot i.val) 7)
    rw [h.mv (slot_sep hi) (Or.inl (by simp only [ACC]; omega)) (by omega)]

/-- What the field operations keep: the registers but `clob`, the regions,
and the memory outside `[64, 1648)`. -/
structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 64 1584 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : Keep base s₁ s₂) (h₂ : Keep base s₂ s₃) :
    Keep base s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem Keep.scr {base : Addr} {s s' : State} (h : Keep base s s') (hs : Scr s base) : Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.keep {base : Addr} {o : Index} {s s' : State} (h : Op base (slot o.val) s s') :
    Keep base s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem.outside (slot_ge o) (by have := slot_lt o; simp only [ACC] at *; omega)
    (by decide) (by decide)⟩

/-! ## The field multiplications -/

/-- What the rest of the proof needs of the field multiplications `fld`:
each writes the field element at `o` and the product's words, and nothing
else of the working space, and changes only the registers `clob` (`Op`). -/
structure FieldOk (fld : Field) : Prop where
  mul : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a b : Nat}, Slot o → Slot a → Slot b →
    WP isa (.block (fld.mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b
  sqr : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a : Nat}, Slot o → Slot a →
    WP isa (.block (fld.sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a
  a24 : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a : Nat}, Slot o → Slot a →
    WP isa (.block (fld.a24 o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = Spec.X448.a24 * F s.mem base a

theorem baseline_ok : FieldOk baseline where
  mul hs _ _ _ ho ha hb := mul_ok hs ho ha hb
  sqr hs _ _ ho ha := sqr_ok hs ho ha
  a24 hs _ _ ho ha := WP.mono (mulSmall_ok hs ho ha (k := a24) (by decide)) fun _ ⟨h, e⟩ =>
    ⟨h, toFe_a24 e⟩

/-! ## The field operations on the slots -/

variable {fld : Field} (hf : FieldOk fld)

def opMul (o a b : Index) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Index) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Index) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Index) (e : Env) : Env := Function.update e o (Spec.X448.a24 * e a)
def opSwap (x y : Index) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

include hf in
theorem mulE {s : State} {base : Addr} (hs : Scr s base) (o a b : Index) :
    WP isa (.block (fld.mul (slot o.val) (slot a.val) (slot b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opMul o a b (E s.mem base) :=
  WP.mono (hf.mul hs (slot_lt o) (slot_lt a) (slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [E_update h.mem, e]; rfl⟩

include hf in
theorem sqrE {s : State} {base : Addr} (hs : Scr s base) (o a : Index) :
    WP isa (.block (fld.sqr (slot o.val) (slot a.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opMul o a a (E s.mem base) :=
  WP.mono (hf.sqr hs (slot_lt o) (slot_lt a)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (o a b : Index) :
    WP isa (.block (add (slot o.val) (slot a.val) (slot b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (add_ok hs (slot_lt o) (slot_lt a) (slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (o a b : Index) :
    WP isa (.block (sub (slot o.val) (slot a.val) (slot b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opSub o a b (E s.mem base) :=
  WP.mono (sub_ok hs (slot_lt o) (slot_lt a) (slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [E_update h.mem, e]; rfl⟩

include hf in
theorem a24E {s : State} {base : Addr} (hs : Scr s base) (o a : Index) :
    WP isa (.block (fld.a24 (slot o.val) (slot a.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opA24 o a (E s.mem base) :=
  WP.mono (hf.a24 hs (slot_lt o) (slot_lt a)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [E_update h.mem, e]; rfl⟩

theorem fe_sel {m m' : Mem} {base : Addr} {x y : Nat} {sw : Bool}
    (h : ∀ i < 7, word m' base (x + 8 * i) =
      if sw then word m base (y + 8 * i) else word m base (x + 8 * i)) :
    fe m' base x = if sw then fe m base y else fe m base x := by
  rw [fe, mv7, fe, fe, mv7, mv7]
  cases sw
  · simp only [Bool.false_eq_true, ite_false] at h ⊢
    exact val7_congr fun i hi => by rw [h i hi]
  · simp only [ite_true] at h ⊢
    exact val7_congr fun i hi => by rw [h i hi]

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (x y : Index) (hxy : x ≠ y) {sw : Bool}
    (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap (slot x.val) (slot y.val))) s fun s' =>
      Keep base s s' ∧ s'.gpr .rcx = s.gpr .rcx ∧ E s'.mem base = opSwap x y sw (E s.mem base) := by
  have hx := slot_lt x; have hy := slot_lt y
  have gx := slot_ge x; have gy := slot_ge y
  simp only [ACC] at hx hy
  refine WP.mono (cswap_ok hs hx hy (slot_sep hxy) hm) fun s' ⟨fx, fy, out, k⟩ => ?_
  refine ⟨⟨fun r hr => k.1 r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide), k.2.1, k.2.2,
    out.outside gx (by omega) gy (by omega)⟩, k.1 _ (by decide), ?_⟩
  funext i
  have ex : E s'.mem base x = if sw then E s.mem base y else E s.mem base x := by
    simp only [E, F, fe_sel fx]; cases sw <;> rfl
  have ey : E s'.mem base y = if sw then E s.mem base x else E s.mem base y := by
    simp only [E, F, fe_sel fy]; cases sw <;> rfl
  by_cases hiy : i = y
  · subst hiy; rw [opSwap, Function.update_self]; exact ey
  · rw [opSwap, Function.update_of_ne hiy]
    by_cases hix : i = x
    · subst hix; rw [Function.update_self]; exact ex
    · rw [Function.update_of_ne hix]
      have hi := slot_lt i
      simp only [ACC] at hi
      show toFe (mv s'.mem base (slot i.val) 7) = toFe (mv s.mem base (slot i.val) 7)
      rw [out.mv (slot_sep hix) (slot_sep hiy) (by omega)]

end VG.Proof.X448.X86_64
