import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Field
import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Copy
import VerifiedGarbage.Proof.Curve448.AArch64.Swap
import VerifiedGarbage.Impl.X448.AArch64.Fast

/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Each field operation updates
the slots it writes. Every slot's limbs stay below `Ib`; products leave
reduced limbs (below `Mb`), which sums and differences need of their
operands.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot)
open VG.Proof.X448.AArch64.Weak (Index Env slot_bound slot_aligned slot_sep opMul opAdd opSub
  opA24 opCopy opSwap)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (toFe)

abbrev fclob := VG.Proof.Curve448.AArch64.Fast.clob

/-- Limbs below `n`. -/
def Bnd (n : Nat) (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 8, limbs m base o i < n

/-- Every slot's limbs are below `Ib`. -/
def BEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bnd Ib m base (slot i.val)

/-- What a field operation preserves: registers outside `clob`, and memory
outside the field slots and the coefficient area. -/
structure FKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps fclob s t
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem FKeep.refl (base : Addr) (s : State) : FKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem FKeep.trans {base : Addr} {s t u : State} (h : FKeep base s t) (h' : FKeep base t u) :
    FKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem FKeep.scr {base : Addr} {s t : State} (h : FKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

/-- Slots other than `os` keep their limbs. -/
def Same (base : Addr) (os : List Index) (m m' : Mem) : Prop :=
  ∀ i : Index, i ∉ os → ∀ j < 8, limbs m' base (slot i.val) j = limbs m base (slot i.val) j

theorem Same.bnd {base : Addr} {os : List Index} {m m' : Mem} (h : Same base os m m') {n : Nat}
    {i : Index} (hi : i ∉ os) (hb : Bnd n m base (slot i.val)) : Bnd n m' base (slot i.val) :=
  fun j hj => by rw [h i hi j hj]; exact hb j hj

theorem Same.env {base : Addr} {os : List Index} {m m' : Mem} (h : Same base os m m') {i : Index}
    (hi : i ∉ os) : VG.Proof.X448.AArch64.Weak.E m' base i = VG.Proof.X448.AArch64.Weak.E m base i :=
  congrArg toFe (VG.Proof.X448.Wide.valN_congr (h i hi))

theorem slot_lt (i : Index) : slot i.val + 128 ≤ ACC := slot_bound i

theorem slot_64 (i : Index) : slot i.val + 64 ≤ ACC := by have := slot_bound i; omega

theorem slot_mem (i : Index) : slot i.val + 128 ≤ 8192 := by
  have := slot_bound i; have : ACC = 3584 := rfl; omega

theorem slot_sep64 {i j : Index} (h : i ≠ j) : slot i.val + 64 ≤ slot j.val ∨ slot j.val + 64 ≤ slot i.val := by
  have := slot_sep h; omega

/-- Byte frame of an operation writing slot `o`'s first 64 bytes and the coefficient area. -/
theorem fieldMem_same {base : Addr} {o : Index} {m m' : Mem} (h : FieldMem base (slot o.val) m m') :
    Same base [o] m m' := by
  intro i hi j hj
  have hne : i ≠ o := fun e => hi (by simp [e])
  exact h.limbs (slot_sep hne) (slot_bound i) (by omega : j < 16)

theorem fieldMem_outside2 {base : Addr} {o : Index} {m m' : Mem} (h : FieldMem base (slot o.val) m m') :
    Outside2 base 64 2816 ACC 1152 m m' := by
  intro p hp hq
  apply h p _ (hq.imp_right fun h => Nat.le_trans (Nat.add_le_add_left (by decide : 512 ≤ 1152) _) h)
  have := o.isLt
  simp only [slot]
  omega

theorem slot_inj {i j : Index} (h : slot i.val = slot j.val) : i = j := by
  apply Fin.ext; simp only [slot] at h; omega

theorem env_update {base : Addr} {s t : State} {o : Index} (hb : BEnv s.mem base)
    (hm : FieldMem base (slot o.val) s.mem t.mem) (ho : Bnd Ib t.mem base (slot o.val)) :
    BEnv t.mem base := by
  intro i
  by_cases h : i = o
  · subst h; exact ho
  · exact (fieldMem_same hm).bnd (by simp [h]) (hb i)

theorem fmulE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b) :
    WP isa (.block (Impl.X448.AArch64.Fast.fmul (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o.val) ∧
      Same base [o] s.mem t.mem ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  have post : ∀ t : State, (∀ i < 8, limbs t.mem base (slot o.val) i =
      VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base (slot a.val))
        (limbs s.mem base (slot b.val)) i) → FieldMem base (slot o.val) s.mem t.mem → Keeps fclob s t →
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o.val) ∧
      Same base [o] s.mem t.mem ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
    intro t tv tm tk
    have bo : Bnd Mb t.mem base (slot o.val) := fun i hi => by
      rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
    refine ⟨⟨tk, fieldMem_outside2 tm⟩, env_update hb tm (fun i hi =>
      Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, fieldMem_same tm, ?_⟩
    rw [VG.Proof.X448.AArch64.Weak.E_update tm]
    simp only [opMul]
    congr 1
    change toFe _ = toFe _ * toFe _
    rw [show VG.Proof.X448.Wide.valN (limbs t.mem base (slot o.val)) 8 =
      VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base (slot a.val))
        (limbs s.mem base (slot b.val))) 8 from VG.Proof.X448.Wide.valN_congr tv]
    exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _
  simp only [Impl.X448.AArch64.Fast.fmul]
  split
  · rename_i h
    have hab := slot_inj h
    subst hab
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.sqr_ok hs (slot_64 o) (slot_aligned o) (slot_64 a)
      (slot_aligned a) (hb a)) fun t ⟨tv, tm, tk⟩ => post t tv tm tk
  · rename_i h
    have hob' : o ≠ b := hob.resolve_left fun e => h (e ▸ rfl)
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.mul_ok hs (slot_64 o) (slot_aligned o) (slot_64 a)
      (slot_aligned a) (slot_64 b) (slot_aligned b) (slot_sep64 hob') (hb a) (hb b))
      fun t ⟨tv, tm, tk⟩ => post t tv tm tk

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

open VG.Proof.Curve448.AArch64.Fast (Away)

theorem away_same {base : Addr} {os : List Index} {m m' : Mem}
    (h : ∀ x, Away base (os.map fun i => slot i.val) 64 x → m' x = m x) : Same base os m m' := by
  intro i hi j hj
  change (word m' base (slot i.val + 8 * j)).toNat = (word m base (slot i.val + 8 * j)).toNat
  rw [VG.Proof.Curve448.AArch64.Fast.away_word h (by have := slot_mem i; omega) (fun o ho => by
    simp only [List.mem_map] at ho
    obtain ⟨k, hk, rfl⟩ := ho
    have := slot_sep (show i ≠ k from fun e => hi (e ▸ hk))
    omega)]

theorem away_outside2 {base : Addr} {os : List Index} {m m' : Mem}
    (h : ∀ x, Away base (os.map fun i => slot i.val) 64 x → m' x = m x) :
    Outside2 base 64 2816 ACC 1152 m m' := by
  intro p hp _
  apply h p
  intro o ho
  simp only [List.mem_map] at ho
  obtain ⟨k, -, rfl⟩ := ho
  have := k.isLt
  simp only [slot]
  omega

theorem away_fieldMem {base : Addr} {o : Index} {m m' : Mem}
    (h : ∀ x, Away base [slot o.val] 64 x → m' x = m x) : FieldMem base (slot o.val) m m' :=
  fun x hx _ => h x fun o' ho' => by simp at ho'; subst ho'; omega

theorem bnd_word {m : Mem} {base : Addr} {n : Nat} {o : Nat} (h : Bnd n m base o) {i : Nat} (hi : i < 8) :
    (word m base (o + 8 * i)).toNat < n := h i hi

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [o] s.mem t.mem ∧ EV t.mem base = opSub o a b (EV s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.sub_ok hs (by have := slot_mem o; omega)
    (by have := slot_mem a; omega) (by have := slot_mem b; omega) (slot_aligned o) (slot_aligned a)
    (slot_aligned b) (slot_sep64 hoa) (slot_sep64 hob)) fun t ⟨tv, tm, tk⟩ => ?_
  have tl : ∀ i < 8, limbs t.mem base (slot o.val) i =
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot a.val)) (limbs s.mem base (slot b.val)) i := by
    intro i hi
    change (word t.mem base (slot o.val + 8 * i)).toNat = _
    rw [tv i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]; rfl
  have fm := away_fieldMem tm
  refine ⟨⟨tk.mono (by decide), fieldMem_outside2 fm⟩, env_update hb fm (fun i hi => by
    rw [tl i hi]; exact VG.Proof.Curve448.AArch64.Fast.diff_bound ha i hi), fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [opSub]
  congr 1
  change toFe _ = toFe _ - toFe _
  rw [VG.Proof.X448.Wide.valN_congr tl]
  exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'

theorem bnd_of_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat} {n : Nat}
    (h : ∀ i < 8, limbs m base o i = f i) (hf : ∀ i < 8, f i < n) : Bnd n m base o :=
  fun i hi => by rw [h i hi]; exact hf i hi

theorem fe_of_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat}
    (h : ∀ i < 8, limbs m base o i = f i) :
    VG.Proof.X448.AArch64.Weak.F m base o = toFe (VG.Proof.X448.Wide.valN f 8) :=
  congrArg toFe (VG.Proof.X448.Wide.valN_congr h)

theorem addSubE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o₁ o₂ a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (h12 : o₁ ≠ o₂)
    (h1a : o₁ ≠ a) (h1b : o₁ ≠ b) (h2a : o₂ ≠ a) (h2b : o₂ ≠ b) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.addSub (slot o₁.val) (slot o₂.val) (slot a.val)
        (slot b.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [o₁, o₂] s.mem t.mem ∧
      EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a + EV s.mem base b))
        o₂ (EV s.mem base a - EV s.mem base b) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.addSub_ok hs (by have := slot_mem o₁; omega)
    (by have := slot_mem o₂; omega) (by have := slot_mem a; omega) (by have := slot_mem b; omega)
    (slot_aligned o₁) (slot_aligned o₂) (slot_aligned a) (slot_aligned b) (slot_sep64 h12)
    (slot_sep64 h1a) (slot_sep64 h1b) (slot_sep64 h2a) (slot_sep64 h2b)) fun t ⟨t1, t2, tm, tk⟩ => ?_
  have l1 : ∀ i < 8, limbs t.mem base (slot o₁.val) i =
      limbs s.mem base (slot a.val) i + limbs s.mem base (slot b.val) i := fun i hi => by
    change (word t.mem base (slot o₁.val + 8 * i)).toNat = _
    rw [t1 i hi, VG.Proof.Curve448.AArch64.Fast.sum_word _ _ (ha i hi) (hb' i hi)]
  have l2 : ∀ i < 8, limbs t.mem base (slot o₂.val) i =
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot a.val)) (limbs s.mem base (slot b.val)) i :=
    fun i hi => by
      change (word t.mem base (slot o₂.val + 8 * i)).toNat = _
      rw [t2 i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]; rfl
  have sm : Same base [o₁, o₂] s.mem t.mem := away_same (os := [o₁, o₂]) tm
  refine ⟨⟨tk.mono (by decide), away_outside2 (os := [o₁, o₂]) tm⟩, fun i => ?_, sm, ?_⟩
  · by_cases e1 : i = o₁
    · subst e1; exact bnd_of_limbs l1 (VG.Proof.Curve448.AArch64.Fast.sum_bound ha hb')
    · by_cases e2 : i = o₂
      · subst e2; exact bnd_of_limbs l2 (VG.Proof.Curve448.AArch64.Fast.diff_bound ha)
      · exact sm.bnd (by simp [e1, e2]) (hb i)
  · funext i
    simp only [Function.update_apply]
    by_cases e2 : i = o₂
    · subst e2
      rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot i.val) = _
      rw [fe_of_limbs l2]
      exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'
    · rw [ite_eq_right e2]
      by_cases e1 : i = o₁
      · subst e1
        rw [ite_eq_left rfl]
        change VG.Proof.X448.AArch64.Weak.F t.mem base (slot i.val) = _
        rw [fe_of_limbs l1]
        exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
      · rw [ite_eq_right e1]; exact sm.env (by simp [e1, e2])

theorem smallE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a e : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.small (slot o.val) (slot a.val) (slot e.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [o] s.mem t.mem ∧
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a + Spec.X448.a24 * EV s.mem base e) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.small_ok hs (by have := slot_mem o; omega)
    (by have := slot_mem a; omega) (by have := slot_mem e; omega) (slot_aligned o) (slot_aligned a)
    (slot_aligned e) ha (hb e)) fun t ⟨tv, tm, tk⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := VG.Proof.X448.AArch64.FieldMem.output (tm.mono (Nat.le_refl _) (by omega))
  refine ⟨⟨tk.mono (by decide), fieldMem_outside2 fm⟩, env_update hb fm
    (bnd_of_limbs tv (VG.Proof.Curve448.AArch64.Fast.small_bound ha (hb e))), fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  congr 1
  change VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = _
  rw [fe_of_limbs tv]
  exact VG.Proof.Curve448.AArch64.Fast.smallF _ _

/-- Slot `i` of the swapped coordinates (`x₂, z₂, x₃, z₃` are slots 1–4). -/
def swp (sw : Bool) (i : Index) : Index := if sw then (if i = 1 then 3 else if i = 3 then 1 else
  if i = 2 then 4 else if i = 4 then 2 else i) else i

/-- The butterfly's result on the field slots. -/
def bflyEnv (sw : Bool) (e : Env) : Env := fun i =>
  if i = 5 then e (swp sw 1) + e (swp sw 2) else if i = 6 then e (swp sw 1) - e (swp sw 2)
  else if i = 7 then e (swp sw 3) + e (swp sw 4) else if i = 8 then e (swp sw 3) - e (swp sw 4)
  else e i

theorem sel_slot (m : Mem) (base : Addr) (sw : Bool) (p q : Index) (i : Nat) :
    VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (slot p.val + 8 * i)) (word m base (slot q.val + 8 * i)) =
      word m base (slot (if sw then q else p).val + 8 * i) := by
  cases sw <;> rfl

theorem bflyE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hM : ∀ i : Index, i.val ∈ [1, 2, 3, 4] → Bnd Mb s.mem base (slot i.val))
    {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.butterfly X2 Z2 X3 Z3 A B C D)) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [5, 6, 7, 8] s.mem t.mem ∧
      EV t.mem base = bflyEnv sw (EV s.mem base) := by
  have hX2 : X2 = slot (1 : Index).val := rfl
  have hZ2 : Z2 = slot (2 : Index).val := rfl
  have hX3 : X3 = slot (3 : Index).val := rfl
  have hZ3 : Z3 = slot (4 : Index).val := rfl
  have hA : A = slot (5 : Index).val := rfl
  have hB : B = slot (6 : Index).val := rfl
  have hC : C = slot (7 : Index).val := rfl
  have hD : D = slot (8 : Index).val := rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.butterfly_ok hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hm) fun t ⟨tv, tm, tk⟩ => ?_
  have sw1 : ∀ p q : Index, p.val ∈ [1, 2, 3, 4] → q.val ∈ [1, 2, 3, 4] →
      Bnd Mb s.mem base (slot (if sw then q else p).val) := fun p q hp hq => by
    cases sw
    · exact hM p hp
    · exact hM q hq
  have val : ∀ (o : Nat) (k : Index) (p q : Index), o = slot k.val →
      (∀ i < 8, word t.mem base (o + 8 * i) = word s.mem base (slot p.val + 8 * i) +
        word s.mem base (slot q.val + 8 * i)) → Bnd Mb s.mem base (slot p.val) → Bnd Mb s.mem base (slot q.val) →
      (∀ i < 8, limbs t.mem base (slot k.val) i = limbs s.mem base (slot p.val) i + limbs s.mem base (slot q.val) i) :=
    fun o k p q ho h hp hq i hi => by
      subst ho
      change (word t.mem base (slot k.val + 8 * i)).toNat = _
      rw [h i hi, VG.Proof.Curve448.AArch64.Fast.sum_word _ _ (hp i hi) (hq i hi)]
  have dif : ∀ (k : Index) (p q : Index),
      (∀ i < 8, word t.mem base (slot k.val + 8 * i) = word s.mem base (slot p.val + 8 * i) +
        VG.Proof.Curve448.AArch64.Fast.twoPW i - word s.mem base (slot q.val + 8 * i)) →
      Bnd Mb s.mem base (slot p.val) → Bnd Mb s.mem base (slot q.val) →
      (∀ i < 8, limbs t.mem base (slot k.val) i =
        VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot p.val)) (limbs s.mem base (slot q.val)) i) :=
    fun k p q h hp hq i hi => by
      change (word t.mem base (slot k.val + 8 * i)).toNat = _
      rw [h i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (hp i hi) (hq i hi)]; rfl
  let x2 := swp sw 1; let z2 := swp sw 2; let x3 := swp sw 3; let z3 := swp sw 4
  have ex2 : (if sw then (3 : Index) else 1) = x2 := by cases sw <;> rfl
  have ez2 : (if sw then (4 : Index) else 2) = z2 := by cases sw <;> rfl
  have ex3 : (if sw then (1 : Index) else 3) = x3 := by cases sw <;> rfl
  have ez3 : (if sw then (2 : Index) else 4) = z3 := by cases sw <;> rfl
  have mx2 := sw1 1 3 (by decide) (by decide); rw [ex2] at mx2
  have mz2 := sw1 2 4 (by decide) (by decide); rw [ez2] at mz2
  have mx3 := sw1 3 1 (by decide) (by decide); rw [ex3] at mx3
  have mz3 := sw1 4 2 (by decide) (by decide); rw [ez3] at mz3
  have wA : ∀ i < 8, word t.mem base (slot (5 : Index).val + 8 * i) =
      word s.mem base (slot x2.val + 8 * i) + word s.mem base (slot z2.val + 8 * i) := fun i hi => by
    rw [← hA, tv A (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, ite_true, hX2, hX3, hZ2, hZ3, sel_slot, ex2, ez2]
  have wB : ∀ i < 8, word t.mem base (slot (6 : Index).val + 8 * i) =
      word s.mem base (slot x2.val + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i -
        word s.mem base (slot z2.val + 8 * i) := fun i hi => by
    rw [← hB, tv B (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show B ≠ A by decide, ite_true, ite_false, hX2, hX3,
      hZ2, hZ3, sel_slot, ex2, ez2]
  have wC : ∀ i < 8, word t.mem base (slot (7 : Index).val + 8 * i) =
      word s.mem base (slot x3.val + 8 * i) + word s.mem base (slot z3.val + 8 * i) := fun i hi => by
    rw [← hC, tv C (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show C ≠ A by decide, show C ≠ B by decide, ite_true,
      ite_false, hX2, hX3, hZ2, hZ3, sel_slot, ex3, ez3]
  have wD : ∀ i < 8, word t.mem base (slot (8 : Index).val + 8 * i) =
      word s.mem base (slot x3.val + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i -
        word s.mem base (slot z3.val + 8 * i) := fun i hi => by
    rw [← hD, tv D (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show D ≠ A by decide, show D ≠ B by decide,
      show D ≠ C by decide, ite_false, hX2, hX3, hZ2, hZ3, sel_slot, ex3, ez3]
  have lA := val _ 5 x2 z2 rfl wA mx2 mz2
  have lB := dif 6 x2 z2 wB mx2 mz2
  have lC := val _ 7 x3 z3 rfl wC mx3 mz3
  have lD := dif 8 x3 z3 wD mx3 mz3
  have sm : Same base [5, 6, 7, 8] s.mem t.mem := away_same (os := [5, 6, 7, 8]) tm
  refine ⟨⟨tk.mono (by decide), away_outside2 (os := [5, 6, 7, 8]) tm⟩, fun i => ?_, sm, ?_⟩
  · by_cases e5 : i = 5
    · subst e5; exact bnd_of_limbs lA (VG.Proof.Curve448.AArch64.Fast.sum_bound mx2 mz2)
    by_cases e6 : i = 6
    · subst e6; exact bnd_of_limbs lB (VG.Proof.Curve448.AArch64.Fast.diff_bound mx2)
    by_cases e7 : i = 7
    · subst e7; exact bnd_of_limbs lC (VG.Proof.Curve448.AArch64.Fast.sum_bound mx3 mz3)
    by_cases e8 : i = 8
    · subst e8; exact bnd_of_limbs lD (VG.Proof.Curve448.AArch64.Fast.diff_bound mx3)
    exact sm.bnd (by simp [e5, e6, e7, e8]) (hb i)
  · funext i
    simp only [bflyEnv]
    by_cases e5 : i = 5
    · subst e5; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((5 : Index) : Nat)) = _
      rw [fe_of_limbs lA]; exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
    rw [ite_eq_right e5]
    by_cases e6 : i = 6
    · subst e6; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((6 : Index) : Nat)) = _
      rw [fe_of_limbs lB]; exact VG.Proof.Curve448.AArch64.Fast.diff_val mz2
    rw [ite_eq_right e6]
    by_cases e7 : i = 7
    · subst e7; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((7 : Index) : Nat)) = _
      rw [fe_of_limbs lC]; exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
    rw [ite_eq_right e7]
    by_cases e8 : i = 8
    · subst e8; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((8 : Index) : Nat)) = _
      rw [fe_of_limbs lD]; exact VG.Proof.Curve448.AArch64.Fast.diff_val mz3
    rw [ite_eq_right e8]
    exact sm.env (by simp [e5, e6, e7, e8])

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ (∀ j < 8, limbs t.mem base (slot o.val) j = limbs s.mem base (slot a.val) j) ∧
      Same base [o] s.mem t.mem ∧ EV t.mem base = opCopy o a (EV s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (slot_mem o) (slot_mem a) (slot_aligned o)
    (slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := VG.Proof.X448.AArch64.FieldMem.output tm
  refine ⟨⟨tk.mono (by decide), fieldMem_outside2 fm⟩, env_update hb fm (fun i hi => by
    rw [tf i hi]; exact hb a i hi), tf, fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  congr 1
  exact congrArg toFe (VG.Proof.X448.Wide.valN_congr tf)

end VG.Proof.X448.AArch64.Fast
