import VerifiedGarbage.Impl.X448.X86
import VerifiedGarbage.Proof.X448.Radix16
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X448 on x86 (32-bit): the working space
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 32 := m.readW (off base d) 32
abbrev limbs (m : Mem) (base : Addr) (o : Nat) (i : Nat) : Nat := (word m base (o + 4 * i)).toNat
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := valN (limbs m base o) 28

def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 28, limbs m base o i < radix

/-- The registers and permissions that an arithmetic operation preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs s₂ s₃) :
    Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.then {rs rs' : List Reg} {s t u : State} (h : Keeps rs s t) (h' : Keeps rs' t u) :
    Keeps (rs ++ rs') s u :=
  (h.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (h'.mono (fun _ hr => List.mem_append_right _ hr))

structure Scr (s : State) (base : Addr) : Prop where
  edi : (s.gpr .edi).setWidth 64 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (s.gpr .edi).toNat + 8192 ≤ 2 ^ 32

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : Keeps rs s s') (hr : .edi ∉ rs) : Scr s' base :=
  ⟨by rw [h.1 _ hr]; exact hs.edi, h.2.2 ▸ hs.wr,
    by rw [h.1 _ hr]; exact hs.nowrap⟩

theorem Scr.ea {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 8192) :
    s.ea (sc d) = off base d := by
  change addr (s.gpr .edi) d = _
  rw [addr_eq (by have := hs.nowrap; omega), hs.edi]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (off base d) n := ⟨_, hs.wr, contains_sc hd⟩

abbrev ofs (base x : Addr) : Nat := (x - base).toNat

def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Outside base o n m₁ m₂)
    (h₂ : Outside base o n m₂ m₃) : Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hl : o' ≤ o) (hr : o + n ≤ o' + n') : Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    ofs base (off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [ofs, off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 8192) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.limbs {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + n ≤ d) (hd' : d + 112 ≤ 8192) {i : Nat} (hi : i < 28) :
    limbs m' base d i = limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + n ≤ d) (hd' : d + 112 ≤ 8192) : fe m' base d = fe m base d :=
  valN_congr fun _ hi => h.limbs hd hd' hi

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 8192) :
    Outside base d 4 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem word_write (m : Mem) (base : Addr) {o i j : Nat} (ho : o + 4 * (i + 1) ≤ 8192)
    (hj : o + 4 * (j + 1) ≤ 8192) (v : BitVec 32) :
    word (m.writeW (off base (o + 4 * i)) v) base (o + 4 * j) =
      if j = i then v else word m base (o + 4 * j) := by
  by_cases h : j = i
  · rw [ite_eq_left h, h, word, Mem.readW_writeW_self32]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- A field operation writes its result and its temporary coefficients. -/
def FieldMem (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + 112 ≤ ofs base x) →
    (ofs base x < ACC ∨ ACC + 512 ≤ ofs base x) → m' x = m x

theorem FieldMem.refl (base : Addr) (o : Nat) (m : Mem) : FieldMem base o m m := fun _ _ _ => rfl

theorem FieldMem.trans {base : Addr} {o : Nat} {m₁ m₂ m₃ : Mem} (h₁ : FieldMem base o m₁ m₂)
    (h₂ : FieldMem base o m₂ m₃) : FieldMem base o m₁ m₃ :=
  fun x hx hw => (h₂ x hx hw).trans (h₁ x hx hw)

theorem FieldMem.output {base : Addr} {o : Nat} {m m' : Mem} (h : Outside base o 112 m m') :
    FieldMem base o m m' := fun x hx _ => h x hx

theorem FieldMem.work {base : Addr} {o d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hl : ACC ≤ d) (hr : d + n ≤ ACC + 512) : FieldMem base o m m' :=
  fun x _ hx => h.mono hl hr x hx

theorem FieldMem.word {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + 112 ≤ d) (hw : d + 4 ≤ ACC) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by simp only [ACC] at hw; omega)]; omega)
    (Or.inl (by rw [ofs_off base (by simp only [ACC] at hw; omega)]; omega))).symm).symm

theorem FieldMem.limbs {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + 112 ≤ d) (hw : d + 112 ≤ ACC) {i : Nat} (hi : i < 28) :
    limbs m' base d i = limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem FieldMem.fe {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + 112 ≤ d) (hw : d + 112 ≤ ACC) : fe m' base d = fe m base d :=
  valN_congr fun _ hi => h.limbs hd hw hi

/-- Memory outside two ranges, used by the conditional swap. -/
def Outside2 (base : Addr) (x nx y ny : Nat) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < x ∨ x + nx ≤ ofs base p) →
    (ofs base p < y ∨ y + ny ≤ ofs base p) → m' p = m p

theorem Outside2.refl (base : Addr) (x nx y ny : Nat) (m : Mem) : Outside2 base x nx y ny m m :=
  fun _ _ _ => rfl

theorem Outside2.trans {base : Addr} {x nx y ny : Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Outside2 base x nx y ny m₁ m₂) (h₂ : Outside2 base x nx y ny m₂ m₃) :
    Outside2 base x nx y ny m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

theorem Outside2.mono {base : Addr} {x nx y ny nx' ny' : Nat} {m m' : Mem}
    (h : Outside2 base x nx y ny m m') (hx : nx ≤ nx') (hy : ny ≤ ny') :
    Outside2 base x nx' y ny' m m' := fun p hp hq => h p (by omega) (by omega)

theorem Outside2.word {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : Outside2 base x nx y ny m m')
    {d : Nat} (hx : d + 4 ≤ x ∨ x + nx ≤ d) (hy : d + 4 ≤ y ∨ y + ny ≤ d) (hd : d + 4 ≤ 8192) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

/-- Aligned word stores read back as an update at one byte offset. -/
theorem word_write_aligned (m : Mem) (base : Addr) {d e : Nat} (hd : d + 4 ≤ 8192)
    (he : e + 4 ≤ 8192) (hdm : d % 4 = 0) (hem : e % 4 = 0) (v : BitVec 32) :
    word (m.writeW (off base d) v) base e = if e = d then v else word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, word, Mem.readW_writeW_self32]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.X448.X86
