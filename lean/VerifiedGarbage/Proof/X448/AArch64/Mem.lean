import VerifiedGarbage.Impl.X448.AArch64
import VerifiedGarbage.Proof.X448.Limbs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X448 on AArch64: the working space

Untrusted: everything here is checked by Lean. Field elements occupy sixteen
words of the 8 KiB working space. `Outside` tracks the bytes a block changes;
`Keeps` tracks its registers and memory permissions independently.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (off base d) 64
abbrev limbs (m : Mem) (base : Addr) (o : Nat) (i : Nat) : Nat := (word m base (o + 8 * i)).toNat
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := valN (limbs m base o) 16

def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 16, limbs m base o i < radix

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
  x3 : s.gpr .x3 = base
  mask : s.gpr .x12 = 0x0fffffff
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : Keeps rs s s') (hr : .x3 ∉ rs ∧ .x12 ∉ rs) : Scr s' base :=
  ⟨(h.1 _ hr.1).trans hs.x3, (h.1 _ hr.2).trans hs.mask, h.2.2 ▸ hs.wr, hs.nowrap⟩

theorem addr_word (s : State) (r : Reg) {d : Nat} (hd : d + 8 ≤ 8192) (ha : d % 8 = 0) :
    addr s 8 r d = some (off (s.gpr r) d) := by
  rw [addr, ite_eq_left ⟨ha, by omega⟩]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (off base d) n := ⟨_, hs.wr, contains_sc hd⟩

theorem load_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    s.load (off base d) 8 = some (word s.mem base d) := by
  rw [State.load, ite_eq_left (hs.read hd)]
  rfl

theorem read1_eq (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p : BitVec (0 + 8)) = m p
  exact BitVec.zero_width_append _ _

theorem read8_eq (m : Mem) (p : Addr) : m.read p 8 = m.readW p 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write8_eq (m : Mem) (p : Addr) (v : BitVec 64) : m.write p 8 v = m.writeW p v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

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
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 8192) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.limbs {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + n ≤ d) (hd' : d + 128 ≤ 8192) {i : Nat} (hi : i < 16) :
    limbs m' base d i = limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + n ≤ d) (hd' : d + 128 ≤ 8192) : fe m' base d = fe m base d :=
  valN_congr fun _ hi => h.limbs hd hd' hi

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 8192) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem word_write (m : Mem) (base : Addr) {o i j : Nat} (ho : o + 8 * (i + 1) ≤ 8192)
    (hj : o + 8 * (j + 1) ≤ 8192) (v : BitVec 64) :
    word (m.writeW (off base (o + 8 * i)) v) base (o + 8 * j) =
      if j = i then v else word m base (o + 8 * j) := by
  by_cases h : j = i
  · rw [ite_eq_left h, h, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- A field operation writes its result and its temporary coefficients. -/
def FieldMem (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + 128 ≤ ofs base x) →
    (ofs base x < ACC ∨ ACC + 512 ≤ ofs base x) → m' x = m x

theorem FieldMem.refl (base : Addr) (o : Nat) (m : Mem) : FieldMem base o m m := fun _ _ _ => rfl

theorem FieldMem.trans {base : Addr} {o : Nat} {m₁ m₂ m₃ : Mem} (h₁ : FieldMem base o m₁ m₂)
    (h₂ : FieldMem base o m₂ m₃) : FieldMem base o m₁ m₃ :=
  fun x hx hw => (h₂ x hx hw).trans (h₁ x hx hw)

theorem FieldMem.output {base : Addr} {o : Nat} {m m' : Mem} (h : Outside base o 128 m m') :
    FieldMem base o m m' := fun x hx _ => h x hx

theorem FieldMem.work {base : Addr} {o d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hl : ACC ≤ d) (hr : d + n ≤ ACC + 512) : FieldMem base o m m' :=
  fun x _ hx => h.mono hl hr x hx

theorem FieldMem.word {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + 128 ≤ d) (hw : d + 8 ≤ ACC) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by simp only [ACC] at hw; omega)]; omega)
    (Or.inl (by rw [ofs_off base (by simp only [ACC] at hw; omega)]; omega))).symm).symm

theorem FieldMem.limbs {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ ACC) {i : Nat} (hi : i < 16) :
    limbs m' base d i = limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem FieldMem.fe {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ ACC) : fe m' base d = fe m base d :=
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
    {d : Nat} (hx : d + 8 ≤ x ∨ x + nx ≤ d) (hy : d + 8 ≤ y ∨ y + ny ≤ d) (hd : d + 8 ≤ 8192) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

/-- Aligned word stores read back as an update at one byte offset. -/
theorem word_write_aligned (m : Mem) (base : Addr) {d e : Nat} (hd : d + 8 ≤ 8192)
    (he : e + 8 ≤ 8192) (hdm : d % 8 = 0) (hem : e % 8 = 0) (v : BitVec 64) :
    word (m.writeW (off base d) v) base e = if e = d then v else word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.X448.AArch64
