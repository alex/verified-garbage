import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on x86-64: field elements in the working space

The working space is 4 KiB at `base`, which `rdi` holds (`Scr`); a field
element is the four words at an offset of it (`fe`), read as an element of
`GF(p)` by `F`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, 4096⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 4096 ≤ 2 ^ 64

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (off base d) 64

/-- The field element at `base + o`: four little-endian words. -/
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat :=
  val4 (word m base o) (word m base (o + 8)) (word m base (o + 16)) (word m base (o + 24))

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = off (s.gpr .rdi) d := by
  simp only [State.ea, sc, at_, BitVec.ofInt_natCast]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 4096) :
    (⟨base, 4096⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem load_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    s.load64 (s.ea (sc d)) = some (word s.mem base d) := by
  rw [ea_sc, hs.rdi, State.load64, ite_eq_left ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩]

theorem readSrc_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    readSrc s (.mem (sc d)) = some (word s.mem base d) := load_sc hs hd

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : Keeps rs s s') (hr : .rdi ∉ rs) : Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

/-! ## Stores and frames -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    ofs base (off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [ofs, off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Outside base o n m₁ m₂)
    (h₂ : Outside base o n m₂ m₃) : Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 32 ≤ o ∨ o + n ≤ d) (hd' : d + 32 < 2 ^ 64) : fe m' base d = fe m base d := by
  simp only [X86_64.fe]
  rw [h.word (by omega) (by omega), h.word (by omega) (by omega), h.word (by omega) (by omega),
    h.word (by omega) (by omega)]

/-- Four words stored at `base + o`. -/
def st4 (m : Mem) (base : Addr) (o : Nat) (w0 w1 w2 w3 : BitVec 64) : Mem :=
  (((m.writeW (off base o) w0).writeW (off base (o + 8)) w1).writeW (off base (o + 16)) w2).writeW
    (off base (o + 24)) w3

theorem sep_off (base : Addr) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : Mem.Sep (off base d) (64 / 8) (off base e) (64 / 8) :=
  Offset.sep base h hd he

theorem fe_st4 (m : Mem) (base : Addr) {o : Nat} (ho : o + 32 < 2 ^ 64) (w0 w1 w2 w3 : BitVec 64) :
    fe (st4 m base o w0 w1 w2 w3) base o = val4 w0 w1 w2 w3 := by
  simp only [X86_64.fe, X86_64.word, st4]
  rw [Mem.readW_writeW_sep (sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64]

theorem write_outside (m : Mem) (base : Addr) {d o : Nat} (v : BitVec 64) (h1 : o ≤ d)
    (h2 : d + 8 ≤ o + 32) (h3 : o + 32 < 2 ^ 64) {x : Addr}
    (hx : ofs base x < o ∨ o + 32 ≤ ofs base x) : (m.writeW (off base d) v) x = m x := by
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 < 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem st4_outside (m : Mem) (base : Addr) {o : Nat} (ho : o + 32 < 2 ^ 64) (w0 w1 w2 w3 : BitVec 64) :
    Outside base o 32 m (st4 m base o w0 w1 w2 w3) := by
  intro x hx
  simp only [st4]
  rw [write_outside _ _ _ (by omega) (by omega) ho hx, write_outside _ _ _ (by omega) (by omega) ho hx,
    write_outside _ _ _ (by omega) (by omega) ho hx, write_outside _ _ _ (by omega) (by omega) ho hx]

end VG.Proof.X25519.X86_64
