import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on AArch64: field elements in the working space

Untrusted: everything here is checked by Lean. The working space is 8 KiB at
`base`, which `x0` holds (`Scr`); a field element is the four words at an
offset of it (`fe`), read as an element of `GF(p)` by `F`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The working space: `x0` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) : Prop where
  x0 : s.gpr .x0 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (off base d) 64

/-- The field element at `base + o`: four little-endian words. -/
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat :=
  val4 (word m base o) (word m base (o + 8)) (word m base (o + 16)) (word m base (o + 24))

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem load_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ 8192) (r : Reg) :
    exec (ld r d) s = some (s.write .x r (word s.mem base d)) := by
  rw [ld, exec_ldr_x ⟨ha, by omega⟩]
  · rw [hs.x0]
  · rw [hs.x0]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

theorem store_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ 8192) (r : Reg) :
    exec (st r d) s = some { s with mem := s.mem.writeW (off base d) (s.gpr r) } := by
  rw [st, exec_str_x ⟨ha, by omega⟩]
  · rw [hs.x0]
  · rw [hs.x0]
    exact ⟨_, hs.wr, contains_sc hd⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : Keeps rs s s') (hr : .x0 ∉ rs) : Scr s' base :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Scr.write {s : State} {base : Addr} (hs : Scr s base)
    {r : Reg} (hr : r ≠ .x0) (v : BitVec 64) : Scr (s.write .x r v) base :=
  ⟨(RegUpd.gpr_write_of_ne s .x v (Ne.symm hr)).trans hs.x0, hs.wr, hs.nowrap⟩

theorem Scr.setMem {s : State} {base : Addr} (hs : Scr s base) (m : Mem) :
    Scr { s with mem := m } base := ⟨hs.x0, hs.wr, hs.nowrap⟩

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

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : Outside base o' n' m m' :=
  fun x hx => h x (by omega)

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 32 ≤ o ∨ o + n ≤ d) (hd' : d + 32 < 2 ^ 64) : fe m' base d = fe m base d := by
  simp only [AArch64.fe]
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
  simp only [AArch64.fe, AArch64.word, st4]
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

/-- An aligned field element inside the workspace. -/
def FieldRange (o : Nat) : Prop := o % 8 = 0 ∧ o + 32 ≤ 8192

theorem stores_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : FieldRange o)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun s' =>
      s' = { s with mem := st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) } := by
  obtain ⟨ha, hb⟩ := ho
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil,
    store_sc hs ha (by omega),
    store_sc (hs.setMem _) (show (o + 8) % 8 = 0 by omega) (by omega),
    store_sc (hs.setMem _) (show (o + 16) % 8 = 0 by omega) (by omega),
    store_sc (hs.setMem _) (show (o + 24) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left']
  rfl

theorem store4_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : FieldRange o) :
    WP isa (.block (store4 o)) s fun s' =>
      s' = { s with mem := st4 s.mem base o (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := stores_ok hs ho _ _ _ _

theorem ld_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ 8192) (r : Reg) :
    WP isa (.block [ld r d]) s fun s' =>
      s'.gpr r = word s.mem base d ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, load_sc hs ha hd,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · exact (RegUpd.gpr_write_self s .x r _).trans (BitVec.setWidth_eq _)
  · intro r' hr
    exact RegUpd.gpr_write_of_ne s .x _ (by simpa only [List.mem_singleton] using hr)

theorem loads_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : FieldRange o)
    {a b c d : Reg} (hd : ([a, b, c, d, .x0] : List Reg).Nodup) :
    WP isa (.block (loads o a b c d)) s fun t =>
      t.gpr a = word s.mem base o ∧ t.gpr b = word s.mem base (o + 8) ∧
      t.gpr c = word s.mem base (o + 16) ∧ t.gpr d = word s.mem base (o + 24) ∧
      Keeps [a, b, c, d] s t := by
  obtain ⟨halign, hbound⟩ := ho
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hac, had, ha0⟩, ⟨hbc, hbd, hb0⟩, ⟨hcd, hc0⟩, ⟨hd0, _⟩⟩ := hd
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil,
    load_sc hs halign (by omega),
    load_sc (hs.write ha0 _) (show (o + 8) % 8 = 0 by omega) (by omega),
    load_sc ((hs.write ha0 _).write hb0 _) (show (o + 16) % 8 = 0 by omega) (by omega),
    load_sc (((hs.write ha0 _).write hb0 _).write hc0 _) (show (o + 24) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, had, hac, hab, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, hbd, hbc, ite_false, ite_true, BitVec.setWidth_eq, RegUpd.mem_write]
  · simp only [RegUpd.gpr_write, hcd, ite_false, ite_true, BitVec.setWidth_eq, RegUpd.mem_write]
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.mem_write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem read_byte (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem Outside.writeW {base : Addr} {o n d : Nat} {m m' : Mem} (h : Outside base o n m m')
    (h₁ : o ≤ d) (h₂ : d + 8 ≤ o + n) (h₃ : o + n < 2 ^ 64) (v : BitVec 64) :
    Outside base o n m (m'.writeW (off base d) v) :=
  h.trans ((writeW_outside m' base v (by omega)).mono h₁ h₂)

theorem word_writeW_sep (m : Mem) (base : Addr) {d e : Nat} (v : BitVec 64)
    (h : e + 8 ≤ d ∨ d + 8 ≤ e) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    word (m.writeW (off base d) v) base e = word m base e :=
  Mem.readW_writeW_sep (sep_off base h he hd) (by decide)

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 m _ v

theorem write64_eq_writeW (m : Mem) (a : Addr) (v : BitVec 64) :
    m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

end VG.Proof.Ed25519.AArch64
