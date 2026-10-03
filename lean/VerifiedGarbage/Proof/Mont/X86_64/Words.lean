import VerifiedGarbage.Impl.Mont.X86_64
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Montgomery arithmetic on x86-64: words in registers and in the working space

Numbers of several words: in registers (`regsVal`, little-endian over a list
of registers) and in the working space (`wordsVal`), which is `size` bytes at
`base`, the value of `rdi` (`Scr`). The loads and stores of the arithmetic,
and what they leave unchanged.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers `rs` read as a little-endian number. -/
def regsVal (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * regsVal s rs

theorem pow64_succ (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

/-- `x + 2⁶⁴ y < 2⁶⁴ X` for a word `x` and `y < X`. -/
theorem word_add_lt {x y X : Nat} (hx : x < 2 ^ 64) (hy : y < X) : x + 2 ^ 64 * y < 2 ^ 64 * X := by
  have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * X := Nat.mul_le_mul_left _ hy
  rw [Nat.mul_succ] at this
  omega

theorem regsVal_lt (s : State) (rs : List Reg) : regsVal s rs < 2 ^ (64 * rs.length) := by
  induction rs with
  | nil => exact Nat.one_pos
  | cons r rs ih =>
    rw [List.length_cons, pow64_succ]
    exact word_add_lt (s.gpr r).isLt ih

theorem regsVal_append (s : State) (rs qs : List Reg) :
    regsVal s (rs ++ qs) = regsVal s rs + 2 ^ (64 * rs.length) * regsVal s qs := by
  induction rs with
  | nil => simp only [List.nil_append, regsVal, List.length_nil, Nat.mul_zero, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add]
  | cons r rs ih =>
    rw [List.cons_append, regsVal, ih, regsVal, List.length_cons, pow64_succ, Nat.mul_add,
      Nat.mul_assoc]
    omega

theorem regsVal_congr {s s' : State} {rs : List Reg} (h : ∀ r ∈ rs, s'.gpr r = s.gpr r) :
    regsVal s' rs = regsVal s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (off base d) 64

/-- The `k` words at `base + d`, as a little-endian number. -/
def wordsVal (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (word m base d).toNat + 2 ^ 64 * wordsVal m base (d + 8) k

theorem wordsVal_lt (m : Mem) (base : Addr) (d k : Nat) : wordsVal m base d k < 2 ^ (64 * k) := by
  induction k generalizing d with
  | zero => exact Nat.one_pos
  | succ k ih =>
    rw [wordsVal, pow64_succ]
    exact word_add_lt (word m base d).isLt (ih (d + 8))

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = off (s.gpr .rdi) d := by
  simp only [State.ea, sc, BitVec.ofInt_natCast]

theorem Scr.contains {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by have := hs.nowrap; omega)

theorem load_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : s.load64 (s.ea (sc d)) = some (word s.mem base d) := by
  rw [ea_sc, hs.rdi, State.load64, ite_eq_left ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩]

theorem readSrc_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : readSrc s (.mem (sc d)) = some (word s.mem base d) := load_sc hs hd

theorem store_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (v : BitVec 64) :
    s.store64 (s.ea (sc d)) v = some { s with mem := s.mem.writeW (off base d) v } := by
  rw [ea_sc, hs.rdi, State.store64, ite_eq_left ⟨_, hs.wr, hs.contains hd (by decide)⟩]

theorem ld_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩

theorem st_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (off base d) 8 :=
  ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : Keeps rs s s') (hr : .rdi ∉ rs) : Scr s' base size :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

/-! ## Memory outside a range of offsets -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

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

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    ofs base (off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [ofs, off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.wordsVal {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Mont.X86_64.wordsVal m' base d k = VG.Proof.Mont.X86_64.wordsVal m base d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [VG.Proof.Mont.X86_64.wordsVal]
    rw [h.word (by omega) (by omega), ih (by omega) (by omega)]

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

end VG.Proof.Mont.X86_64
