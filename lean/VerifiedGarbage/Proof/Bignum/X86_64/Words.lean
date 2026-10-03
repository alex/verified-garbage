import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Multiword arithmetic on x86-64: words in the working space

The working space is `size` bytes at `base` (`Scr`), writable and not
wrapping around. A number of `n` words at byte offset `d` of it is
`wv m base d n`, little-endian. The arrays' words are addressed as
`[b + 8 i + disp]` with a base `b = base + e` and an index `i` in registers
(`ea_ix`).

`Outside base o n m m'`: `m'` agrees with `m` but on the bytes at offsets
`[o, o + n)` of `base`, so a number elsewhere keeps its value
(`Outside.wv`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (load64_eq store64_eq)

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The word at `p + d`. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : BitVec 64 := m.readW (off p d) 64

/-- The `n` words at `p + d`, little-endian. -/
def wv (m : Mem) (p : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wv m p d n + 2 ^ (64 * n) * (word m p (d + 8 * n)).toNat

theorem pow64_succ (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem wv_lt (m : Mem) (p : Addr) (d n : Nat) : wv m p d n < 2 ^ (64 * n) := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [wv, pow64_succ]
    have hw := (word m p (d + 8 * n)).isLt
    have : 2 ^ (64 * n) * (word m p (d + 8 * n)).toNat ≤ 2 ^ (64 * n) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega

theorem wv_congr {m m' : Mem} {p : Addr} {d n : Nat}
    (h : ∀ i < n, word m' p (d + 8 * i) = word m p (d + 8 * i)) : wv m' p d n = wv m p d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wv]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

/-- A number of `n + k` words is its low `n` words and its high `k` words. -/
theorem wv_add (m : Mem) (p : Addr) (d n k : Nat) :
    wv m p d (n + k) = wv m p d n + 2 ^ (64 * n) * wv m p (d + 8 * n) k := by
  induction k with
  | zero => simp [wv]
  | succ k ih =>
    rw [← Nat.add_assoc, wv, ih, wv, show 64 * (n + k) = 64 * n + 64 * k by omega, Nat.pow_add,
      show d + 8 * (n + k) = d + 8 * n + 8 * k by omega, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- A number is zero iff its words are. -/
theorem wv_eq_zero_iff (m : Mem) (p : Addr) (d n : Nat) :
    wv m p d n = 0 ↔ ∀ q < n, word m p (d + 8 * q) = 0 := by
  induction n with
  | zero => simp [wv]
  | succ n ih =>
    rw [wv]
    constructor
    · intro h q hq
      have h1 : wv m p d n = 0 := by omega
      have h2 : 2 ^ (64 * n) * (word m p (d + 8 * n)).toNat = 0 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
      · exact ih.mp h1 q hq
      · subst hq
        rcases Nat.mul_eq_zero.mp h2 with h | h
        · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos _))
        · exact BitVec.eq_of_toNat_eq h
    · intro h
      rw [ih.mpr fun q hq => h q (by omega), h n (by omega)]
      rfl

/-- A number whose words but word `i` are zero. -/
theorem wv_single (m : Mem) (p : Addr) (d : Nat) {i : Nat} :
    ∀ n, i < n → (∀ q < n, q ≠ i → word m p (d + 8 * q) = 0) →
      wv m p d n = (word m p (d + 8 * i)).toNat * 2 ^ (64 * i)
  | 0, hi, _ => absurd hi (by omega)
  | n + 1, hi, h => by
    rw [wv]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [wv_single m p d n hi fun q hq hne => h q (by omega) hne, h n (by omega) (by omega)]
      simp
    · subst hi
      rw [(wv_eq_zero_iff m p d i).mpr fun q hq => h q (by omega) (by omega), Nat.zero_add, Nat.mul_comm]

/-! ## The working space -/

/-- The working space: `size` bytes at `base`, writable, not wrapping
around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64

theorem Scr.contains {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by have := hs.nowrap; omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (off base d) 8 :=
  ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.st8 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 1 ≤ size) : InRegions s.wr (off base d) 1 :=
  ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.congr {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : s'.wr = s.wr) : Scr s' base size :=
  ⟨h ▸ hs.wr, hs.nowrap⟩

/-! ## Addresses -/

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem ofNat_mul8 (j : Nat) : BitVec.ofNat 64 j * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * j) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem ofInt_ofNat (d : Nat) : BitVec.ofInt 64 (Int.ofNat d) = BitVec.ofNat 64 d := by
  rw [Int.ofNat_eq_natCast, BitVec.ofInt_natCast]

/-- `[b + 8 i + d]` for `b = p + e` and `i = j`. -/
theorem ea_ix (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (d : Nat) :
    s.ea (ix b i (Int.ofNat d)) = off p (e + 8 * j + d) := by
  simp only [State.ea, ix, hb, hi, off, ofInt_ofNat, ofNat_mul8, BitVec.add_assoc, BitVec.ofNat_add]

theorem ea_ix0 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) : s.ea (ix b i) = off p (e + 8 * j) := by
  have := ea_ix s hb hi 0
  rwa [Nat.add_zero] at this

theorem ea_ix8 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) : s.ea (ix b i 8) = off p (e + 8 * j + 8) :=
  ea_ix s hb hi 8

/-- `[b + 8 i - 8]` for `b = p + e` and `i = j ≥ 1`. -/
theorem ea_ixm8 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (hj : 1 ≤ j) :
    s.ea (ix b i (-8)) = off p (e + 8 * (j - 1)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (8 * (j - 1)) := by
    rw [show (-8 : Int) = - ((8 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 1) + 8 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  simp only [State.ea, ix, hb, hi, off, ofNat_mul8, BitVec.add_assoc, h8, BitVec.ofNat_add]

theorem ea_at0 (s : State) {b : Reg} {p : Addr} {e : Nat} (hb : s.gpr b = off p e) :
    s.ea (at0 b) = off p e := by
  simp only [State.ea, at0, hb, BitVec.ofInt_ofNat, BitVec.add_zero]

theorem ea_hdr (s : State) {p : Addr} (hb : s.gpr .rdi = p) (i : Nat) :
    s.ea (hdr i) = off p (8 * i) := by
  simp only [State.ea, hdr, hb, off]
  rw [show (8 * (i : Int)) = ((8 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]

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

theorem Outside.wv {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    wv m' base d k = wv m base d k :=
  wv_congr fun i hi => h.word (by omega) (by omega)

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 m _ v

/-- Writing word `n` of a number of `n + 1` words. -/
theorem wv_writeW_top (m : Mem) (base : Addr) (d n : Nat) (v : BitVec 64) (h : d + 8 * n + 8 ≤ 2 ^ 64) :
    wv (m.writeW (off base (d + 8 * n)) v) base d (n + 1) = wv m base d n + 2 ^ (64 * n) * v.toNat := by
  rw [wv, word_writeW_self, (writeW_outside m base v (by omega)).wv (Or.inl (Nat.le_refl _)) (by omega)]

end VG.Proof.Bignum.X86_64
