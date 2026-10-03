import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-!
# Memory unchanged outside a list of ranges

`Unch base W m m'`: `m'` agrees with `m` but at the offsets of `base` in the
ranges `W` (offset, length). Code made of parts that each change some ranges
changes their union (`Unch.trans`); a number or a byte apart from all of them
is unchanged (`Unch.wordsVal`, `Unch.byte`), and so is memory beyond them
(`Unch.far`), such as the arguments and the result, outside the working space.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Proof.Mont.X86_64

/-- `m'` agrees with `m` but at offsets of `base` in the ranges `W`. -/
def Unch (base : Addr) (W : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ w ∈ W, ofs base x < w.1 ∨ w.1 + w.2 ≤ ofs base x) → m' x = m x

theorem Unch.refl (base : Addr) (W : List (Nat × Nat)) (m : Mem) : Unch base W m m :=
  fun _ _ => rfl

theorem Unch.trans {base : Addr} {W W' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem}
    (h₁ : Unch base W m₁ m₂) (h₂ : Unch base W' m₂ m₃) : Unch base (W ++ W') m₁ m₃ :=
  fun x hx => (h₂ x fun w hw => hx w (List.mem_append_right _ hw)).trans
    (h₁ x fun w hw => hx w (List.mem_append_left _ hw))

theorem Unch.mono {base : Addr} {W W' : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w ∈ W') : Unch base W' m m' :=
  fun x hx => h x fun w hw => hx w (hW w hw)

theorem _root_.VG.Proof.Mont.X86_64.Outside.unch {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') :
    Unch base [(o, n)] m m' :=
  fun x hx => h x (hx _ (List.mem_singleton_self _))

theorem _root_.VG.Proof.Mont.X86_64.OpKeep.unch {M : Mod} {base : Addr} {o : Nat} {s s' : State} (h : OpKeep M base o s s') :
    Unch base [(o, 8 * M.n), (M.tmp, 8 * M.n)] s.mem s'.mem :=
  fun x hx => h.mem x (hx _ (List.mem_cons_self ..)) (hx (M.tmp, 8 * M.n) (by simp))

theorem _root_.VG.Proof.Mont.X86_64.OpKeep.scr {M : Mod} {base : Addr} {o size : Nat} {s s' : State} (h : OpKeep M base o s s')
    (hs : Scr s base size) : Scr s' base size :=
  ⟨(h.gpr _ (rdi_not_clob _)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem ProgKeep.unch {M : Mod} {base : Addr} {W : List Nat} {s s' : State}
    (h : ProgKeep M base W s s') :
    Unch base (W.map (·, 8 * M.n) ++ [(M.tmp, 8 * M.n)]) s.mem s'.mem :=
  fun x hx => h.mem x (fun _ hw => hx _ (List.mem_append_left _ (List.mem_map_of_mem hw)))
    (hx _ (List.mem_append_right _ (List.mem_singleton_self _)))

theorem Unch.outside {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {o n : Nat} (hW : ∀ w ∈ W, o ≤ w.1 ∧ w.1 + w.2 ≤ o + n) : Outside base o n m m' :=
  fun x hx => h x fun w hw => by have := hW w hw; omega

/-- A word apart from the ranges. -/
theorem Unch.word {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : ∀ w ∈ W, d + 8 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ fun w hw' => by
    rw [ofs_off base (by omega)]; have := hd w hw'; omega).symm).symm

/-- A number apart from the ranges. -/
theorem Unch.wordsVal {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d k : Nat} (hd : ∀ w ∈ W, d + 8 * k ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Mont.X86_64.wordsVal m' base d k = VG.Proof.Mont.X86_64.wordsVal m base d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [VG.Proof.Mont.X86_64.wordsVal]
    rw [h.word (fun w hw => by have := hd w hw; omega) (by omega),
      ih (fun w hw => by have := hd w hw; omega) (by omega)]

/-- A byte apart from the ranges. -/
theorem Unch.byte {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : ∀ w ∈ W, d + 1 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d < 2 ^ 64) :
    m' (off base d) = m (off base d) :=
  h _ fun w hw => by
    have e : ofs base (off base d) = d := by
      have := ofs_off base (d := d) (i := 0) (by omega)
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] using this
    rw [e]; have := hd w hw; omega

/-- Memory beyond every range. -/
theorem Unch.far {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {x : Addr} (hx : ∀ w ∈ W, w.1 + w.2 ≤ ofs base x) : m' x = m x :=
  h x fun w hw => Or.inr (hx w hw)

end VG.Proof.Weierstrass.X86_64
