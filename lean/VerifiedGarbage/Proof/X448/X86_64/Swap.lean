import VerifiedGarbage.Proof.X448.X86_64.AddSub

/-!
# X448 on x86-64: the conditional swap

An XOR mask exchanges the words without a branch or an address depending on
the swap bit, word by word (`wp_range_flatMap`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The registers (and regions) of `s'` are those of `s` but for `rs`. -/
def KeepsR (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem KeepsR.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepsR rs s₁ s₂)
    (h₂ : KeepsR rs s₂ s₃) : KeepsR rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Scr.of_keepsR {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : KeepsR rs s s') (hr : .rdi ∉ rs) : Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2 ▸ hs.wr, hs.nowrap⟩

theorem swapStep_ok {s : State} {base : Addr} (hs : Scr s base) {x y i : Nat}
    (hx : x + 56 ≤ 1536) (hy : y + 56 ≤ 1536) (hi : i < 7) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * i))), .mov .rdx (.mem (sc (y + 8 * i))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * i)) .rax, .store (sc (y + 8 * i)) .rdx]) s fun t =>
      t.mem = (s.mem.writeW (off base (x + 8 * i))
        (if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i))).writeW
        (off base (y + 8 * i)) (if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      KeepsR [.rax, .rdx, .r8] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by omega)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by omega)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by omega)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hs.rdi, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

theorem word_write (m : Mem) (base : Addr) {d e : Nat} (hd : d + 8 ≤ 8192) (he : e + 8 ≤ 8192)
    (hde : d + 8 ≤ e ∨ e + 8 ≤ d ∨ e = d) (v : BitVec 64) :
    word (m.writeW (off base d) v) base e = if e = d then v else word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap the seven words under the mask, and nothing else. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : x + 56 ≤ 1536)
    (hy : y + 56 ≤ 1536) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 7, word t.mem base (x + 8 * i) =
        if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i)) ∧
      (∀ i < 7, word t.mem base (y + 8 * i) =
        if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      Outside2 base x 56 y 56 s.mem t.mem ∧ KeepsR [.rax, .rdx, .r8] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (x + 8 * i) =
      if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i)) ∧
    (∀ i < n, word t.mem base (y + 8 * i) =
      if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
    Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ KeepsR [.rax, .rdx, .r8] s t
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * n))), .mov .rdx (.mem (sc (y + 8 * n))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * n)) .rax, .store (sc (y + 8 * n)) .rdx]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .rcx (by decide)).trans hc
    refine WP.mono (swapStep_ok (hs.of_keepsR tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : word t.mem base (x + 8 * n) = word s.mem base (x + 8 * n) :=
      tm.word (by omega) (by omega) (by omega)
    have ey : word t.mem base (y + 8 * n) = word s.mem base (y + 8 * n) :=
      tm.word (by omega) (by omega) (by omega)
    refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, tk.trans uk⟩
    · rw [um, word_write _ _ (by omega) (by omega) (by omega),
        word_write _ _ (by omega) (by omega) (by omega)]
      by_cases h : j = n
      · subst h
        rw [ite_eq_right (by omega), ite_eq_left rfl, ex, ey]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact tx j (by omega)
    · rw [um, word_write _ _ (by omega) (by omega) (by omega)]
      by_cases h : j = n
      · subst h
        rw [ite_eq_left rfl, ex, ey]
      · rw [ite_eq_right (by omega), word_write _ _ (by omega) (by omega) (by omega),
          ite_eq_right (by omega)]
        exact ty j (by omega)
    · intro p hp hq
      rw [um, writeW_outside _ _ _ (by omega : y + 8 * n + 8 < 2 ^ 64) p (by omega),
        writeW_outside _ _ _ (by omega : x + 8 * n + 8 < 2 ^ 64) p (by omega)]
      exact tm p (by omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl⟩⟩

end VG.Proof.X448.X86_64
