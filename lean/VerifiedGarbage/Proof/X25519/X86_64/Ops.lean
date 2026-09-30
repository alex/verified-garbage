import VerifiedGarbage.Proof.X25519.X86_64.Mul

/-!
# X25519 on x86-64: the field operations

Untrusted: everything here is checked by Lean. Each field operation on the
working space (`mul`, `mulSmall`, `add`, `sub`, and `cswap`), as a change of
the field elements `F` it reads and writes: the element at `o` becomes the
result, every byte outside it is unchanged, and so are the registers but
those the arithmetic uses (`Op`).
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The field element at `base + o`, in `GF(p)`. -/
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (fe m base o)

/-- The registers the field arithmetic uses. -/
def clob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A field operation's effect but for its result: the registers but `clob`,
the regions and the memory outside the 32 bytes at `base + o` are unchanged. -/
structure Op (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base o 32 s.mem s'.mem

theorem Op.scr {base : Addr} {o : Nat} {s s' : State} (h : Op base o s s') (hs : Scr s base) :
    Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- A field element's slot: 32 bytes of the working space. -/
abbrev Slot (o : Nat) : Prop := o + 32 ≤ 4096

/-- A field element at another slot is unchanged. -/
theorem Op.fe {base : Addr} {o : Nat} {s s' : State} (h : Op base o s s') {d : Nat}
    (hd : d + 32 ≤ o ∨ o + 32 ≤ d) (hd' : Slot d) : fe s'.mem base d = fe s.mem base d :=
  h.mem.fe hd (by omega)

theorem stores_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun s' =>
      s'.mem = st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 4096 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs.rdi, State.store64,
    w o (by omega), w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ => trivial, trivial, trivial⟩

theorem store4_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o) :
    WP isa (.block (store4 o)) s fun s' =>
      s'.mem = st4 s.mem base o (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  stores_ok hs ho _ _ _ _

theorem zero4_ok (s : State) :
    WP isa (.block zero4) s fun s' =>
      s'.gpr .r8 = 0 ∧ s'.gpr .r9 = 0 ∧ s'.gpr .r10 = 0 ∧ s'.gpr .r11 = 0 ∧
      Keeps [.r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp only [zero4, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem row0 (a b : Nat) : row a b 0 = rowR a b 0 .r8 .r9 .r10 .r11 .r12 := row_eq a b 0
theorem row1 (a b : Nat) : row a b 1 = rowR a b 1 .r9 .r10 .r11 .r12 .r13 := row_eq a b 1
theorem row2 (a b : Nat) : row a b 2 = rowR a b 2 .r10 .r11 .r12 .r13 .r14 := row_eq a b 2
theorem row3 (a b : Nat) : row a b 3 = rowR a b 3 .r11 .r12 .r13 .r14 .r15 := row_eq a b 3

theorem fe_mul_expand (m : Mem) (base : Addr) (a : Nat) (B : Nat) :
    fe m base a * B = (word m base (a + 8 * 0)).toNat * B + 2 ^ 64 * ((word m base (a + 8 * 1)).toNat * B) +
      2 ^ 128 * ((word m base (a + 8 * 2)).toNat * B) + 2 ^ 192 * ((word m base (a + 8 * 3)).toNat * B) := by
  simp only [X86_64.fe, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]
  ring

theorem mul_mod_arith {L H V c AB : Nat} (h₁ : V + 2 ^ 256 * c = L + 38 * H)
    (h₂ : L + 2 ^ 256 * H = AB) : (V + 38 * c) % VG.Spec.X25519.P = AB % VG.Spec.X25519.P := by
  rw [← h₂, fold256, ← h₁, fold256]

/-- `[o] = [a] · [b]`. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [show mul o a b = zero4 ++ (row a b 0 ++ (row a b 1 ++ (row a b 2 ++ (row a b 3 ++
    (reduce ++ store4 o))))) by simp only [mul, List.append_assoc], WP.block_append_iff]
  refine WP.mono (zero4_ok s) fun s₀ ⟨z8, z9, z10, z11, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff, row0]
  refine WP.mono (rowR_ok hs₀ (by omega) hb (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff, row1]
  refine WP.mono (rowR_ok hs₁ (by omega) hb (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff, row2]
  refine WP.mono (rowR_ok hs₂ (by omega) hb (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff, row3]
  refine WP.mono (rowR_ok hs₃ (by omega) hb (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [show reduce ++ store4 o = ([.mov32 .rcx (.imm 38), .mov32 .rbp (.imm 0)] ++
      (mulStep .r8 .rbp .rcx (.reg .r12) ++ (mulStep .r9 .rbp .rcx (.reg .r13) ++
        (mulStep .r10 .rbp .rcx (.reg .r14) ++ mulStep .r11 .rbp .rcx (.reg .r15))))) ++
      (fold ++ store4 o) by simp only [reduce_eq, List.append_assoc], WP.block_append_iff]
  refine WP.mono (reduceSteps_ok s₄) fun s₅ ⟨e5, c5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  have hB : val4 (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11) +
      38 * val4 (s₄.gpr .r12) (s₄.gpr .r13) (s₄.gpr .r14) (s₄.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s₄.gpr .r8).isLt; have := (s₄.gpr .r9).isLt; have := (s₄.gpr .r10).isLt
    have := (s₄.gpr .r11).isLt; have := (s₄.gpr .r12).isLt; have := (s₄.gpr .r13).isLt
    have := (s₄.gpr .r14).isLt; have := (s₄.gpr .r15).isLt
    omega
  have hc : (s₅.gpr .rbp).toNat < 39 := by
    simp only [val4] at e5 hB
    have := (s₅.gpr .r8).isLt; have := (s₅.gpr .r9).isLt; have := (s₅.gpr .r10).isLt
    have := (s₅.gpr .r11).isLt
    omega
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok s₅ c5 (by omega)) fun s₆ ⟨e6, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  refine WP.mono (store4_ok hs₆ ho) fun s₇ ⟨m7, g7, rd7, wr7⟩ => ?_
  -- Memory is only read until the store.
  have M : s₆.mem = s.mem :=
    k6.2.1.trans (k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans (k1.2.1.trans k0.2.1)))))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g7, g k6 r (by simp [h5, h6, h7, h8, h1, h3]), g k5 r (by simp [h5, h6, h7, h8, h1, h3, h2, h4]),
      g k4 r (by simp [h8, h9, h10, h11, h12, h1, h3, h2, h4]),
      g k3 r (by simp [h7, h8, h9, h10, h11, h1, h3, h2, h4]),
      g k2 r (by simp [h6, h7, h8, h9, h10, h1, h3, h2, h4]),
      g k1 r (by simp [h5, h6, h7, h8, h9, h1, h3, h2, h4]), g k0 r (by simp [h5, h6, h7, h8])]
  · rw [rd7, k6.2.2.1, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1, k0.2.2.1]
  · rw [wr7, k6.2.2.2, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2, k0.2.2.2]
  · rw [m7, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m7, fe_st4 _ _ (by omega), e6]
    refine mul_mod_arith e5 ?_
    rw [fe_mul_expand]
    -- Every row read the same memory.
    rw [k0.2.1] at e1
    rw [k1.2.1, k0.2.1] at e2
    rw [k2.2.1, k1.2.1, k0.2.1] at e3
    rw [k3.2.1, k2.2.1, k1.2.1, k0.2.1] at e4
    -- The registers along the way.
    rw [z8, z9, z10, z11] at e1
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have r1 := g k2 .r8 (by decide); have r2 := g k3 .r8 (by decide); have r3 := g k4 .r8 (by decide)
    have q2 := g k3 .r9 (by decide); have q3 := g k4 .r9 (by decide); have q4 := g k4 .r10 (by decide)
    simp only [val4, hz, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e1 e2 e3 e4 ⊢
    rw [r3, r2, r1, q3, q2, q4]
    omega_using [e1, e2, e3, e4]

end VG.Proof.X25519.X86_64
