import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.X448.Invert

/-!
# X448 on x86-64: the inversion

The inversion `invert` writes only the temporaries `T0`–`T7` (slots 14–21)
and the product's words (bytes `[960, 1648)`) and, in its runs of squarings,
the counter `rbx`; slot 21 (`T7`) ends as `VG.Proof.X448.invert` of slot 2
(`Z2`). Each part of it is an `ISpec`: a change of the slots by a function of
them, keeping everything else.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

/-- What the inversion keeps: the registers but `clob` and `rbx`, the regions,
and the memory outside `[960, 1648)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 960 688 s.mem s'.mem

theorem IKeep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : IKeep base s₁ s₂)
    (h₂ : IKeep base s₂ s₃) : IKeep base s₁ s₃ :=
  ⟨fun r hr hb => (h₂.gpr r hr hb).trans (h₁.gpr r hr hb), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem IKeep.scr {base : Addr} {s s' : State} (h : IKeep base s s') (hs : Scr s base) :
    Scr s' base :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `c` changes the slots by `f`, and keeps everything else (`IKeep`). -/
def ISpec (base : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base → WP isa c s fun s' => IKeep base s s' ∧ E s'.mem base = f (E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env} (h₁ : ISpec base c₁ f)
    (h₂ : ISpec base c₂ g) : ISpec base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem ISpec.append {base : Addr} {l₁ l₂ : List Instr} {f g : Env → Env}
    (h₁ : ISpec base (.block l₁) f) (h₂ : ISpec base (.block l₂) g) :
    ISpec base (.block (l₁ ++ l₂)) fun e => g (f e) := fun s hs => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩

/-- A slot of the inversion's: 14 to 21. -/
abbrev ISlot (o : Index) : Prop := 14 ≤ o.val

theorem islot_out {base : Addr} {o : Index} (ho : ISlot o) {m m' : Mem}
    (h : Outside2 base (slot o.val) 56 ACC 112 m m') : Outside base 960 688 m m' :=
  h.outside (by simp only [slot]; omega) (by have := slot_lt o; simp only [ACC] at *; omega)
    (by decide) (by decide)

variable {fld : Field} (hf : FieldOk fld)

include hf in
/-- A multiplication into a slot of the inversion's, which also keeps `rbx`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : Scr s base) (o a b : Index) (ho : ISlot o) :
    WP isa (.block (fld.mul (slot o.val) (slot a.val) (slot b.val))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ E s'.mem base = opMul o a b (E s.mem base) :=
  WP.mono (hf.mul hs (slot_lt o) (slot_lt a) (slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, islot_out ho h.mem⟩,
      h.gpr _ (by decide), by rw [E_update h.mem, e]; rfl⟩

include hf in
/-- A square into a slot of the inversion's, which also keeps `rbx`. -/
theorem sqrI_ok {s : State} {base : Addr} (hs : Scr s base) (o a : Index) (ho : ISlot o) :
    WP isa (.block (fld.sqr (slot o.val) (slot a.val))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ E s'.mem base = opMul o a a (E s.mem base) :=
  WP.mono (hf.sqr hs (slot_lt o) (slot_lt a)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, islot_out ho h.mem⟩,
      h.gpr _ (by decide), by rw [E_update h.mem, e]; rfl⟩

include hf in
theorem mulI (base : Addr) (o a b : Index) (ho : ISlot o) :
    ISpec base (.block (fld.mul (slot o.val) (slot a.val) (slot b.val))) (opMul o a b) :=
  fun _ hs => WP.mono (mulI_ok hf hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

include hf in
theorem sqrI (base : Addr) (o a : Index) (ho : ISlot o) :
    ISpec base (.block (fld.sqr (slot o.val) (slot a.val))) (opMul o a a) :=
  fun _ hs => WP.mono (sqrI_ok hf hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-! ## Runs of squarings -/

/-- `rbx = k`. -/
theorem setRbx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 k))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- `rbx -= 1`, from `rbx = k + 1`: the flag `ZF` says whether `k = 0`. -/
theorem decRbx_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k = 0)) := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zf : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb', RegUpd.gpr_setReg_self, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, zf]
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false,
    RegUpd.gpr_arithFlags], trivial, trivial, trivial, trivial⟩

/-- Slot `o` becomes slot `a` squared `n` times. -/
def opSqn (o a : Index) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Index) (e : Env) (v : Spec.X448.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

include hf in
/-- The loop of `sqn`, with the counter `rbx = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scr s₀ base) (o : Index) (ho : ISlot o)
    (x : Spec.X448.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → IKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      E s.mem base = Function.update (E s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (fld.sqr (slot o.val) (slot o.val) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun s' =>
        IKeep base s₀ s' ∧ E s'.mem base = Function.update (E s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ IKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧
    E s.mem base = Function.update (E s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (sqrI_ok hf (hk.scr hs₀) o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
  refine WP.mono (decRbx_ok (by omega) (b1.trans hb)) fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : IKeep base s₀ s2 := hk.trans (k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have e2 : E s2.mem base = Function.update (E s₀.mem base) o (sqn x (n - m)) := by
    rw [m2, e1, he, opMul_update]
    congr 2
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, k2, b2, e2⟩

include hf in
/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : Index) (ho : ISlot o) (n : Nat) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 32) :
    ISpec base (Impl.X448.X86_64.sqn fld (slot o.val) (slot a.val) n) (opSqn o a n) := by
  intro s hs
  rw [Impl.X448.X86_64.sqn]
  by_cases h1 : n = 1
  · subst h1
    rw [ite_eq_left rfl]
    exact WP.mono (sqrI_ok hf hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, by rw [e]; rfl⟩
  rw [ite_eq_right h1]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrI_ok hf hs o a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (setRbx_ok s1 (n - 1) (by omega)) fun s2 ⟨b2, g2, m2, rd2, wr2⟩ => ?_
  have k2 : IKeep base s s2 := k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩
  refine sqLoop_ok hf hs o ho (E s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [m2, e1, show n - (n - 1) = 1 by omega]
  rfl

/-! ## The inversion -/

/-- The slots after the inversion. -/
def invEnv (e : Env) : Env :=
  opMul 21 21 20 (opMul 20 20 2 (opSqn 20 20 2 (opSqn 21 21 225 (opMul 21 21 2 (opSqn 21 20 1
    (opMul 20 20 14 (opSqn 20 20 2 (opMul 20 20 15 (opSqn 20 20 4 (opMul 20 20 16 (opSqn 20 20 8
    (opMul 20 20 17 (opSqn 20 20 16 (opMul 20 20 19 (opSqn 20 20 64 (opMul 20 20 19 (opSqn 20 19 64
    (opMul 19 19 18 (opSqn 19 18 32 (opMul 18 18 17 (opSqn 18 17 16 (opMul 17 17 16 (opSqn 17 16 8
    (opMul 16 16 15 (opSqn 16 15 4 (opMul 15 15 14 (opSqn 15 14 2 (opMul 14 14 2
    (opSqn 14 2 1 e)))))))))))))))))))))))))))))

include hf in
theorem invert_spec (base : Addr) : ISpec base (Impl.X448.X86_64.invert fld) invEnv := by
  have h : ISpec base _ _ :=
    (sqnI hf base 14 2 (by decide) 1 (by decide) (by decide)).seq <|
    (mulI hf base 14 14 2 (by decide)).seq <|
    (sqnI hf base 15 14 (by decide) 2 (by decide) (by decide)).seq <|
    (mulI hf base 15 15 14 (by decide)).seq <|
    (sqnI hf base 16 15 (by decide) 4 (by decide) (by decide)).seq <|
    (mulI hf base 16 16 15 (by decide)).seq <|
    (sqnI hf base 17 16 (by decide) 8 (by decide) (by decide)).seq <|
    (mulI hf base 17 17 16 (by decide)).seq <|
    (sqnI hf base 18 17 (by decide) 16 (by decide) (by decide)).seq <|
    (mulI hf base 18 18 17 (by decide)).seq <|
    (sqnI hf base 19 18 (by decide) 32 (by decide) (by decide)).seq <|
    (mulI hf base 19 19 18 (by decide)).seq <|
    (sqnI hf base 20 19 (by decide) 64 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 19 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 64 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 19 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 16 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 17 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 8 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 16 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 4 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 15 (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 2 (by decide) (by decide)).seq <|
    (mulI hf base 20 20 14 (by decide)).seq <|
    (sqnI hf base 21 20 (by decide) 1 (by decide) (by decide)).seq <|
    (mulI hf base 21 21 2 (by decide)).seq <|
    (sqnI hf base 21 21 (by decide) 225 (by decide) (by decide)).seq <|
    (sqnI hf base 20 20 (by decide) 2 (by decide) (by decide)).seq
    ((mulI hf base 20 20 2 (by decide)).append (mulI hf base 21 21 20 (by decide)))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 21 = VG.Proof.X448.invert (e 2) := by
  simp (config := {decide := true}) only [invEnv, opMul, opSqn, Function.update_apply]
  rfl

include hf in
theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (Impl.X448.X86_64.invert fld) s fun s' =>
      (∀ r, r ∉ clob → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 960 688 s.mem s'.mem ∧
      E s'.mem base 21 = VG.Proof.X448.invert (E s.mem base 2) :=
  WP.mono (invert_spec hf base s hs) fun _ ⟨k, e⟩ =>
    ⟨k.gpr, k.rd, k.wr, k.mem, by rw [e, invEnv_eval]⟩

end VG.Proof.X448.X86_64
