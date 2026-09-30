import VerifiedGarbage.Proof.X25519.X86_64.Env
import VerifiedGarbage.Proof.X25519.Invert

/-!
# X25519 on x86-64: the inversion

Untrusted: everything here is checked by Lean. The inversion `invert` writes
only the temporaries `T0`–`T3` (slots 16–19, bytes `[512, 640)`) and, in its
runs of squarings, the counter `rbx`; slot 17 (`T1`) ends as
`VG.Proof.X25519.invert` of slot 4 (`Z2`). Each part of it is an `ISpec`: a
change of the slots by a function of them, keeping everything else.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- What the inversion keeps: the registers but `clob` and `rbx`, the regions,
and the memory outside `[512, 640)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 512 128 s.mem s'.mem

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

/-- A slot of the inversion's: 16 to 19. -/
abbrev ISlot (o : Fin 128) : Prop := 16 ≤ o.val ∧ o.val < 20

/-- A multiplication into a slot of the inversion's, which also keeps `rbx`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : ISlot o) :
    WP isa (.block (mul (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ E s'.mem base = opMul o a b (E s.mem base) :=
  WP.mono (mul_ok hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.mem.mono (by omega) (by omega)⟩,
      h.gpr _ (by decide), by rw [E_update h.mem, e]; rfl⟩

theorem mulI (base : Addr) (o a b : Fin 128) (ho : ISlot o) :
    ISpec base (.block (mul (32 * o.val) (32 * a.val) (32 * b.val))) (opMul o a b) := fun _ hs =>
  WP.mono (mulI_ok hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

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
def opSqn (o a : Fin 128) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Fin 128) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

/-- The loop of `sqn`, with the counter `rbx = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scr s₀ base) (o : Fin 128) (ho : ISlot o)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → IKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      E s.mem base = Function.update (E s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (mul (32 * o.val) (32 * o.val) (32 * o.val) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun s' =>
        IKeep base s₀ s' ∧ E s'.mem base = Function.update (E s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ IKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧
    E s.mem base = Function.update (E s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (mulI_ok (hk.scr hs₀) o o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
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

/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : Fin 128) (ho : ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    ISpec base (Impl.X25519.X86_64.sqn (32 * o.val) (32 * a.val) n) (opSqn o a n) := by
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulI_ok hs o a a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (setRbx_ok s1 (n - 1) (by omega)) fun s2 ⟨b2, g2, m2, rd2, wr2⟩ => ?_
  have k2 : IKeep base s s2 := k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩
  refine sqLoop_ok hs o ho (E s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [m2, e1, show n - (n - 1) = 1 by omega]
  rfl

/-! ## The inversion -/

/-- The slots after the inversion. -/
def invEnv (e : Env) : Env :=
  opMul 17 17 16 (opSqn 17 17 5 (opMul 17 18 17 (opSqn 18 18 50 (opMul 18 19 18 (opSqn 19 18 100
    (opMul 18 18 17 (opSqn 18 17 50 (opMul 17 18 17 (opSqn 18 18 10 (opMul 18 19 18 (opSqn 19 18 20
    (opMul 18 18 17 (opSqn 18 17 10 (opMul 17 18 17 (opSqn 18 17 5 (opMul 17 17 18
    (opMul 18 16 16 (opMul 16 16 17 (opMul 17 4 17 (opMul 17 17 17 (opMul 17 16 16
    (opMul 16 4 4 e))))))))))))))))))))))

theorem invert_spec (base : Addr) : ISpec base Impl.X25519.X86_64.invert invEnv := by
  have h : ISpec base _ _ :=
    (mulI base 16 4 4 ⟨by decide, by decide⟩).seq <|
    ((mulI base 17 16 16 ⟨by decide, by decide⟩).append
      (mulI base 17 17 17 ⟨by decide, by decide⟩)).seq <|
    ((((mulI base 17 4 17 ⟨by decide, by decide⟩).append
      (mulI base 16 16 17 ⟨by decide, by decide⟩)).append
      (mulI base 18 16 16 ⟨by decide, by decide⟩)).append
      (mulI base 17 17 18 ⟨by decide, by decide⟩)).seq <|
    (sqnI base 18 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 17 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 19 18 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 18 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 17 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 18 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 19 18 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI base 18 19 18 ⟨by decide, by decide⟩).seq <|
    (sqnI base 18 18 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 17 18 17 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 17 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (mulI base 17 17 16 ⟨by decide, by decide⟩)
  exact h

theorem invEnv_eval (e : Env) : invEnv e 17 = VG.Proof.X25519.invert (e 4) := by
  simp (config := {decide := true}) only [invEnv, opMul, opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa Impl.X25519.X86_64.invert s fun s' =>
      (∀ r, r ∉ clob → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 512 128 s.mem s'.mem ∧
      E s'.mem base 17 = VG.Proof.X25519.invert (E s.mem base 4) :=
  WP.mono (invert_spec base s hs) fun _ ⟨k, e⟩ =>
    ⟨k.gpr, k.rd, k.wr, k.mem, by rw [e, invEnv_eval]⟩

end VG.Proof.X25519.X86_64
