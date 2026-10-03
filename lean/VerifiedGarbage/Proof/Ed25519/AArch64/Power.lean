import VerifiedGarbage.Impl.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Ed25519.RootPower

/-! Merged from `Proof.Ed25519.AArch64.PowerEnv`. -/
section
/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

/-- What the inversion keeps: the registers but `clob` and `x19`, the regions,
and the memory outside `[512, 640)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outside base 512 128 s.mem s'.mem

theorem IKeep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : IKeep base s₁ s₂)
    (h₂ : IKeep base s₂ s₃) : IKeep base s₁ s₃ :=
  ⟨fun r hr hb => (h₂.gpr r hr hb).trans (h₁.gpr r hr hb), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₁.mem.trans h₂.mem⟩

theorem IKeep.scr {base : Addr} {s s' : State} (h : IKeep base s s') (hs : Scr s base large) :
    Scr s' base large :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `c` changes the slots by `f`, and keeps everything else (`IKeep`). -/
def ISpec (base : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base large → WP isa c s fun s' => IKeep base s s' ∧ env s'.mem base = f (env s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env} (h₁ : ISpec (large := large) base c₁ f)
    (h₂ : ISpec (large := large) base c₂ g) : ISpec (large := large) base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem ISpec.append {base : Addr} {l₁ l₂ : List Instr} {f g : Env → Env}
    (h₁ : ISpec (large := large) base (.block l₁) f) (h₂ : ISpec (large := large) base (.block l₂) g) :
    ISpec (large := large) base (.block (l₁ ++ l₂)) fun e => g (f e) := fun s hs => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩

/-- A slot of the inversion's: 14 to 17. -/
abbrev ISlot (o : Slot) : Prop := 14 ≤ o.val ∧ o.val < 18

/-- A multiplication into a slot of the inversion's, which also keeps `x19`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) (ho : ISlot o) :
    WP isa (.block (fieldMul (offset o) (offset a) (offset b))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .x19 = s.gpr .x19 ∧ env s'.mem base = opMul o a b (env s.mem base) :=
  WP.mono (mul_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a) (slot_rangeWith (large := large) b)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      h.gpr _ (by decide), by rw [env_update o h.mem, e]; rfl⟩

theorem mulI (base : Addr) (o a b : Slot) (ho : ISlot o) :
    ISpec (large := large) base (.block (fieldMul (offset o) (offset a) (offset b))) (opMul o a b) := fun _ hs =>
  WP.mono (mulI_ok hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-- A squaring into a slot of the inversion's, which also keeps `x19`. -/
theorem sqrI_ok {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) (ho : ISlot o) :
    WP isa (.block (fieldSqr (offset o) (offset a))) s fun s' =>
      IKeep base s s' ∧ s'.gpr .x19 = s.gpr .x19 ∧ env s'.mem base = opMul o a a (env s.mem base) :=
  WP.mono (sqr_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      h.gpr _ (by decide), by rw [env_update o h.mem, e]; rfl⟩

theorem sqrI (base : Addr) (o a : Slot) (ho : ISlot o) :
    ISpec (large := large) base (.block (fieldSqr (offset o) (offset a))) (opMul o a a) := fun _ hs =>
  WP.mono (sqrI_ok hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-! ## Runs of squarings -/

theorem decX19_ok {s : State} {k : Nat} (hb : s.gpr .x19 = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 k ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem counter_nonzero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases h : k = 0
  · subst k; rfl
  · rw [decide_eq_true h]
    apply bne_iff_ne.mpr
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, show (0 : BitVec 64).toNat = 0 from rfl] at he'
    exact h he'

/-- Slot `o` becomes slot `a` squared `n` times. -/
def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

/-- The loop of `sqn`, with the counter `x19 = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scr s₀ base large) (o : Slot) (ho : ISlot o)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → IKeep base s₀ s → s.gpr .x19 = BitVec.ofNat 64 m →
      env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (fieldSqr (offset o) (offset o) ++
          ([.subImm .x .x19 .x19 1] : List Instr))) (.nonzero .x .x19)) s fun s' =>
        IKeep base s₀ s' ∧ env s'.mem base = Function.update (env s₀.mem base) o (sqn x n) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ IKeep base s₀ s ∧
    s.gpr .x19 = BitVec.ofNat 64 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (sqrI_ok (hk.scr hs₀) o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
  refine WP.mono (decX19_ok (b1.trans hb)) fun s2 ⟨b2, kdec⟩ => ?_
  have k2 : IKeep base s₀ s2 := hk.trans (k1.trans ⟨fun r _ hr => kdec.gpr r (by simpa only [List.mem_singleton] using hr), kdec.rd, kdec.wr, kdec.sp,
    by rw [kdec.mem]; exact Outside.refl _ _ _ _⟩)
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) := by
    rw [kdec.mem, e1, he, opMul_update]
    congr 2
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, read_x, b2, counter_nonzero (by omega : m < 2 ^ 64)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_true (by omega : m ≠ 0)], m, by omega,
      by omega, by omega, k2, rfl, e2⟩

/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : Slot) (ho : ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    ISpec (large := large) base (Impl.Ed25519.AArch64.sqn (offset o) (offset a) n) (opSqn o a n) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrI_ok hs o a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (const64_ok s1 .x19 (BitVec.ofNat 64 (n - 1))) fun s2 ⟨b2, kdec⟩ => ?_
  have k2 : IKeep base s s2 := k1.trans ⟨fun r _ hr => kdec.gpr r (by simpa only [List.mem_singleton] using hr), kdec.rd, kdec.wr, kdec.sp,
    by rw [kdec.mem]; exact Outside.refl _ _ _ _⟩
  refine sqLoop_ok hs o ho (env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [kdec.mem, e1, show n - (n - 1) = 1 by omega]
  rfl


end VG.Proof.Ed25519.AArch64
end

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : Addr) : ISpec (large := large) base power250 power250Env := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : ISpec (large := large) base _ _ :=
    (sqrI base 14 2 ⟨by decide, by decide⟩).seq <|
    ((sqrI base 15 14 ⟨by decide, by decide⟩).append
      (sqrI base 15 15 ⟨by decide, by decide⟩)).seq <|
    ((((mulI base 15 2 15 ⟨by decide, by decide⟩).append
      (mulI base 14 14 15 ⟨by decide, by decide⟩)).append
      (sqrI base 16 14 ⟨by decide, by decide⟩)).append
      (mulI base 15 15 16 ⟨by decide, by decide⟩)).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 16 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 16 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 15 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (sqnI base 17 16 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (sqnI base 16 16 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (mulI base 15 16 15 ⟨by decide, by decide⟩)
  exact h

def invEnv (e : Env) : Env := opMul 15 15 14 (opSqn 15 15 5 (power250Env e))
def rootEnv (e : Env) : Env := opMul 15 15 2 (opSqn 15 15 2 (power250Env e))

theorem invert_spec (base : Addr) : ISpec (large := large) base invert invEnv := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : ISpec (large := large) base _ _ := (power250_spec base).seq ((sqnI base 15 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (mulI base 15 15 14 ⟨by decide, by decide⟩))
  exact h

theorem rootPower_spec (base : Addr) : ISpec (large := large) base Impl.Ed25519.AArch64.rootPower rootEnv := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : ISpec (large := large) base _ _ := (power250_spec base).seq ((sqnI base 15 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI base 15 15 2 ⟨by decide, by decide⟩))
  exact h

theorem invEnv_eval (e : Env) : invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp (config := {decide := true}) only [invEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp (config := {decide := true}) only [rootEnv, power250Env, opMul, opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa invert s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) :=
  WP.mono (invert_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa Impl.Ed25519.AArch64.rootPower s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) :=
  WP.mono (rootPower_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, rootEnv_eval]⟩

end VG.Proof.Ed25519.AArch64
