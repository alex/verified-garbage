import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
import VerifiedGarbage.Proof.X25519.Invert

/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

/-- Field work and its fixed-count squaring counter. -/
structure IKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest (.r10 :: clob) s t
  frame : Frame [FA ACC b] s.mem t.mem

theorem IKeep.trans {b : BitVec 32} {s t u : State} (h : IKeep b s t) (k : IKeep b t u) :
    IKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem IKeep.ctx {b : BitVec 32} {s t : State} (h : IKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem IKeep.of_counter {b : BitVec 32} {s t : State} (hr : Rest [.r10] s t)
    (hm : t.mem = s.mem) : IKeep b s t :=
  ⟨hr.mono (by decide), by rw [hm]; exact Frame.refl _ _⟩

def ISpec (b : BitVec 32) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Ctx b s → AllLim s.mem b → WP isa c s fun t =>
    IKeep b s t ∧ AllLim t.mem b ∧ env t.mem b = f (env s.mem b)

theorem ISpec.seq {b : BitVec 32} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : ISpec b c₁ f) (h₂ : ISpec b c₂ g) : ISpec b (.seq c₁ c₂) fun e => g (f e) :=
  fun s hc hl => WP.seq (WP.mono (h₁ s hc hl) fun _ ⟨k₁, l₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.ctx hc) l₁) fun _ ⟨k₂, l₂, e₂⟩ =>
      ⟨k₁.trans k₂, l₂, by rw [e₂, e₁]⟩)

theorem mulI_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (o a b : Slot) :
    WP isa (mulP o a b) s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      t.gpr .r10 = s.gpr .r10 ∧ env t.mem base = opMul o a b (env s.mem base) :=
  WP.mono (fieldOp_ok hc hl (.mul o a b)) fun _ ⟨hk, hlt, he⟩ =>
    ⟨⟨hk.rest.mono (by decide), hk.frame⟩, hlt, hk.rest.gpr _ (by decide), he⟩

theorem mulI (base : BitVec 32) (o a b : Slot) : ISpec base (mulP o a b) (opMul o a b) :=
  fun _ hc hl => WP.mono (mulI_ok hc hl o a b) fun _ ⟨hk, hlt, _, he⟩ => ⟨hk, hlt, he⟩

theorem decR10_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .r10 = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.subs .r10 .r10 (.imm 1)]) s fun t =>
      t.gpr .r10 = BitVec.ofNat 32 k ∧ t.z = decide (k = 0) ∧
      Rest [.r10] s t ∧ t.mem = s.mem := by
  refine wp_subs (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : s.gpr .r10 - 1 = BitVec.ofNat 32 k := by
    rw [hb, BitVec.ofNat_add]
    change BitVec.ofNat 32 k + (1 : BitVec 32) - 1 = _
    exact BitVec.add_sub_cancel _ _
  exact ⟨ht.gpr.trans he, by rw [hz, he, ofNat_beq_zero hk], ht.rest (by decide), ht.mem⟩

def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

theorem sqLoop_ok {s₀ : State} {base : BitVec 32} (hc : Ctx base s₀)
    (o : Slot) (x : Spec.X25519.Fe) (n : Nat) (hn : n < 65536) :
    ∀ m s, 1 ≤ m → m < n → IKeep base s₀ s → AllLim s.mem base →
      s.gpr .r10 = BitVec.ofNat 32 m →
      env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.subs .r10 .r10 (.imm 1)])) .ne) s fun t =>
        IKeep base s₀ t ∧ AllLim t.mem base ∧
        env t.mem base = Function.update (env s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hl hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) =>
    1 ≤ m ∧ m < n ∧ IKeep base s₀ s ∧ AllLim s.mem base ∧
    s.gpr .r10 = BitVec.ofNat 32 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m))) ?_
    m s ⟨h1, h2, hk, hl, hb, he⟩
  intro m s ⟨h1, h2, hk, hl, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.seq (WP.mono (mulI_ok (hk.ctx hc) hl o o o) fun s1 ⟨k1, l1, b1, e1⟩ => ?_)
  refine WP.mono (decR10_ok (by omega) (b1.trans hb)) fun s2 ⟨b2, z2, r2, mem2⟩ => ?_
  have k2 : IKeep base s₀ s2 := hk.trans (k1.trans (IKeep.of_counter r2 mem2))
  have l2 : AllLim s2.mem base := by rw [mem2]; exact l1
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) := by
    rw [mem2, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem base) o)
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [VG.Arm.eval, z2]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, l2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : m ≠ 0), Bool.not_false],
      m, by omega, by omega, by omega, k2, l2, b2, e2⟩

theorem sqnI (base : BitVec 32) (o a : Slot) (n : Nat) (hn : 2 ≤ n) (hn' : n < 65536) :
    ISpec base (Impl.Ed25519.Arm.sqn o a n) (opSqn o a n) := by
  intro s hc hl
  refine WP.seq (WP.mono (mulI_ok hc hl o a a) fun s1 ⟨k1, l1, _, e1⟩ => ?_)
  refine WP.seq (wp_movw fun s2 h2 => WP.block_nil ?_)
  have b2 : s2.gpr .r10 = BitVec.ofNat 32 (n - 1) := by
    rw [h2.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : n - 1 < 2 ^ 16)]
  have k2 : IKeep base s s2 := k1.trans (IKeep.of_counter (h2.rest (by decide)) h2.mem)
  refine sqLoop_ok hc o (env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2
    (by rw [h2.mem]; exact l1) b2 ?_
  rw [h2.mem, e1, show n - (n - 1) = 1 by omega]
  rfl

end VG.Proof.Ed25519.Arm
