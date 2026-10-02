import VerifiedGarbage.Impl.Ed25519.X86.Power
import VerifiedGarbage.Proof.Ed25519.X86.Field
import VerifiedGarbage.Proof.X25519.Invert

/-! Fixed-count squaring and compositional field exponentiation. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (mul)
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)
def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

structure IKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 64 864] s.mem t.mem

theorem IKeep.refl (x : BitVec 32) (s : State) : IKeep x s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem IKeep.trans {x : BitVec 32} {s t u : State} (h : IKeep x s t) (k : IKeep x t u) :
    IKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem IKeep.ctx {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr

theorem IKeep.of_field {x : BitVec 32} {s t : State} (h : FieldKeep x s t) : IKeep x s t :=
  ⟨h.keep.edi, h.keep.esp, h.keep.rd, h.keep.wr, h.frame⟩

theorem IKeep.of_counter {x : BitVec 32} {s t : State} {v : BitVec 32}
    (h : Wp.Upd s t .esi v) : IKeep x s t :=
  ⟨h.other _ (by decide), h.other _ (by decide), h.rd, h.wr,
    by rw [h.mem]; exact Frame.refl _ _⟩

def ISpec (x : BitVec 32) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Ctx x s → WP isa c s fun t => IKeep x s t ∧ env t.mem x = f (env s.mem x)

theorem ISpec.seq {x : BitVec 32} {c d : Prog isa} {f g : Env → Env}
    (h : ISpec x c f) (k : ISpec x d g) : ISpec x (.seq c d) (fun e => g (f e)) :=
  fun s hc => WP.seq (WP.mono (h s hc) fun t ⟨ht, et⟩ =>
    WP.mono (k t (ht.ctx hc)) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩)

theorem ISpec.append {x : BitVec 32} {c d : List Instr} {f g : Env → Env}
    (h : ISpec x (.block c) f) (k : ISpec x (.block d) g) :
    ISpec x (.block (c ++ d)) (fun e => g (f e)) := fun s hc => by
  rw [WP.block_append_iff]
  exact WP.mono (h s hc) fun t ⟨ht, et⟩ =>
    WP.mono (k t (ht.ctx hc)) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, by rw [eu, et]⟩

abbrev ISlot (o : Slot) : Prop := 14 ≤ o.val ∧ o.val < 18

theorem mulI (x : BitVec 32) (o a b : Slot) (_ho : ISlot o) :
    ISpec x (.block (mul (offset o) (offset a) (offset b))) (opMul o a b) := fun _ hc =>
  WP.mono (fieldOp_ok hc (.mul o a b)) fun _ ⟨hk, he⟩ => ⟨IKeep.of_field hk, he⟩

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

theorem sqLoop_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx x s₀) (o : Slot)
    (v : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → IKeep x s₀ s → s.gpr .esi = BitVec.ofNat 32 m →
      env s.mem x = Function.update (env s₀.mem x) o (sqn v (n - m)) →
      WP isa (.loop (.block (mul (offset o) (offset o) (offset o) ++
        ([.alu .sub .esi (.imm 1)] : List Instr))) .ne) s fun t =>
        IKeep x s₀ t ∧ env t.mem x = Function.update (env s₀.mem x) o (sqn v n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ IKeep x s₀ s ∧
    s.gpr .esi = BitVec.ofNat 32 m ∧
    env s.mem x = Function.update (env s₀.mem x) o (sqn v (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldOp_ok (hk.ctx hc₀) (.mul o o o)) fun t ⟨ht, et⟩ => ?_
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  have ku := hk.trans ((IKeep.of_field ht).trans (IKeep.of_counter hu))
  have bu : u.gpr .esi = BitVec.ofNat 32 (m - 1) := by
    rw [hu.gpr, ht.keep.esi, hb]; exact Wp.ofNat_pred h1
  have eu : env u.mem x = Function.update (env s₀.mem x) o (sqn v (n - (m - 1))) := by
    rw [hu.mem, et, he]
    change opMul o o o (Function.update _ o _) = _
    rw [opMul_update, show n - (m - 1) = (n - m) + 1 by omega]
    rfl
  have ev : isa.eval .ne u = some (!decide (m - 1 = 0)) := by
    show u.zf.map (!·) = _
    rw [hz, ht.keep.esi, hb, Wp.ofNat_pred h1, Wp.ofNat_beq_zero (by omega_using [h2, hn])]
    rfl
  by_cases hm : m = 1
  · subst m
    exact .inl ⟨by rw [ev]; rfl, ku, by simpa only [Nat.sub_self, Nat.sub_zero] using eu⟩
  · exact .inr ⟨by rw [ev]; simp only [show m - 1 ≠ 0 by omega, decide_false]; rfl,
      m - 1, by omega, by omega, by omega, ku, bu, eu⟩

theorem sqnI (x : BitVec 32) (o a : Slot) (_ho : ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    ISpec x (Impl.Ed25519.X86.sqn (offset o) (offset a) n) (opSqn o a n) := by
  intro s hc
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fieldOp_ok hc (.mul o a a)) fun t ⟨ht, et⟩ => ?_
  refine Wp.wp_movi fun u hu => WP.block_nil ?_
  refine sqLoop_ok hc o (env s.mem x a) n hn' (n - 1) u (by omega) (by omega)
    ((IKeep.of_field ht).trans (IKeep.of_counter hu)) hu.gpr ?_
  rw [hu.mem, et, show n - (n - 1) = 1 by omega]
  rfl

end VG.Proof.Ed25519.X86
