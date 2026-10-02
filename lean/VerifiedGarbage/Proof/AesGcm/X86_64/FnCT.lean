import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.J0CT

/-!
# AES-GCM on x86-64: functions in two runs

Untrusted: everything here is checked by Lean. A function is its entry,
checked by the taint analysis from the public arguments, after which
correctness says what each run holds (`I₁`, `I₂`); its body, related from
those; and `restore`, checked from the environment the body leaves
(`fn_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

theorem restore_check : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block restore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A function `entry; body; restore`, in two runs from `s₀` and `s₀'`. -/
theorem fn_rel {E : List Instr} {B : Prog isa} {s₀ s₀' : State} {I₁ I₂ : State → Prop} {Ctx St W SP : Addr}
    (rs : List Reg) (hag : ∀ r ∈ rs, s₀.gpr r = s₀'.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) (.block E) hc).isSome = true)
    (hE₁ : WP isa (.block E) s₀ I₁) (hE₂ : WP isa (.block E) s₀' I₂)
    (hB : RelCT isa (fun s₁ s₂ => True ∧ I₁ s₁ ∧ I₂ s₂) B
      fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.seq (.block E) (.seq B (.block restore))) fun _ _ => True := by
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') rs (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h; exact hag) hc) (fun _ _ h => h) (G₁ := I₁) (G₂ := I₂)
    (fun s h => h ▸ hE₁) (fun s h => h ▸ hE₂)
  exact RelCT.seq e (RelCT.seq hB (rel_taint [.r13, .r14, .r15, .rsp]
    (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩) restore_check))

/-- A stack argument loaded into `rax`. -/
theorem loadArg_ok {s : State} {k : Nat}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp k))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 k) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [VG.X86_64.RegUpd.gpr_setReg]
  · intro r a; simp [VG.X86_64.RegUpd.gpr_setReg, a]

/-- A function whose entry first loads `W`, a stack argument, into `rax`. -/
theorem fn_rel₂ {E₁ : List Instr} {B : Prog isa} {s₀ s₀' : State} {I₁ I₂ : State → Prop} {Ctx St W SP : Addr}
    {k : Nat} (rs : List Reg) (hrs : .rsp ∈ rs)
    (hc₀ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp k))]) hc).isSome = true) (hag : ∀ r ∈ rs, s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 k) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 k) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 k) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 k) 8)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (.rax :: rs)) (.block E₁) hc).isSome = true)
    (hE₁ : WP isa (.block ([.mov .rax (.mem (at_ .rsp k))] ++ E₁)) s₀ I₁)
    (hE₂ : WP isa (.block ([.mov .rax (.mem (at_ .rsp k))] ++ E₁)) s₀' I₂)
    (hB : RelCT isa (fun s₁ s₂ => True ∧ I₁ s₁ ∧ I₂ s₂) B
      fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block ([.mov .rax (.mem (at_ .rsp k))] ++ E₁)) (.seq B (.block restore))) fun _ _ => True := by
  have l := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ hrs) hc₀)
    (fun _ _ h => h) (G₁ := fun s' => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 k) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (G₂ := fun s' => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 k) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    (fun s h => by subst h; exact loadArg_ok hr₁) (fun s h => by subst h; exact loadArg_ok hr₂)
  have e := rel_wp (rel_block_split (RelCT.seq l (rel_taint (.rax :: rs) (fun _ _ h r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [h.2.1.1, h.2.2.1, hw]
      · by_cases hx : r = .rax
        · subst hx; rw [h.2.1.1, h.2.2.1, hw]
        · rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) hc))) (fun _ _ h => h) (G₁ := I₁) (G₂ := I₂)
    (fun s h => by subst h; exact hE₁) (fun s h => by subst h; exact hE₂)
  exact RelCT.seq e (RelCT.seq hB (rel_taint [.r13, .r14, .r15, .rsp]
    (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩) restore_check))

/-- Constant time, from runs related from each pair of states. -/
theorem ct_of_rel {k : Contract isa} {c : Prog isa}
    (h : ∀ s₀ s₀', k.pre s₀ → k.pre s₀' → k.pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') c fun _ _ => True) :
    ConstantTime isa k.pre k.pub c :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (h _ _ h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.X86_64
