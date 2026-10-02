import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT

/-!
# AES-GCM on x86-64: `flush`, `lens` and `tag` in two runs

Untrusted: everything here is checked by Lean. Each leaks only what its
public registers (the number of buffered bytes, the lengths) and the
environment say: the code around the calls is checked by the taint
analysis, and the calls of `vg_ghash` and `vg_aes_ctr32` have the same
arguments in both runs (for `tag`, by `tagMid_ok`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- `flush yo`, with the same number of buffered bytes. -/
theorem flush_rel : RelCT isa (EnvAgree Ctx St W SP [.rbx]) (flush v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_regs ([.rbx] ++ [.r13, .r14, .r15, .rsp]) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) true
      (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine rel_reassoc2 (RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => h.1.2) (rel_taint ([.rbx] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.1.1.1) ⟨_, by taint_decide⟩))
    ?_)
  refine (ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (gh1Check_r15_96 hyo) (F₁ := Env Ctx St W SP) (F₂ := Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], covers_left (he.perm.wC (by decide))⟩

/-- `lens yo`, with the same lengths. -/
theorem lens_rel : RelCT isa (EnvAgree Ctx St W SP [.rbx, .rbp]) (lens v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_taint ([.rbx, .rbp] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine (ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (gh1Check_r15_96 hyo) (F₁ := Env Ctx St W SP) (F₂ := Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], covers_left (he.perm.wC (by decide))⟩

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `tag o`, with the same lengths and number of rounds. -/
theorem tag_rel {o R : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (fun s₁ s₂ => EnvAgree Ctx St W SP [.rbx, .rbp] s₁ s₂ ∧ RoundsAt s₁.mem W R ∧ RoundsAt s₂.mem W R)
      (tag v.callees o) fun _ _ => True := by
  -- The arguments of the call, in each run.
  let G : State → Prop := fun s => Env Ctx St W SP s ∧
    CtrCall s Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1
  have hG : ∀ s, (Env Ctx St W SP s ∧ RoundsAt s.mem W R) → WP isa (.seq (lens v.callees 16)
      (.block ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax,
        .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO))) s G := fun s h =>
    WP.mono (tagMid_ok v L ho h.1 rfl h.2 rfl) fun _ M => ⟨M.env, M.call⟩
  have hL : ∀ s, Env Ctx St W SP s → WP isa (lens v.callees 16) s (Env Ctx St W SP) := fun s he =>
    WP.mono (lens_ok v L (.inr rfl) he rfl) fun _ h => h.1
  have hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block ([.mov .rax (.mem (at_ .r14 16)),
      .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
      .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++
      ptr .r9 .r15 scrO)) hc).isSome = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  let P₀ : State → State → Prop := fun s₁ s₂ => EnvAgree Ctx St W SP [.rbx, .rbp] s₁ s₂ ∧
    RoundsAt s₁.mem W R ∧ RoundsAt s₂.mem W R
  have l : RelCT isa P₀ (lens v.callees 16) fun s₁ s₂ => True ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ :=
    rel_wp ((lens_rel v L (.inr rfl)).mono (fun _ _ h => h.1) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.1, h.1.2.1⟩) hL hL
  have b : RelCT isa (fun s₁ s₂ => True ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) _ fun _ _ => True :=
    rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1, h.2.2, fun _ h => by cases h⟩) hc
  have pre : RelCT isa P₀ _ fun s₁ s₂ => True ∧ G s₁ ∧ G s₂ :=
    rel_wp (RelCT.seq l b) (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2.1, h.2.2⟩⟩) (fun s h => hG s h) (fun s h => hG s h)
  refine rel_reassoc2 (RelCT.seq pre (ctr_rel v.ctr fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩))
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

end

end VG.Proof.AesGcm.X86_64
