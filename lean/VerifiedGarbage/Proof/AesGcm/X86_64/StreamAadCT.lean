import VerifiedGarbage.Proof.AesGcm.X86_64.StreamAad
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_aad` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
absorb data at the same address, of the same length, after the same number
of bytes modulo 16 (`absorb_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block)

/-- What the entry of `vg_aes_gcm_stream_aad` leaves. -/
theorem streamAadEntry_ok {s : State} (hp : Proof.AesGcm.streamAadX86_64.pre s) :
    WP isa (.block (save .r9 ++ ([.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi),
        .mov .r12 (.reg .rcx), .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] : List Instr))) s
      fun s₂ => ∃ H, AbsIn (s.gpr .rdi) (s.gpr .rsi) (s.gpr .r9) (s.gpr .rsp) 16 H
        (List.replicate ((s.gpr .rdx).toNat % 16) 0) (s.gpr .rcx) (s.gpr .r8).toNat s₂ := by
  simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, -, -, d_ds, d_dw, -, -, -, -, k_d, -, -, -, wd, -, -⟩ := hp
  have pW : Covers [⟨s.gpr .r9, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := save_ok s .r9 rfl pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hbx, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r9), .mov .r14 (.reg .rsi), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rcx),
        .mov .rbp (.reg .r8), .mov .rbx (.reg .rdx), .alu .and .rbx (imm 15)] s₁ = some s₂ ∧
      s₂.gpr .r15 = s.gpr .r9 ∧ s₂.gpr .r14 = s.gpr .rsi ∧ s₂.gpr .r13 = s.gpr .rdi ∧ s₂.gpr .r12 = s.gpr .rcx ∧
      s₂.gpr .rbp = BitVec.ofNat 64 (s.gpr .r8).toNat ∧
      s₂.gpr .rbx = BitVec.ofNat 64 ((List.replicate ((s.gpr .rdx).toNat % 16) (0 : Byte)).length % 16) ∧
      s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hand := and15 (s.gpr .rdx)
    rw [imm_eq (by decide)] at hand
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hg₁, hand, List.length_replicate, Nat.mod_mod]
    · simp [gpr_setReg, hg₁]
    all_goals rfl
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, _, ⟨h13, h14, h15, hg₂, ?_⟩,
    h12, hbp, hbx, ⟨?_, by have := (s.gpr .r8).isLt; omega, wd, d_ds, d_dw, k_d⟩, rfl⟩⟩)
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
    · exact pW
  · rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem streamAad_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamAadX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamAadX86_64.pre s₀') (hq : Proof.AesGcm.streamAadX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamAad v.callees) fun _ _ => True := by
  have L : Lay (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .r9) (s₀.gpr .rsp) := by
    simp only [Proof.AesGcm.streamAadX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
    obtain ⟨-, -, d_cs, d_cw, -, -, d_sw, -, -, k_c, -, k_s, k_w, wc, -, ws, ww⟩ := hp
    exact Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have hE₂ := streamAadEntry_ok hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇] at hE₂
  refine fn_rel (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := s₀.gpr .r9) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨_, by taint_decide⟩ (streamAadEntry_ok hp) hE₂ ?_
  have a := RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
    absorb_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := List.replicate ((s₀.gpr .rdx).toNat % 16) 0)
      (x₂ := List.replicate ((s₀.gpr .rdx).toNat % 16) 0) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat) rfl
  have hw : ∀ s, (∃ H, AbsIn (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .r9) (s₀.gpr .rsp) 16 H
      (List.replicate ((s₀.gpr .rdx).toNat % 16) 0) (s₀.gpr .rcx) (s₀.gpr .r8).toNat s) →
      WP isa (absorb v.callees 16) s (Env (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .r9) (s₀.gpr .rsp)) :=
    fun s ⟨_, h⟩ => WP.mono (absorb_ok v L (.inr rfl) h) fun _ o => o.env
  exact (rel_wp a (fun _ _ ⟨H₁, H₂, h₁, h₂⟩ => ⟨⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩) hw hw).mono
    (fun _ _ ⟨_, ⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩ => ⟨H₁, H₂, h₁, h₂⟩) fun _ _ h => h.2

theorem streamAad_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamAadX86_64.pre Proof.AesGcm.streamAadX86_64.pub (streamAad v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamAad_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
