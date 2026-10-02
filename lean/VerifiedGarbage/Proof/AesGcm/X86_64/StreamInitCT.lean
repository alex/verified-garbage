import VerifiedGarbage.Proof.AesGcm.X86_64.StreamInit
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_init` is constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
compute `J₀` of nonces at the same address, of the same length (`j0_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block)

/-- What the entry of `vg_aes_gcm_stream_init` leaves. -/
theorem streamInitEntry_ok {s : State} (hp : Proof.AesGcm.streamInitX86_64.pre s) :
    WP isa (.block (save .r8 ++ [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi),
        .mov .r12 (.reg .rsi), .mov .rbp (.reg .rdx)])) s
      fun s₂ => ∃ H, J0In (s.gpr .rdi) (s.gpr .rcx) (s.gpr .r8) (s.gpr .rsp) H (s.gpr .rsi) (s.gpr .rdx).toNat s₂ := by
  simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
  obtain ⟨hrd, hwr, -, -, d_ns, d_nw, -, -, -, -, k_n, -, -, -, wn, -, -⟩ := hp
  have pW : Covers [⟨s.gpr .r8, 2560⟩] s.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ⟨s₁, run₁, hg₁, hrd₁, hwr₁, -, -⟩ := save_ok s .r8 rfl pW
  obtain ⟨s₂, run₂, h15, h14, h13, h12, hbp, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .r15 (.reg .r8), .mov .r14 (.reg .rcx), .mov .r13 (.reg .rdi), .mov .r12 (.reg .rsi),
        .mov .rbp (.reg .rdx)] s₁ = some s₂ ∧
      s₂.gpr .r15 = s.gpr .r8 ∧ s₂.gpr .r14 = s.gpr .rcx ∧ s₂.gpr .r13 = s.gpr .rdi ∧ s₂.gpr .r12 = s.gpr .rsi ∧
      s₂.gpr .rbp = BitVec.ofNat 64 (s.gpr .rdx).toNat ∧ s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    · simp [gpr_setReg, hg₁]
    all_goals rfl
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, _, ⟨h13, h14, h15, hg₂, ?_⟩,
    rfl, h12, hbp, ⟨?_, by have := (s.gpr .rdx).isLt; omega, wn, d_ns, d_nw, k_n⟩⟩⟩)
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [hrd₂, hwr₂, hrd₁, hwr₁]
    · rw [hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_cons_self ..))
    · rw [hwr]; exact covers_of_mem (List.mem_cons_self ..)
    · exact pW
  · rw [hrd₂, hrd₁, hwr₂, hwr₁, hrd]
    exact covers_of_mem (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem streamInit_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamInitX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamInitX86_64.pre s₀') (hq : Proof.AesGcm.streamInitX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamInit v.callees) fun _ _ => True := by
  have L : Lay (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsp) := by
    simp only [Proof.AesGcm.streamInitX86_64, Proof.AesGcm.stk, Proof.AesGcm.ret] at hp
    obtain ⟨-, -, d_cs, d_cw, -, -, d_sw, -, -, k_c, -, k_s, k_w, wc, -, ws, ww⟩ := hp
    exact Lay.of wc ws ww d_cs d_cw d_sw k_c k_s k_w
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆⟩ := hq
  have hE₂ := streamInitEntry_ok hp'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆] at hE₂
  refine fn_rel (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rcx) (W := s₀.gpr .r8) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .rsp] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨_, by taint_decide⟩ (streamInitEntry_ok hp) hE₂ ?_
  have a := RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
    j0_rel v L (H₁ := H₁) (H₂ := H₂) (Np := s₀.gpr .rsi) (n := (s₀.gpr .rdx).toNat)
  have hw : ∀ s, (∃ H, J0In (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsp) H (s₀.gpr .rsi)
      (s₀.gpr .rdx).toNat s) →
      WP isa (j0 v.callees) s (Env (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsp)) :=
    fun s ⟨_, h⟩ => WP.mono (j0_ok v L h) fun _ o => o.env
  exact (rel_wp a (fun _ _ ⟨H₁, H₂, h₁, h₂⟩ => ⟨⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩) hw hw).mono
    (fun _ _ ⟨_, ⟨H₁, h₁⟩, ⟨H₂, h₂⟩⟩ => ⟨H₁, H₂, h₁, h₂⟩) fun _ _ h => h.2

theorem streamInit_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamInitX86_64.pre Proof.AesGcm.streamInitX86_64.pub (streamInit v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamInit_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
