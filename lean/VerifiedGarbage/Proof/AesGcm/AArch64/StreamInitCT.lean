import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_init` is constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis, from the public arguments and `W`; `j0` by `j0_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem streamInit_ct (v : GcmImpl) :
    ConstantTime isa streamInitAArch64.pre streamInitAArch64.pub (streamInit v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, qsp⟩ := hq
  simp only [streamInitAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q3, ← q4] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hNp : σ₁.gpr .x1 = Np at *
  generalize hn : (σ₁.gpr .x2).toNat = n at *
  generalize hSt : σ₁.gpr .x3 = St at *
  generalize hW : σ₁.gpr .x4 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x2).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨Np, n⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨Np, n⟩])
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x23 = Np ∧ σ'.gpr .x24 = BitVec.ofNat 64 n ∧
        σ'.gpr .x26 = BitVec.ofNat 64 n ∧ σ'.gpr .x27 = 0 ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧ σ'.rd = σ.rd ∧
        σ'.wr = σ.wr) :
      J0In Ctx St W σ.sp σ'.gpr (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) Np n σ' := by
    obtain ⟨he, hk, x23, x24, x26, x27, _, rd, wr⟩ := h
    exact ⟨he, hk, x23, x24, x26, x27, ⟨covers_mem (by rw [rd, wr, hrd]; simp), hlt, wn, dns, dnw⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4] qsp
      (by agree_tac [hCtx, hNp, hSt, hW, ← q0, ← q1, q2, ← q3, ← q4]) ⟨_, by taint_decide⟩)
    (siEntry_ok hCtx hNp hn hSt hW (perm σ₁ hrd₁ hwr₁))
    (siEntry_ok q0.symm q1.symm (by rw [← q2, hn]) q3.symm q4.symm
      (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have j₁ := mk σ₁ τ₁ hrd₁ a₁
  have j₂ := mk σ₂ τ₂ hrd₂ a₂
  rw [← qsp] at j₂
  refine rel_seq (j0_rel L v j₁ j₂) (j0_ok L v j₁) (j0_ok L v j₂) fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64
