import VerifiedGarbage.Proof.AesGcm.AArch64.StreamAad
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_aad` is constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis, from the public arguments and `W`; `absorb` by `absorb_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem streamAad_ct (v : GcmImpl) :
    ConstantTime isa streamAadAArch64.pre streamAadAArch64.pub (streamAad v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, qsp⟩ := hq
  simp only [streamAadAArch64] at h₁ h₂
  rw [← q0, ← q1, ← q3, ← q4, ← q5] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x1 = St at *
  generalize hD : σ₁.gpr .x3 = D at *
  generalize hn : (σ₁.gpr .x4).toNat = n at *
  generalize hW : σ₁.gpr .x5 = W at *
  generalize ho : (σ₁.gpr .x2).toNat % 16 = o at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x4).isLt
  have ho₂ : (σ₂.gpr .x2).toNat % 16 = o := by rw [← q2, ho]
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨D, n⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have hz : (Spec.Gcm.zeros o).length % 16 = o := by
    rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt (ho ▸ Nat.mod_lt _ (by decide))
  have mk (σ σ' : State) (hrd : σ.rd = [⟨Ctx, 256⟩, ⟨D, n⟩]) (hσ : (σ.gpr .x2).toNat % 16 = o)
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x23 = D ∧ σ'.gpr .x24 = BitVec.ofNat 64 n ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x2).toNat % 16) ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      AbsIn Ctx St W σ.sp σ'.gpr (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros o) D n o σ' := by
    obtain ⟨he, hk, x23, x24, x25, _, rd, wr⟩ := h
    exact ⟨he, hk, x23, x24, by rw [x25, hσ], hz, ⟨covers_mem (by rw [rd, wr, hrd]; simp), hlt, wd, dds, ddw⟩,
      rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, ← q1, q2, ← q3, q4, ← q5]) ⟨_, by taint_decide⟩)
    (aadEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (aadEntry_ok q0.symm q1.symm q3.symm (by rw [← q4, hn]) q5.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have j₁ := mk σ₁ τ₁ hrd₁ ho a₁
  have j₂ := mk σ₂ τ₂ hrd₂ ho₂ a₂
  rw [← qsp] at j₂
  refine rel_seq (absorb_rel L v (.inr rfl) j₁ j₂) (absorb_ok L (.inr rfl) v j₁) (absorb_ok L (.inr rfl) v j₂)
    fun τ₁ τ₂ b₁ b₂ => ?_
  exact rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
    ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64
