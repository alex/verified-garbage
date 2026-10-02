import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry and the exit by the
taint analysis; the bodies by `encBody_rel` and `decBody_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `decAbs` in two runs. -/
theorem decAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decAbs v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  exact padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ =>
    textAbs_rel L v c₁.env c₂.env c₁.kept c₂.kept c₁.x23 c₂.x23 c₁.x24 c₂.x24 c₁.x25 c₂.x25
      ((c₁.kept .x26 (by decide)).trans k26₁) ((c₂.kept .x26 (by decide)).trans k26₂) c₁.data.ok c₂.data.ok

/-- `decBody` in two runs. -/
theorem decBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (decBody v.callees) TT := by
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (h₁.kept .x22 (by decide)).symm.trans h₁.x22
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (h₂.kept .x22 (by decide)).symm.trans h₂.x22
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine rel_seq (decAbs_rel L v h₁ h₂ hq) (decAbs_ok L v h₁) (decAbs_ok L v h₂)
    fun τ₁ τ₂ ⟨e₁, kk₁, x25₁, _, rd₁, wr₁, _⟩ ⟨e₂, kk₂, x25₂, _, rd₂, wr₂, _⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [e₁.sp, e₂.sp])
      (by agree_tac [kk₁ .x26 (by decide), kk₂ .x26 (by decide), kk₁ .x28 (by decide),
        kk₂ .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok kk₁ k26₁ k28₁) (textPiece_ok kk₂ k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := kk₁.of_others rp₁.others
  have pk₂ := kk₂.of_others rp₂.others
  exact crypt_rel L v
    ⟨e₁.of_regs rp₁, pk₁, (pk₁ .x22 (by decide)).trans k22₁, h₁.rounds, p23₁, p24₁,
      by rw [rp₁.others _ (by decide), x25₁], h₁.data.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁])⟩
    ⟨e₂.of_regs rp₂, pk₂, (pk₂ .x22 (by decide)).trans k22₂, h₂.rounds, p23₂, p24₂,
      by rw [rp₂.others _ (by decide), x25₂], h₂.data.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂])⟩

end

/-- The entry, a body and the exit, in two runs. -/
theorem cr_rel {body : Prog isa} {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂)
    (hq : streamCryptPub σ₁ σ₂)
    (hrel : ∀ {Ctx St W SP : Addr} {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
      {H₁ H₂ : Block} {τ₁ τ₂ : State}, Lay Ctx St W → BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ τ₁ →
      BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ τ₂ → a₁.length % 16 = a₂.length % 16 →
      RelCT isa (Eq2 τ₁ τ₂) body TT)
    (hw : ∀ {Ctx St W SP : Addr} {k : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a c : List Byte} {H : Block}
      {τ : State}, Lay Ctx St W → BodyIn Ctx St W SP k R n P D a c H τ →
      WP isa body τ fun τ' => Env Ctx St W SP τ') :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block crEntry) (.seq body (.block restore))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩ := hq
  simp only [streamCryptPre] at h₁ h₂
  rw [← q0, ← q1, ← q2, ← q5, ← q6, ← q7] at h₂
  obtain ⟨hrd₁, hwr₁, dcs, dcd, dcw, dsd, dsw, ddw, wc, ws, wd, ww, hR⟩ := h₁
  obtain ⟨hrd₂, hwr₂, -⟩ := h₂
  generalize hCtx : σ₁.gpr .x0 = Ctx at *
  generalize hSt : σ₁.gpr .x2 = St at *
  generalize hD : σ₁.gpr .x5 = D at *
  generalize hn : (σ₁.gpr .x6).toNat = n at *
  generalize hW : σ₁.gpr .x7 = W at *
  have L : Lay Ctx St W := Lay.of wc ws ww dcs dcw dsw
  have hlt : n < 2 ^ 64 := hn ▸ (σ₁.gpr .x6).isLt
  have perm (σ : State) (hrd : σ.rd = [⟨Ctx, 256⟩]) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 2560⟩]) :
      Perm Ctx St W σ :=
    ⟨covers_mem (by rw [hrd, hwr]; simp), covers_of_mem (by rw [hwr]; simp), covers_of_mem (by rw [hwr]; simp)⟩
  have mk (σ σ' : State) (hwr : σ.wr = [⟨St, 80⟩, ⟨D, n⟩, ⟨W, 2560⟩]) (hR : rounds (σ.gpr .x1))
      (h : Env Ctx St W σ.sp σ' ∧ Kept σ'.gpr σ' ∧ σ'.gpr .x22 = BitVec.ofNat 64 (σ.gpr .x1).toNat ∧
        σ'.gpr .x25 = BitVec.ofNat 64 ((σ.gpr .x3).toNat % 16) ∧ σ'.gpr .x26 = BitVec.ofNat 64 n ∧
        σ'.gpr .x27 = BitVec.ofNat 64 (σ.gpr .x4).toNat ∧ σ'.gpr .x28 = D ∧ σ'.mem = savedMem σ.mem W σ.gpr ∧
        σ'.rd = σ.rd ∧ σ'.wr = σ.wr) :
      BodyIn Ctx St W σ.sp σ'.gpr (σ.gpr .x1).toNat n (σ.gpr .x4).toNat D
        (Spec.Gcm.zeros ((σ.gpr .x3).toNat % 16)) (Spec.Gcm.zeros (σ.gpr .x4).toNat)
        (blockAt σ'.mem (Ctx + BitVec.ofNat 64 240)) σ' := by
    obtain ⟨he, hk, x22, x25, x26, x27, x28, _, rd, wr⟩ := h
    exact ⟨he, hk, x22, hR, by rw [x25, hz_mod _ (Nat.mod_lt _ (by decide))], x26, x27, x28,
      Proof.Gcm.length_zeros _, (σ.gpr .x4).isLt,
      ⟨⟨covers_left (by rw [wr, hwr]; exact covers_of_mem (by simp)), hlt, wd, dsd.symm, ddw⟩,
        by rw [wr, hwr]; exact covers_of_mem (by simp), dcd⟩, rfl⟩
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] qsp
      (by agree_tac [hCtx, hSt, hD, hW, ← q0, q1, ← q2, q3, q4, ← q5, q6, ← q7]) ⟨_, by taint_decide⟩)
    (crEntry_ok hCtx hSt hD hn hW (perm σ₁ hrd₁ hwr₁))
    (crEntry_ok q0.symm q2.symm q5.symm (by rw [← q6, hn]) q7.symm (perm σ₂ hrd₂ hwr₂))
    fun τ₁ τ₂ a₁ a₂ => ?_
  have b₁ := mk σ₁ τ₁ hwr₁ hR a₁
  have b₂ := mk σ₂ τ₂ hwr₂ (by rw [← q1]; exact hR) a₂
  rw [← qsp, ← q1, ← q4] at b₂
  refine rel_seq (hrel L b₁ b₂ (by rw [Proof.Gcm.length_zeros, Proof.Gcm.length_zeros, Nat.mod_mod, Nat.mod_mod, q3]))
    (hw L b₁) (hw L b₂) fun τ₁ τ₂ e₁ e₂ => ?_
  exact rel_taint [.x19] (by rw [e₁.sp, e₂.sp]) (by agree_tac [e₁.x19, e₂.x19]) ⟨_, by taint_decide⟩

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa streamEncryptAArch64.pre streamEncryptAArch64.pub (streamEncrypt v.callees) :=
  ct_of fun _ _ h₁ h₂ hq => cr_rel h₁ h₂ hq (fun L b₁ b₂ hq => encBody_rel L v b₁ b₂ hq)
    (fun L b => WP.mono (encBody_ok L v b 0) fun _ h => h.env)

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa streamDecryptAArch64.pre streamDecryptAArch64.pub (streamDecrypt v.callees) :=
  ct_of fun _ _ h₁ h₂ hq => cr_rel h₁ h₂ hq (fun L b₁ b₂ hq => decBody_rel L v b₁ b₂ hq)
    (fun L b => WP.mono (decBody_ok L v b 0) fun _ h => h.env)

end VG.Proof.AesGcm.AArch64
