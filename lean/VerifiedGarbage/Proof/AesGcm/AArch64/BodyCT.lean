import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT

/-!
# AES-GCM on AArch64: the bodies are constant time

Untrusted: everything here is checked by Lean. Two runs of `encBody`,
`decAbs`, `decBody` or `finBody` from states with the same public values (the
lengths and the offset of the buffered additional data) leak the same.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

omit L in
theorem hz_mod (o : Nat) (ho : o < 16) : (Spec.Gcm.zeros o).length % 16 = o := by
  rw [Proof.Gcm.length_zeros]; exact Nat.mod_eq_of_lt ho

/-- `fo`, `flush` and `textArgs` in two runs, and what each leaves. -/
theorem padArgs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, CrIn Ctx St W SP k₁ R P D n τ₁ → CrIn Ctx St W SP k₂ R P D n τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq fo (.seq (flush v.callees 16) (.seq (.block textArgs) rest))) TT := by
  have hn := h₁.data.ok.lt
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k27₁ : k₁ .x27 = BitVec.ofNat 64 P := (h₁.kept .x27 (by decide)).symm.trans h₁.x27
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (h₁.kept .x22 (by decide)).symm.trans h₁.x22
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k27₂ : k₂ .x27 = BitVec.ofNat 64 P := (h₂.kept .x27 (by decide)).symm.trans h₂.x27
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (h₂.kept .x22 (by decide)).symm.trans h₂.x22
  refine rel_seq (rel_taint [.x25, .x26, .x27] (by rw [h₁.env.sp, h₂.env.sp])
      (by agree_tac [h₁.x25, h₂.x25, hq, h₁.x26, h₂.x26, h₁.x27, h₂.x27]) ⟨_, by taint_decide⟩)
    (fo_ok h₁.x25 h₁.x26 h₁.x27 hn h₁.hP) (fo_ok h₂.x25 h₂.x26 h₂.x27 hn h₂.hP)
    fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have he₁ := h₁.env.of_regs r₁
  have he₂ := h₂.env.of_regs r₂
  have hk₁ := h₁.kept.of_others r₁.others
  have hk₂ := h₂.kept.of_others r₂.others
  rw [← hq] at x25₂
  refine rel_seq (flush_rel L v (.inr rfl) he₁ he₂ hk₁ hk₂ x25₁ x25₂ (by split <;> omega))
    (WP.with_rdwr (flushStep_ok L v (a := a₁) (c := c₁) (n := n) he₁ hk₁ (by rw [x25₁, h₁.hc]) rfl))
    (WP.with_rdwr (flushStep_ok L v (a := a₂) (c := c₂) (n := n) he₂ hk₂ (by rw [x25₂, h₂.hc, hq]) rfl))
    fun τ₁ τ₂ ⟨⟨fe₁, fk₁, _, _, _⟩, frd₁, fwr₁⟩ ⟨⟨fe₂, fk₂, _, _, _⟩, frd₂, fwr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x27, .x28] (by rw [fe₁.sp, fe₂.sp])
      (by agree_tac [fk₁ .x26 (by decide), fk₂ .x26 (by decide), fk₁ .x27 (by decide), fk₂ .x27 (by decide),
        fk₁ .x28 (by decide), fk₂ .x28 (by decide), k26₁, k26₂, k27₁, k27₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textArgs_ok fk₁ k26₁ k27₁ k28₁ h₁.hP) (textArgs_ok fk₂ k26₂ k27₂ k28₂ h₂.hP)
    fun τ₁ τ₂ ⟨a25₁, a23₁, a24₁, ra₁⟩ ⟨a25₂, a23₂, a24₂, ra₂⟩ => ?_
  have ge₁ := fe₁.of_regs ra₁
  have ge₂ := fe₂.of_regs ra₂
  have gk₁ := fk₁.of_others ra₁.others
  have gk₂ := fk₂.of_others ra₂.others
  exact hr τ₁ τ₂
    ⟨ge₁, gk₁, (gk₁ .x22 (by decide)).trans k22₁, h₁.rounds, a23₁, a24₁, a25₁,
      h₁.data.of_eq (by rw [ra₁.rd, frd₁, r₁.rd]) (by rw [ra₁.wr, fwr₁, r₁.wr])⟩
    ⟨ge₂, gk₂, (gk₂ .x22 (by decide)).trans k22₂, h₂.rounds, a23₂, a24₂, a25₂,
      h₂.data.of_eq (by rw [ra₂.rd, frd₂, r₂.rd]) (by rw [ra₂.wr, fwr₂, r₂.wr])⟩

/-- `textAbs` in two runs. -/
theorem textAbs_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {n P : Nat} {D : Addr} {σ₁ σ₂ : State}
    (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h23₁ : σ₁.gpr .x23 = D) (h23₂ : σ₂.gpr .x23 = D)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 n) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 n)
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (P % 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (P % 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 n) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 n)
    (hd₁ : DataOk St W σ₁ D n) (hd₂ : DataOk St W σ₂ D n) :
    RelCT isa (Eq2 σ₁ σ₂) (textAbs v.callees) TT := by
  refine rel_ite (eval_zero h26₁ hd₁.lt) (eval_zero h26₂ hd₁.lt) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (by rw [he₁.sp, he₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact absorb_rel L v (.inr rfl)
      (⟨he₁, hk₁, h23₁, h24₁, h25₁, hz_mod _ (Nat.mod_lt _ (by decide)), hd₁, rfl⟩ :
        AbsIn Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₁)
      (⟨he₂, hk₂, h23₂, h24₂, h25₂, hz_mod _ (Nat.mod_lt _ (by decide)), hd₂, rfl⟩ :
        AbsIn Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) (Spec.Gcm.zeros (P % 16)) D n (P % 16) σ₂)

/-- `encBody` in two runs. -/
theorem encBody_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {R n P : Nat} {D : Addr} {a₁ a₂ c₁ c₂ : List Byte}
    {H₁ H₂ : Block} {σ₁ σ₂ : State} (h₁ : BodyIn Ctx St W SP k₁ R n P D a₁ c₁ H₁ σ₁)
    (h₂ : BodyIn Ctx St W SP k₂ R n P D a₂ c₂ H₂ σ₂) (hq : a₁.length % 16 = a₂.length % 16) :
    RelCT isa (Eq2 σ₁ σ₂) (encBody v.callees) TT := by
  have k26₁ : k₁ .x26 = BitVec.ofNat 64 n := (h₁.kept .x26 (by decide)).symm.trans h₁.x26
  have k28₁ : k₁ .x28 = D := (h₁.kept .x28 (by decide)).symm.trans h₁.x28
  have k26₂ : k₂ .x26 = BitVec.ofNat 64 n := (h₂.kept .x26 (by decide)).symm.trans h₂.x26
  have k28₂ : k₂ .x28 = D := (h₂.kept .x28 (by decide)).symm.trans h₂.x28
  refine padArgs_rel L v h₁ h₂ hq fun τ₁ τ₂ c₁ c₂ => ?_
  refine rel_seq (crypt_rel L v c₁ c₂) (WP.with_rdwr (crypt_ok L v (icb := 0) c₁))
    (WP.with_rdwr (crypt_ok L v (icb := 0) c₂)) fun τ₁' τ₂' ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_taint [.x26, .x28] (by rw [o₁.env.sp, o₂.env.sp])
      (by agree_tac [o₁.kept .x26 (by decide), o₂.kept .x26 (by decide), o₁.kept .x28 (by decide),
        o₂.kept .x28 (by decide), k26₁, k26₂, k28₁, k28₂]) ⟨_, by taint_decide⟩)
    (textPiece_ok o₁.kept k26₁ k28₁) (textPiece_ok o₂.kept k26₂ k28₂) fun τ₁ τ₂ ⟨p23₁, p24₁, rp₁⟩ ⟨p23₂, p24₂, rp₂⟩ => ?_
  have pk₁ := o₁.kept.of_others rp₁.others
  have pk₂ := o₂.kept.of_others rp₂.others
  exact textAbs_rel L v (o₁.env.of_regs rp₁) (o₂.env.of_regs rp₂) pk₁ pk₂ p23₁ p23₂ p24₁ p24₂
    (by rw [rp₁.others _ (by decide), o₁.x25]) (by rw [rp₂.others _ (by decide), o₂.x25])
    ((pk₁ .x26 (by decide)).trans k26₁) ((pk₂ .x26 (by decide)).trans k26₂)
    (c₁.data.ok.of_eq (by rw [rp₁.rd, rd₁]) (by rw [rp₁.wr, wr₁]))
    (c₂.data.ok.of_eq (by rw [rp₂.rd, rd₂]) (by rw [rp₂.wr, wr₂]))

/-- `finBody o` in two runs. -/
theorem finBody_rel (v : GcmImpl) {o : Nat} (ho : o = 0 ∨ o = 112) {k₁ k₂ : Reg → BitVec 64} {R A P : Nat}
    {σ₁ σ₂ : State} (he₁ : Env Ctx St W SP σ₁) (he₂ : Env Ctx St W SP σ₂) (hk₁ : Kept k₁ σ₁) (hk₂ : Kept k₂ σ₂)
    (h22₁ : σ₁.gpr .x22 = BitVec.ofNat 64 R) (h22₂ : σ₂.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 A) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 A)
    (h27₁ : σ₁.gpr .x27 = BitVec.ofNat 64 P) (h27₂ : σ₂.gpr .x27 = BitVec.ofNat 64 P)
    (hA : A < 2 ^ 64) (hP : P < 2 ^ 64) :
    RelCT isa (Eq2 σ₁ σ₂) (finBody v.callees o) TT := by
  have ho' : (if P = 0 then A % 16 else P % 16) < 16 := by split <;> exact Nat.mod_lt _ (by decide)
  refine rel_seq (rel_taint [.x26, .x27] (by rw [he₁.sp, he₂.sp])
      (by agree_tac [h26₁, h26₂, h27₁, h27₂]) ⟨_, by taint_decide⟩)
    (finOff_ok h26₁ h27₁ hA hP) (finOff_ok h26₂ h27₂ hA hP) fun τ₁ τ₂ ⟨x25₁, r₁⟩ ⟨x25₂, r₂⟩ => ?_
  have fe₁ := he₁.of_regs r₁
  have fe₂ := he₂.of_regs r₂
  have fk₁ := hk₁.of_others r₁.others
  have fk₂ := hk₂.of_others r₂.others
  refine rel_seq (flush_rel L v (.inr rfl) fe₁ fe₂ fk₁ fk₂ x25₁ x25₂ ho')
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₁.mem (Ctx + BitVec.ofNat 64 240)) fe₁ fk₁
      x25₁ (hz_mod _ ho') rfl)
    (flush_ok L (.inr rfl) v (x := Spec.Gcm.zeros _) (H := blockAt τ₂.mem (Ctx + BitVec.ofNat 64 240)) fe₂ fk₂
      x25₂ (hz_mod _ ho') rfl) fun τ₁ τ₂ ⟨t₁, _, _⟩ ⟨t₂, _, _⟩ => ?_
  have k22₁ : k₁ .x22 = BitVec.ofNat 64 R := (hk₁ .x22 (by decide)).symm.trans h22₁
  have k22₂ : k₂ .x22 = BitVec.ofNat 64 R := (hk₂ .x22 (by decide)).symm.trans h22₂
  exact tag_rel L v ho t₁.env t₂.env t₁.kept t₂.kept ((t₁.kept .x22 (by decide)).trans k22₁)
    ((t₂.kept .x22 (by decide)).trans k22₂) hR t₁.x25 t₂.x25

end

end VG.Proof.AesGcm.AArch64
