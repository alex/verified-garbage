import VerifiedGarbage.Proof.AesGcm.X86_64.StreamDecrypt
import VerifiedGarbage.Proof.AesGcm.X86_64.TextAbsorbCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. After the entry, both runs
encrypt (`crypt_rel`) and absorb (`textAbsorb_rel`) data at the same address,
of the same length, after the same lengths, with the same number of rounds;
the lengths, the data's address and the rounds stay in `W` (`CrS`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- What stays in `W` and the data, between the pieces. -/
def CrS (Ctx St W SP : Addr) (R : Nat) (aL tL : BitVec 64) (D : Addr) (n : Nat) (s : State) : Prop :=
  (∃ H, TaIn Ctx St W SP H aL tL D n s) ∧ RoundsAt s.mem W R ∧ DataW Ctx St W SP s D n

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
/-- `CrS` after code writing only the regions `rs`, apart from `W`'s slots and the key context. -/
theorem CrS.frame {R : Nat} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s s' : State}
    (h : CrS Ctx St W SP R aL tL D n s) (he : Env Ctx St W SP s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hk : ∀ d, 176 ≤ d → d + 8 ≤ 216 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r)
    (hc : ∀ r ∈ rs, (⟨Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r) :
    CrS Ctx St W SP R aL tL D n s' := by
  obtain ⟨⟨H, t⟩, hR, hd⟩ := h
  have rd : ∀ d, 176 ≤ d → d + 8 ≤ 216 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (hk d h₁ h₂) (by decide)
  exact ⟨⟨H, he, by rw [blockAt_frame hf hc, t.hH], by rw [rd 184 (by decide) (by decide)]; exact t.alen,
    by rw [rd 192 (by decide) (by decide)]; exact t.tlen, by rw [rd 200 (by decide) (by decide)]; exact t.dat,
    by rw [rd 208 (by decide) (by decide)]; exact t.len, t.data.of_eq hrd hwr⟩,
    ⟨by rw [rd 176 (by decide) (by decide)]; exact hR.1, hR.2⟩, hd.of_eq hrd hwr⟩

/-- After `crypt`. -/
theorem crypt_crS {R : Nat} {icb : Block} {P : Nat} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State}
    (h : CrS Ctx St W SP R aL tL D n s) (hi : CrIn Ctx St W SP R icb P D n s) :
    WP isa (crypt v.callees) s (CrS Ctx St W SP R aL tL D n) :=
  WP.mono (WP.with_rdwr (crypt_ok v L hi)) fun _ ⟨co, hrd, hwr⟩ => h.frame co.env hrd hwr co.frame
    (fun d h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (h.2.2.ok.w.sub_right (Lay.wSub (by omega))).symm
      · exact (L.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w (by omega)).symm)
    (fun r hr => (ctx_crFrame L h.2.2 r hr).sub_left (Lay.ctxSub (by decide)))

/-- After `textAbsorb`. -/
theorem ta_crS {R : Nat} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State} {a c : List Byte}
    (hA : aL = BitVec.ofNat 64 a.length) (hT : tL.toNat = c.length) (h : CrS Ctx St W SP R aL tL D n s) :
    WP isa (textAbsorb v.callees) s (CrS Ctx St W SP R aL tL D n) := by
  have t := h.1.choose_spec
  refine WP.mono (WP.with_rdwr (textAbsorb_ok v L t hA hT)) fun _ ⟨⟨he, f, _⟩, hrd, hwr⟩ =>
    h.frame he hrd hwr f (fun d h₁ h₂ => kept_taFrame L h₁ (by omega)) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L in
/-- The data reloaded for `crypt`. -/
theorem reload_ok {R : Nat} {aL tL : BitVec 64} {D : Addr} {n : Nat} {s : State} (h : CrS Ctx St W SP R aL tL D n s) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)),
      .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      CrS Ctx St W SP R aL tL D n s₁ ∧ CrIn Ctx St W SP R 0 tL.toNat D n s₁ := by
  obtain ⟨⟨H, t⟩, hR, hd⟩ := h
  have he := t.env
  have q₁ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have hand := and15 tL
  rw [imm_eq (by decide)] at hand
  obtain ⟨s₄, run₄, h12, hbp, hbx, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov .rbx (.mem (at_ .r15 tlenO)), .alu .and .rbx (imm 15)] s = some s₄ ∧
      s₄.gpr .r12 = D ∧ s₄.gpr .rbp = BitVec.ofNat 64 n ∧ s₄.gpr .rbx = BitVec.ofNat 64 (tL.toNat % 16) ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₄.gpr r = s.gpr r) ∧ s₄.mem = s.mem ∧ s₄.rd = s.rd ∧
      s₄.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, q₂, q₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, t.dat]
    · simp [gpr_setReg, t.len]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, t.tlen, hand]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  have he₄ : Env Ctx St W SP s₄ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  refine WP.of_runBlock ⟨s₄, run₄, ⟨⟨H, t.keep (fun r hr => ?_) hm₄ hrd₄ hwr₄⟩,
    by rw [hm₄]; exact hR, hd.of_eq hrd₄ hwr₄⟩, he₄, h12, hbp, hbx, hd.of_eq hrd₄ hwr₄, by rw [hm₄]; exact hR⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)

end

theorem cryptEntry_crS {s : State} (hp : Proof.AesGcm.streamCryptPre s) :
    WP isa (.block cryptEntry) s fun s₁ =>
      CrS (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rcx) (s.gpr .r8)
        (s.gpr .r9) (stackArg s 0).toNat s₁ ∧
      CrIn (s.gpr .rdi) (s.gpr .rdx) (stackArg s 1) (s.gpr .rsp) (s.gpr .rsi).toNat 0 (s.gpr .r8).toNat
        (s.gpr .r9) (stackArg s 0).toNat s₁ := by
  have C := CryptCtx.of hp
  refine WP.mono (cryptEntry_ok rfl rfl rfl rfl rfl rfl C.perm C.ww C.args C.dA C.rounds) fun s₁ E => ?_
  have hd := C.data.of_eq E.rd E.wr
  exact ⟨⟨⟨_, E.env, rfl, E.alen, E.tlen, E.dat, E.len, hd.ok⟩, E.rounds, hd⟩,
    E.env, E.r12, E.rbp, E.rbx, hd, E.rounds⟩

theorem stream_pub {s₀ s₀' : State} (hq : Proof.AesGcm.streamCryptPub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem streamEncrypt_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamEncryptX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamEncryptX86_64.pre s₀') (hq : Proof.AesGcm.streamEncryptX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamEncrypt v.callees) fun _ _ => True := by
  have L := (CryptCtx.of hp).lay
  have hE₂ := cryptEntry_crS hp'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := cryptEntry_crS hp
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [streamEncrypt, cryptEntry, List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₉
    (CryptCtx.of hp).args.2 (CryptCtx.of hp').args.2 ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  let CS : State → Prop := CrS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
    (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .r9) (stackArg s₀ 0).toNat
  let CI : State → Prop := CrIn (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
    (s₀.gpr .rsi).toNat 0 (s₀.gpr .r8).toNat (s₀.gpr .r9) (stackArg s₀ 0).toNat
  have c := rel_wp ((crypt_rel v L (hP := rfl)).mono (P' := fun s₁ s₂ => True ∧ (CS s₁ ∧ CI s₁) ∧ (CS s₂ ∧ CI s₂))
      (fun _ _ h => ⟨h.2.1.2, h.2.2.2⟩) fun _ _ h => h) (fun _ _ h => h.2)
    (fun s h => crypt_crS v L h.1 h.2) (fun s h => crypt_crS v L h.1 h.2)
  have hT : ∀ s, CS s →
      WP isa (textAbsorb v.callees) s (Env (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)) :=
    fun s h => WP.mono (textAbsorb_ok v L h.1.choose_spec (a := List.replicate (s₀.gpr .rcx).toNat 0)
      (c := List.replicate (s₀.gpr .r8).toNat 0) (by simp) (by simp)) fun _ h => h.1
  have t := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => textAbsorb_rel v L (H₁ := H₁) (H₂ := H₂)).mono
      (P' := fun s₁ s₂ => True ∧ CS s₁ ∧ CS s₂)
      (fun _ _ h => ⟨_, _, h.2.1.1.choose_spec, h.2.2.1.choose_spec⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hT hT
  exact (RelCT.seq c t).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamDecrypt_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.streamDecryptX86_64.pre s₀)
    (hp' : Proof.AesGcm.streamDecryptX86_64.pre s₀') (hq : Proof.AesGcm.streamDecryptX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (streamDecrypt v.callees) fun _ _ => True := by
  have L := (CryptCtx.of hp).lay
  have hE₂ := cryptEntry_crS hp'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := hq'
  simp only [Proof.AesGcm.arg] at q₈ q₉
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈, ← q₉] at hE₂
  have hE₁ := cryptEntry_crS hp
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [streamDecrypt, cryptEntry, List.append_assoc]
  refine rel_reassoc_inner3 (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rdx) (W := stackArg s₀ 1)
    (SP := s₀.gpr .rsp) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 16) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₉
    (CryptCtx.of hp).args.2 (CryptCtx.of hp').args.2 ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  have hT : ∀ s, CrS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rcx)
      (s₀.gpr .r8) (s₀.gpr .r9) (stackArg s₀ 0).toNat s →
      WP isa (textAbsorb v.callees) s (CrS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
        (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .r9) (stackArg s₀ 0).toNat) :=
    fun s h => ta_crS v L (a := List.replicate (s₀.gpr .rcx).toNat 0) (c := List.replicate (s₀.gpr .r8).toNat 0)
      (by simp) (by simp) h
  let CS : State → Prop := CrS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
    (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .r9) (stackArg s₀ 0).toNat
  let CI : State → Prop := CrIn (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
    (s₀.gpr .rsi).toNat 0 (s₀.gpr .r8).toNat (s₀.gpr .r9) (stackArg s₀ 0).toNat
  have t := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => textAbsorb_rel v L (H₁ := H₁) (H₂ := H₂)).mono
      (P' := fun s₁ s₂ => True ∧ (CS s₁ ∧ CI s₁) ∧ (CS s₂ ∧ CI s₂))
      (fun _ _ h => ⟨_, _, h.2.1.1.1.choose_spec, h.2.2.1.1.choose_spec⟩) fun _ _ h => h)
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) hT hT
  have r := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ CrS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)
      (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .r9) (stackArg s₀ 0).toNat s₁ ∧
      CrS (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rcx) (s₀.gpr .r8)
        (s₀.gpr .r9) (stackArg s₀ 0).toNat s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.2.1.1.choose_spec.env h.2.2.1.choose_spec.env)
      ⟨_, by taint_decide⟩) (fun _ _ h => h.2) (fun s h => reload_ok h) (fun s h => reload_ok h)
  have hC : ∀ s, CS s ∧ CI s →
      WP isa (crypt v.callees) s (Env (s₀.gpr .rdi) (s₀.gpr .rdx) (stackArg s₀ 1) (s₀.gpr .rsp)) :=
    fun s h => WP.mono (crypt_ok v L h.2) fun _ o => o.env
  have c := rel_wp ((crypt_rel v L (hP := rfl)).mono (P' := fun s₁ s₂ => True ∧ (CS s₁ ∧ CI s₁) ∧ (CS s₂ ∧ CI s₂))
      (fun _ _ h => ⟨h.2.1.2, h.2.2.2⟩) fun _ _ h => h) (fun _ _ h => h.2) hC hC
  exact (RelCT.seq t (RelCT.seq r c)).mono (fun _ _ h => h) fun _ _ h => h.2

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamEncryptX86_64.pre Proof.AesGcm.streamEncryptX86_64.pub
      (streamEncrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamEncrypt_rel v hp hp' hq

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.streamDecryptX86_64.pre Proof.AesGcm.streamDecryptX86_64.pub
      (streamDecrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => streamDecrypt_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
