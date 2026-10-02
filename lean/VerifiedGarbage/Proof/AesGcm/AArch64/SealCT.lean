import VerifiedGarbage.Proof.AesGcm.AArch64.OneCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry by `entry_rel`,
`j0` and the additional data by `front_rel`, the text by `encBody_rel` and
the tag by `finBody_rel`; the blocks between them by the taint analysis.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `onePre` gives, with the values of the first run. -/
structure OneFacts (σ σ₀ : State) (n : Nat) : Prop where
  ol : OneLay σ₀ n
  hW : stackArg σ 0 = stackArg σ₀ 0
  perm : Perm (σ₀.gpr .x0) (stackArg σ₀ 0 + BitVec.ofNat 64 16) (stackArg σ₀ 0) σ
  hsp : InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 0) 8
  nonceR : Covers [⟨σ₀.gpr .x2, (σ₀.gpr .x3).toNat⟩] (σ.rd ++ σ.wr)
  aadR : Covers [⟨σ₀.gpr .x4, (σ₀.gpr .x5).toNat⟩] (σ.rd ++ σ.wr)
  dataW : Covers [⟨σ₀.gpr .x6, (σ₀.gpr .x7).toNat⟩] σ.wr

theorem oneFacts {σ₁ σ₂ : State} {n : Nat} (hn : 1 ≤ n) (h₁ : onePre n σ₁) (h₂ : onePre n σ₂)
    (hq : onePub n σ₁ σ₂) : OneFacts σ₁ σ₁ n ∧ OneFacts σ₂ σ₁ n := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qw : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by omega)
  have o₁ := oneLay hn h₁
  have o₂ := oneLay hn h₂
  refine ⟨⟨o₁, rfl, o₁.perm, o₁.hsp, o₁.nonceR, o₁.aadR, o₁.dataW⟩, ⟨o₁, qw.symm, ?_, o₂.hsp, ?_, ?_, ?_⟩⟩
  · have := o₂.perm; rw [← q0, ← qw] at this; exact this
  · have := o₂.nonceR; rw [← q2, ← q3] at this; exact this
  · have := o₂.aadR; rw [← q4, ← q5] at this; exact this
  · have := o₂.dataW; rw [← q6, ← q7] at this; exact this

/-- `FrontIn` after the entry. -/
theorem frontIn_of {σ σ₀ τ : State} {n : Nat} (f : OneFacts σ σ₀ n)
    (h3 : σ.gpr .x3 = σ₀.gpr .x3) (h2 : σ.gpr .x2 = σ₀.gpr .x2) (h4 : σ.gpr .x4 = σ₀.gpr .x4)
    (h5 : σ.gpr .x5 = σ₀.gpr .x5) (h6 : σ.gpr .x6 = σ₀.gpr .x6) (h7 : σ.gpr .x7 = σ₀.gpr .x7)
    (a : Env (σ₀.gpr .x0) (stackArg σ₀ 0 + BitVec.ofNat 64 16) (stackArg σ₀ 0) σ.sp τ ∧
      τ.gpr .x22 = σ.gpr .x1 ∧ τ.gpr .x23 = σ.gpr .x2 ∧ τ.gpr .x24 = σ.gpr .x3 ∧
      τ.gpr .x26 = σ.gpr .x3 ∧ τ.gpr .x27 = 0 ∧
      τ.mem.readW (stackArg σ₀ 0 + BitVec.ofNat 64 216) 64 = σ.gpr .x4 ∧
      τ.mem.readW (stackArg σ₀ 0 + BitVec.ofNat 64 224) 64 = σ.gpr .x5 ∧
      τ.mem.readW (stackArg σ₀ 0 + BitVec.ofNat 64 232) 64 = σ.gpr .x6 ∧
      τ.mem.readW (stackArg σ₀ 0 + BitVec.ofNat 64 240) 64 = σ.gpr .x7 ∧
      Frame [entryR (stackArg σ₀ 0)] σ.mem τ.mem ∧ SavedAt τ.mem (stackArg σ₀ 0) σ ∧ τ.rd = σ.rd ∧ τ.wr = σ.wr) :
    FrontIn (σ₀.gpr .x0) (stackArg σ₀ 0 + BitVec.ofNat 64 16) (stackArg σ₀ 0) σ.sp τ.gpr (σ₀.gpr .x2)
      (σ₀.gpr .x4) (σ₀.gpr .x6) (σ₀.gpr .x3).toNat (σ₀.gpr .x5).toNat (σ₀.gpr .x7).toNat τ := by
  obtain ⟨he, _, x23, x24, x26, x27, s1, s2, s3, s4, _, _, rd, wr⟩ := a
  have sub16 : Region.Sub ⟨stackArg σ₀ 0 + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₀ 0)) := Lay.wSub (by decide)
  exact ⟨he, fun _ _ => rfl, by rw [x23, h2], by rw [x24, h3, ofNat_toNat'], by rw [x26, h3, ofNat_toNat'], x27,
    ⟨by rw [rd, wr]; exact f.nonceR, (σ₀.gpr .x3).isLt, f.ol.nw, f.ol.nonce.sub_right sub16, f.ol.nonce⟩,
    ⟨by rw [rd, wr]; exact f.aadR, (σ₀.gpr .x5).isLt, f.ol.aw, f.ol.aad.sub_right sub16, f.ol.aad⟩,
    by rw [s1, h4], by rw [s2, h5, ofNat_toNat'], by rw [s3, h6], by rw [s4, h7, ofNat_toNat']⟩

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨f₁, f₂⟩ := oneFacts (le_refl 1) h₁ h₂ hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, -⟩ := hq
  have L := f₁.ol.lay
  refine rel_seq (entry_rel f₁.hW f₂.hW f₁.hsp f₂.hsp f₁.perm.w f₂.perm.w qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (oneEntry_ok f₁.hW f₁.hsp rfl f₁.perm) (oneEntry_ok f₂.hW f₂.hsp q0.symm f₂.perm) fun τ₁ τ₂ a₁ a₂ => ?_
  have i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl a₁
  have i₂ := frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm a₂
  rw [← qsp] at i₂
  obtain ⟨_, x22₁, _, _, _, _, _, s2₁, _, s4₁, _, _, rd₁, wr₁⟩ := a₁
  obtain ⟨_, x22₂, _, _, _, _, _, s2₂, _, s4₂, _, _, rd₂, wr₂⟩ := a₂
  rw [← q1] at x22₂
  rw [← q5] at s2₂
  rw [← q7] at s4₂
  have ol := f₁.ol
  have sub16 : Region.Sub ⟨stackArg σ₁ 0 + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ 0)) := Lay.wSub (by decide)
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := ol.rounds
  have hal := (σ₁.gpr .x5).isLt
  have hn := (σ₁.gpr .x7).isLt
  refine front_rel L v i₁ i₂ fun u₁ u₂ o₁ o₂ => ?_
  have mkB : ∀ {σ τ u : State}, OneFacts σ σ₁ 1 → τ.gpr .x22 = σ₁.gpr .x1 → τ.wr = σ.wr →
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      BodyIn (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp u.gpr (σ₁.gpr .x1).toNat
        (σ₁.gpr .x7).toNat 0 (σ₁.gpr .x6) (Spec.Gcm.zeros (σ₁.gpr .x5).toNat) []
        (blockAt u.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240)) u := fun f x22 wr o =>
    ⟨o.env, fun _ _ => rfl, by rw [o.x22, x22, ofNat_toNat'], hRb, by rw [o.x25, Proof.Gcm.length_zeros],
      o.x26, o.x27, o.x28, rfl, by decide,
      ⟨⟨covers_left (by rw [o.wr, wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [o.wr, wr]; exact f.dataW, ol.cd⟩, rfl⟩
  have B₁ := mkB f₁ x22₁ wr₁ o₁
  have B₂ := mkB f₂ x22₂ wr₂ o₂
  refine rel_seq (encBody_rel L v B₁ B₂ rfl) (WP.with_rdwr (encBody_ok L v B₁ 0))
    (WP.with_rdwr (encBody_ok L v B₂ 0)) fun w₁ w₂ ⟨b₁, _, _⟩ ⟨b₂, _, _⟩ => ?_
  have sl : ∀ {σ τ u w : State}, OneFacts σ σ₁ 1 →
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      Frame (bodyFrame (stackArg σ₁ 0 + BitVec.ofNat 64 16) (stackArg σ₁ 0) (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
        u.mem w.mem → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      w.mem.readW (stackArg σ₁ 0 + BitVec.ofNat 64 d) 64 = τ.mem.readW (stackArg σ₁ 0 + BitVec.ofNat 64 d) 64 :=
    fun _ o fb d h₁ h₂ => by
      rw [slot_kept fb (slots_bodyFrame L ol.data) h₁ h₂, slot_kept o.frame (slots_frontFrame L) h₁ h₂]
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (finPrep_ok (al := (σ₁.gpr .x5).toNat) (n := (σ₁.gpr .x7).toNat) b₁.env.x19 (covers_left b₁.env.perm.w) (by rw [sl f₁ o₁ b₁.frame 224 (by decide) (by decide), s2₁,
      ofNat_toNat']) (by rw [sl f₁ o₁ b₁.frame 240 (by decide) (by decide), s4₁, ofNat_toNat']))
    (finPrep_ok (al := (σ₁.gpr .x5).toNat) (n := (σ₁.gpr .x7).toNat) b₂.env.x19 (covers_left b₂.env.perm.w) (by rw [sl f₂ o₂ b₂.frame 224 (by decide) (by decide), s2₂,
      ofNat_toNat']) (by rw [sl f₂ o₂ b₂.frame 240 (by decide) (by decide), s4₂, ofNat_toNat']))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  have y22₁ : z₁.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₁.others _ (by decide), b₁.kept .x22 (by decide), o₁.x22, x22₁, ofNat_toNat']
  have y22₂ : z₂.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₂.others _ (by decide), b₂.kept .x22 (by decide), o₂.x22, x22₂, ofNat_toNat']
  refine rel_seq (finBody_rel L v (.inl rfl) (b₁.env.of_regs r₁) (b₂.env.of_regs r₂) (fun _ _ => rfl)
      (fun _ _ => rfl) y22₁ y22₂ hRb x26₁ x26₂ x27₁ x27₂ hal hn)
    (finBody_env v L (.inl rfl) (b₁.env.of_regs r₁) (fun _ _ => rfl) y22₁ hRb x26₁ x27₁ hn)
    (finBody_env v L (.inl rfl) (b₂.env.of_regs r₂) (fun _ _ => rfl) y22₂ hRb x26₂ x27₂ hn) fun e₁ e₂ g₁ g₂ => ?_
  exact rel_taint [.x19] (by rw [g₁.1.sp, g₂.1.sp]) (by agree_tac [g₁.1.x19, g₂.1.x19]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64
