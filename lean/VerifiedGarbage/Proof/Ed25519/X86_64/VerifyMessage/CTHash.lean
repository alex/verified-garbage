import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CTAccess

/-! SHA-512's trace depends only on the input pointers and length. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (gpr_ce rsp_ce nosp_init upd_verified upd_nosp upd_depth fin_verified fin_nosp fin_depth within_base)
open VG.Proof.Sha512.X86_64 (Compress)

theorem init_ct : RelCT isa (Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block initArgs) (Two fun L _ => InitArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (initArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := Spec.Sha512.init512Api.name) (Φ := fun L _ => InitArgs L)
    (Proof.Sha512.X86_64.Stream.init_verified _).1 (Proof.Sha512.X86_64.Stream.init_verified _).2.1
    (nosp_init _) (by decide) (fun _ => initRd) initWr (fun _ _ _ _ _ hL hc ha => init_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ _ _ a₁ a₂ =>
      ((gpr_ce t₁ initRd (initWr L) (by decide)).trans a₁).trans
        ((gpr_ce t₂ initRd (initWr L) (by decide)).trans a₂).symm) init_access
  exact b.seq c

theorem upd_ct (v : Compress) (count : Lay → BitVec 64) (p : Lay → Addr) (n : Lay → BitVec 64)
    (hi : ∀ L, Input L ⟨p L, (n L).toNat⟩) :
    RelCT isa (Two fun L _ => UpdArgs L (count L) (p L) (n L))
      (.call (Spec.Sha512.updateApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee))
      (Two fun _ _ _ => True) := by
  exact two_callP (upd_verified v).1 (upd_verified v).2.1 (upd_nosp v) (upd_depth v)
    (fun L => [⟨p L, (n L).toNat⟩]) updWr
    (fun L _ _ _ _ hL hc ha => upd_pre hL hc ha (hi L))
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁⟩ := upd_regs a₁ [⟨p L, (n L).toNat⟩] (updWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂⟩ := upd_regs a₂ [⟨p L, (n L).toNat⟩] (updWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩)
    (fun L => upd_access L (p L) (n L) (hi L))

theorem finalize_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.finalize v.callee)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block finalizeArgs) (Two fun L _ => FinArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (finalizeArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := Spec.Sha512.finalizeApi.name ++ v.suffix) (Φ := fun L _ => FinArgs L)
    (fin_verified v).1 (fin_verified v).2.1 (fin_nosp v) (fin_depth v) (fun _ => []) finWr
    (fun _ _ _ _ _ hL hc ha => fin_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁'⟩ := fin_regs a₁ [] (finWr L)
      obtain ⟨d₂, s₂, x₂, c₂'⟩ := fin_regs a₂ [] (finWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩) fin_access
  exact b.seq c

theorem hash_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hash v.callee v.suffix) (Two fun _ _ _ => True) := by
  have r : RelCT isa (Two fun _ _ _ => True) (.block (prefixArgs fSignature 0))
      (Two fun L _ => UpdArgs L 0 L.sig 32) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (prefixArgs_ok hc fSignature 0 (by decide) (by decide) _ hc.pSig)
        fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have a : RelCT isa (Two fun _ _ _ => True) (.block (prefixArgs fPublicKey 32))
      (Two fun L _ => UpdArgs L 32 L.pk 32) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (prefixArgs_ok hc fPublicKey 32 (by decide) (by decide) _ hc.pPk)
        fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have m : RelCT isa (Two fun _ _ _ => True) (.block messageArgs)
      (Two fun L _ => UpdArgs L 64 L.msg L.len) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (messageArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  exact init_ct.seq ((r.seq (upd_ct v (fun _ => 0) Lay.sig (fun _ => 32)
    (fun L => ⟨L.SIG, by simp [Lay.inputs], within_base _ (by decide)⟩))).seq
    ((a.seq (upd_ct v (fun _ => 32) Lay.pk (fun _ => 32)
      (fun L => ⟨L.PK, by simp [Lay.inputs], within_base _ (by decide)⟩))).seq
    ((m.seq (upd_ct v (fun _ => 64) Lay.msg Lay.len
      (fun L => ⟨L.MSG, by simp [Lay.inputs], within_base _ (by omega)⟩))).seq (finalize_ct v))))

end VG.Proof.Ed25519.X86_64.VerifyMessage
