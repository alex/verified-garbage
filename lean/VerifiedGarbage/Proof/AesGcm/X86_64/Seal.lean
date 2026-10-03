import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot

/-!
# AES-GCM on x86-64: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. `J₀` and the additional data
(`oneAad`), the data encrypted (`oneCrypt`) and the tag of the ciphertext
(`oneTag 0`): GCM-AE (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

/-- What `seal` and `open` share: `J₀`, the additional data, and their
effects so far, from the entry. -/
structure OneMid (s₀ : State) (Ctx W SP D : Addr) (n : Nat) (H : Block) (iv a : List Byte) (mE : Mem) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H
  rounds : RoundsAt s.mem W (s₀.gpr .rsi).toNat
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = s₀.gpr .r9
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  abs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
    (a ++ zeros (padLen a.length))
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  saved : SavedAt s.mem W s₀
  frame : Frame [⟨W, 2560⟩, below SP 8] s₀.mem s.mem
  fr : Frame (wFrame W SP) mE s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem oneR_w {W SP : Addr} : ∃ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Region.Sub (oneR W) r :=
  ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

theorem wFrame_w {W SP : Addr} {m m' : Mem} (h : Frame (wFrame W SP) m m') :
    Frame [⟨W, 2560⟩, below SP 8] m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- `oneAad`, after the entry. -/
theorem oneMid_ok (v : GcmImpl) {k : Nat} {s s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hal : (s.gpr .r9).toNat = al) :
    WP isa (oneAad v.callees) s₁
      (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) s₁.mem) := by
  have L := C.lay
  have dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W], (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  have hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))]
  have hiv : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl := bytesAt_frame E.frame (dW _ _ C.nonce.w) (by have := C.nonce.lt; omega)
  have haa : bytesAt s₁.mem A al = bytesAt s.mem A al := bytesAt_frame E.frame (dW _ _ C.aad.w) (by have := C.aad.lt; omega)
  have hal' : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (WP.with_rdwr (oneAad_ok v L E.env hH₁ (by rw [E.r12, hNp])
    (by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (C.nonce.of_eq E.rd E.wr) (C.aad.of_eq E.rd E.wr)
    C.dE E.aad hal')) fun s₂ ⟨ao, hrd₂, hwr₂⟩ => ?_
  rw [hiv, haa] at ao
  have f₂ := wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) (wFrame_cons ao.frame)
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd)
      (by decide)
  refine ⟨ao.env, ao.hH, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact E.rounds.1, E.rounds.2⟩,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact E.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact E.len,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact E.alen, ao.j0, ao.abs, ao.cb,
    E.saved.frame f₂ (saved_oneFrame L C.dE), ?_, ao.frame, hrd₂.trans E.rd, hwr₂.trans E.wr⟩
  exact (E.frame.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact oneR_w).trans
    (wFrame_w ao.frame)

/-- The entry and `oneAad`. -/
theorem oneStart_ok (v : GcmImpl) {k : Nat} (hk : 3 ≤ k) {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s k Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hA : s.gpr .r8 = A) (hal : (s.gpr .r9).toNat = al)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hW : stackArg s 2 = W) :
    WP isa (.seq (.block oneEntry) (oneAad v.callees)) s fun s' => ∃ mE,
      OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) mE s' :=
  WP.seq (WP.mono (oneEntry_ok hk C hCtx hSP hA hD hn hW) fun s₁ E =>
    WP.mono (oneMid_ok v C E hNp hnl hal) fun _ h => ⟨s₁.mem, h⟩)

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

/-- `vg_aes_gcm_seal`. -/
theorem seal_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.sealX86_64.pre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  have C := OneCtx.of hp
  generalize hCtx : s.gpr .rdi = Ctx at *
  generalize hSP : s.gpr .rsp = SP at *
  generalize hNp : s.gpr .rdx = Np at *
  generalize hnl : (s.gpr .rcx).toNat = nl at *
  generalize hA : s.gpr .r8 = A at *
  generalize hal : (s.gpr .r9).toNat = al at *
  generalize hD : stackArg s 0 = D at *
  generalize hn : (stackArg s 1).toNat = n at *
  generalize hW : stackArg s 2 = W at *
  have L := C.lay
  generalize hR : (s.gpr .rsi).toNat = R at *
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq_assoc (WP.seq (WP.mono (oneStart_ok v (k := 3) (Nat.le_refl _) C hCtx hSP hNp hnl hA hal hD hn hW)
    fun s₂ ⟨_, M⟩ => ?_))
  generalize hH : ctxH s.mem Ctx = H at M
  generalize hiv : bytesAt s.mem Np nl = iv at M
  generalize ha : bytesAt s.mem A al = a at M
  have hRo : RoundsAt s₂.mem W R := hR ▸ M.rounds
  have hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq M.rd M.wr
  refine WP.seq (WP.mono (oneCrypt_ok v L (icb := inc32 (Spec.Gcm.j0 H iv)) M.env hRo M.dat M.len hd₂)
    fun s₃ ⟨co, hrd₃, hwr₃⟩ => ?_)
  have hctr₂ : Ctr s₂.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 64)
      (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) 0 := ⟨M.cb, fun h => absurd rfl h⟩
  have kp : ∀ {m m' : Mem}, Frame (oneFrame W D SP n) m m' → ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L C.dE hd)
      (by decide)
  have f₃ := crFrame_one co.frame
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide))), M.hH]
  have hal₂ : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hal₃ : a.length = al := by rw [← ha, length_bytesAt]
  have hd₃ : DataOk (W + BitVec.ofNat 64 16) W SP s₃ D n := hd₂.ok.of_eq hrd₃ hwr₃
  refine WP.seq (WP.mono (oneTag_ok v L (o := 0) (.inl rfl) co.env hH₃ co.rounds
    (by rw [kp f₃ 200 (.inl ⟨by decide, by decide⟩)]; exact M.dat)
    (by rw [kp f₃ 208 (.inl ⟨by decide, by decide⟩)]; exact M.len)
    (by rw [kp f₃ 184 (.inl ⟨by decide, by decide⟩)]; exact hal₂) hal₃ hd₃ C.dE C.data.ctx)
    fun s₄ ⟨he₄, f₄, hrd₄, hwr₄, _, hq⟩ => ?_)
  have hsv₄ : SavedAt s₄.mem W s :=
    (M.saved.frame co.frame (saved_crFrame L hd₂)).frame (wFrame_one (D := D) (n := n) (o := 0) (.inl rfl) f₄) (saved_oneFrame L C.dE)
  have dRw : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact ret_below SP
  have hret : s₄.mem.readW SP 64 = s.mem.readW SP 64 := by
    rw [ret_kept f₄ dRw, ret_kept co.frame (fun r hr => ?_), ret_kept M.frame (fun r hr => ?_)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact C.rW
      · exact ret_below SP
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact C.rD
      · rw [add_ofNat_assoc]; exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact ret_below SP
  refine WP.mono (exit_ok he₄.r15 (by rw [he₄.rsp, hSP]) (covers_left he₄.perm.w) hsv₄ (by rw [hSP, hret]))
    fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  -- The memory of the parts.
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₂ : ciphOf s₂.mem Ctx R = ctxCiph s.mem Ctx R :=
    ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
  have hp₂ : bytesAt s₂.mem D n = bytesAt s.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by have := C.data.ok.lt; omega)
  have hc₃ : bytesAt s₃.mem D n = gctr (ctxCiph s.mem Ctx R) (inc32 (Spec.Gcm.j0 H iv)) (bytesAt s.mem D n) := by
    rw [co.out hctr₂, hc₂, hp₂, Proof.Gcm.gctr_eq]
  have dDw : ∀ r ∈ (⟨W + BitVec.ofNat 64 0, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.dE.sub_right (Lay.wSub (by decide))
    · exact C.data.ok.stk.symm
  have hd₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D n := bytesAt_frame f₄ dDw (by have := C.data.ok.lt; omega)
  have dSc : ∀ d k, d + k ≤ 48 → ∀ r ∈ crFrame (W + BitVec.ofNat 64 16) W SP D n,
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hd₂.ok.st.sub_right (Lay.stSub (by omega))).symm
    · exact L.st_st (.inl (by omega)) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have habs₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length)) := by
    have hl := Nat.mod_lt (a ++ zeros (padLen a.length)).length (show 16 > 0 by decide)
    exact M.abs.congr (blockAt_frame co.frame (dSc 16 16 (by decide)))
      (bytesAt_frame co.frame (dSc 32 _ (by omega)) (by omega))
  have hJ₃ : blockAt s₃.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv := by
    rw [← M.j0]; simpa using blockAt_frame co.frame (dSc 0 16 (by decide))
  have hT := hq habs₃
  rw [hJ₃, ciph_frame co.frame (ctx_crFrame L hd₂) hR', hc₂, hc₃, show W + BitVec.ofNat 64 0 = W from BitVec.add_zero W] at hT
  simp only [Proof.AesGcm.sealX86_64, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hW, hR, hH, hiv, ha, Spec.Gcm.encryptWith, hm, hT, hd₄, hc₃,
    Proof.Gcm.fullTag_eq, Proof.Gcm.length_gctr, length_bytesAt]
  simp only [Prod.mk.injEq, true_and]
  rw [List.take_of_length_le (by rw [Cmac.toBytes_length])]

end VG.Proof.AesGcm.X86_64
