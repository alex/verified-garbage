import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp

/-!
# AES-GCM on x86-64: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. A tag length §5.2.1.2 does
not allow gives 0. Any other: `J₀` and the additional data (`oneAad`), the
tag of the ciphertext (`oneTag 112`), the received tag padded (`recv`) and
compared (`cmp 112`), and only if they match the data decrypted (`oneCrypt`):
GCM-AD (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 zeros padLen ghashFrom ghash blocks
  ofBytes toBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `OneEntry`, after code that writes only the tag length's slot. -/
theorem OneEntry.keep {s₀ s s' : State} {A D : Addr} {n : Nat} (E : OneEntry s₀ Ctx W SP A D n s)
    (hg : ∀ r ∈ [Reg.r12, .rbp, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneEntry s₀ Ctx W SP A D n s' := by
  have kp : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h h' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) h' (by decide)) (by decide)
  refine ⟨E.env.keep (fun r hr => ?_) hrd hwr, ⟨by rw [kp 176 (.inl (by decide)) (by decide)]; exact E.rounds.1,
    E.rounds.2⟩, by rw [kp 232 (.inr (by decide)) (by decide)]; exact E.aad,
    by rw [kp 184 (.inl (by decide)) (by decide)]; exact E.alen, by rw [kp 200 (.inl (by decide)) (by decide)]; exact E.dat,
    by rw [kp 208 (.inl (by decide)) (by decide)]; exact E.len, by rw [hg _ (by simp)]; exact E.r12,
    by rw [hg _ (by simp)]; exact E.rbp, by rw [hg _ (by simp)]; exact E.rsp,
    E.saved.frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
    E.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩), hrd.trans E.rd, hwr.trans E.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by simp)

end

/-- The entry of `open`, and the tag length kept at `W + 224`. -/
theorem openEntry_ok {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (hCtx : s.gpr .rdi = Ctx) (hSP : s.gpr .rsp = SP) (hA : s.gpr .r8 = A)
    (hD : stackArg s 0 = D) (hn : (stackArg s 1).toNat = n) (hW : stackArg s 2 = W) :
    WP isa (.block (oneEntry ++ ([.mov .rbx (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rbx] : List Instr))) s fun s₁ =>
      OneEntry s Ctx W SP A D n s₁ ∧ s₁.gpr .rbx = stackArg s 3 ∧
      s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = stackArg s 3 ∧ Frame [oneR W] s.mem s₁.mem := by
  have L := C.lay
  refine WP.block_append (WP.mono (oneEntry_ok (by decide) C hCtx hSP hA hD hn hW) fun s₁ E => ?_)
  have a₃ : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [E.rd, E.wr]; exact C.args 3 (by omega)
  have ht : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = stackArg s 3 := by
    rw [E.frame.readW (r := ⟨SP + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hs : Region.Sub ⟨SP + BitVec.ofNat 64 32, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 4⟩ := by
        rw [show (32 : Nat) = 8 + 24 by rfl, ← add_ofNat_assoc]; exact Offset.sub_base _ (by decide)
      exact (C.dA.sub_left hs).sub_right (Lay.wSub (by decide))) (by decide), ← hSP]
    rfl
  have w₁ := E.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hbx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rbx (.mem (at_ .rsp 32)),
      .store (at_ .r15 tlO) .rbx] s₁ = some s₂ ∧ s₂.gpr .rbx = stackArg s 3 ∧ (∀ r, r ≠ .rbx → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 224) (stackArg s 3) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by xrun [E.rsp, E.env.r15, a₃, w₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, ht]
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, ht]
    all_goals rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₂, run₂, E.keep L (fun r hr => hg₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hrd₂ hwr₂ f₂, hbx₂,
    by rw [hm₂, Mem.readW_writeW_self64], ?_⟩
  exact E.frame.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
theorem ite_ofNat (p : Prop) [Decidable p] :
    (if p then 1 else 0 : BitVec 64) = BitVec.ofNat 64 (if p then 1 else 0) := by split <;> rfl

/-- After the comparison, from `s`: `k` is 1 if the tag of the ciphertext `T`
matches the received one, and 0 if not, in ZF and at `W + 216`. -/
structure OpenMid (Ctx W SP : Addr) (J : Block) (k : Nat) (s s' : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s'
  frame : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cb : blockAt s'.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J
  zf : s'.zf = some (decide (k = 0))
  aux : s'.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k

/-- After `oneAad`: the tag of the ciphertext, compared with the received one. -/
theorem openCheckA_ok {R t : Nat} {D : Addr} {n al : Nat} {H J : Block} {a : List Byte} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) (ha : a.length = al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (habs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length)))
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J)
    (hcb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J) :
    WP isa (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
      (.seq recv
      (.seq (cmp uO)
        (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))) s
      (OpenMid Ctx W SP J (if (toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
        [ofBytes (lensBlock a.length n)] ^^^ ciphOf s.mem Ctx R J)).take t = bytesAt s.mem W t then 1 else 0) s) := by
  have hlt := hd.ok.lt
  have hR' := hR.2
  -- The tag.
  refine WP.seq (WP.mono (oneTag_ok v L (o := 112) (.inr rfl) he hH hR hdat hlen hal ha hd.ok hDW hd.ctx)
    fun s₃ ⟨he₃, f₃, hrd₃, hwr₃, hcb₃, hq⟩ => ?_)
  have hT₃ := hq habs
  rw [hj] at hT₃
  generalize hT : toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
    [ofBytes (lensBlock a.length n)] ^^^ ciphOf s.mem Ctx R J) = T at hT₃ ⊢
  have f₃' := wFrame_one (D := D) (n := n) (.inr rfl) f₃
  have kp₃ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => f₃'.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd')
      (by decide)
  have dW16 : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨W, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have e0 : W + BitVec.ofNat 64 0 = W := BitVec.add_zero W
    have w0 : ∀ d k, 16 ≤ d → d + k ≤ 2560 → (⟨W, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
      fun d k h₁ h₂ => by
        have h := L.w_w (a := 0) (n := 16) (d := d) (k := k) (.inl h₁) (by decide) h₂
        rw [e0] at h; exact h
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact w0 112 16 (by decide) (by decide)
    · exact w0 16 112 (by decide) (by decide)
    · exact w0 216 8 (by decide) (by decide)
    · exact w0 240 2320 (by decide) (by decide)
    · have h := (L.stk_w (a := 0) (n := 16) (by decide)).symm
      rw [e0] at h; exact h
  have hW₃ : bytesAt s₃.mem W t = bytesAt s.mem W t := by
    rw [bytesAt_take _ _ h16, bytesAt_take s.mem _ h16, bytesAt_frame f₃ dW16 (by decide)]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [kp₃ 224 (.inr ⟨by decide, by decide⟩)]; exact htl
  have q₁ := he₃.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₄, run₄, hbx₄, hg₄, hm₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO))] s₃ = some s₄ ∧
      s₄.gpr .rbx = BitVec.ofNat 64 t ∧ (∀ r, r ≠ .rbx → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr := by
    refine ⟨_, by xrun [he₃.r15, q₁], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, htl₃]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hrd₄ hwr₄
  -- The received tag, padded.
  refine WP.seq (WP.mono (WP.with_rdwr (recv_ok L he₄ hbx₄ h1 h16)) fun s₅ ⟨⟨he₅, hr₅, f₅, hbx₅⟩, hrd₅, hwr₅⟩ => ?_)
  rw [hbx₄] at hbx₅
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L (o := 112) (.inr rfl) he₅ hbx₅ h1 h16 (length_bytesAt _ _ _) hr₅))
    fun s₆ ⟨⟨he₆, hax₆, f₆⟩, hrd₆, hwr₆⟩ => ?_)
  have d256 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hU : bytesAt s₅.mem (W + BitVec.ofNat 64 112) t = T.take t := by
    rw [bytesAt_take _ _ h16, bytesAt_frame f₅ d256 (by decide), hm₄, hT₃]
  rw [hU, hm₄, hW₃, ite_ofNat] at hax₆
  generalize hk : (if T.take t = bytesAt s.mem W t then 1 else 0) = k at hax₆
  have hk1 : k < 2 ^ 64 := by rw [← hk]; split <;> decide
  -- The result kept at `W + 216`.
  have w₇ := he₆.perm.wW (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₇, run₇, hz₇, hg₇, hm₇, hrd₇, hwr₇⟩ : ∃ s₇, runBlock isa [.store (at_ .r15 auxO) .rax,
      .alu .test .rax (.reg .rax)] s₆ = some s₇ ∧ s₇.zf = some (decide (k = 0)) ∧ (∀ r, s₇.gpr r = s₆.gpr r) ∧
      s₇.mem = s₆.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧ s₇.rd = s₆.rd ∧ s₇.wr = s₆.wr := by
    refine ⟨_, by xrun [he₆.r15, w₇], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hax₆, mem_setReg]
      exact congrArg some (and_self_beq hk1)
    · intro r; simp [gpr_arithFlags, gpr_setReg]
    · simp [mem_arithFlags, mem_setReg, hax₆]
    all_goals simp [rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have he₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₇ := he₆.keep (fun r _ => hg₇ r) hrd₇ hwr₇
  have g₇ : Frame [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 256, 16⟩]
      s₃.mem s₇.mem := by
    have g₅ := f₅.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    have g₆ := f₆.mono (rs' := [⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
      ⟨W + BitVec.ofNat 64 256, 16⟩]) fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
    rw [hm₄] at g₅
    rw [hm₇]
    exact (g₅.trans g₆).writeW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  have f₇ : Frame (wFrame W SP) s₃.mem s₇.mem := g₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_wFrame (.inr (.inl ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
    · exact w_wFrame (.inr (.inr ⟨by decide, by decide⟩))
  have F₇ : Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem s₇.mem := f₃.trans (wFrame_cons f₇)
  have hcb₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J := by
    rw [blockAt_frame g₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [add_ofNat_assoc]
      rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)), hcb₃, hcb]
  have hrd₇' : s₇.rd = s.rd := hrd₇.trans (hrd₆.trans (hrd₅.trans (hrd₄.trans hrd₃)))
  have hwr₇' : s₇.wr = s.wr := hwr₇.trans (hwr₆.trans (hwr₅.trans (hwr₄.trans hwr₃)))
  have hax₇ : s₇.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [hm₇, Mem.readW_writeW_self64]
  subst hk hT
  exact ⟨he₇, F₇, hrd₇', hwr₇', hcb₇, hz₇, hax₇⟩

/-- After `oneAad`: the tag of the ciphertext, compared with the received
one, and the data decrypted if they match. -/
theorem openCheck_ok {R t : Nat} {D : Addr} {n al : Nat} {H J : Block} {a : List Byte} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (hR : RoundsAt s.mem W R) (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) (ha : a.length = al)
    (htl : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ t) (h16 : t ≤ 16)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (habs : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length)))
    (hj : blockAt s.mem (W + BitVec.ofNat 64 16) = J)
    (hcb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 J) :
    WP isa (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))])
      (.seq recv
      (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (.block []) (oneCrypt v.callees))
        (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (oneFrame W D SP n) s.mem s'.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧
      let T := toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
        [ofBytes (lensBlock a.length n)] ^^^ ciphOf s.mem Ctx R J)
      s'.gpr .rax = BitVec.ofNat 64 (if T.take t = bytesAt s.mem W t then 1 else 0) ∧
      bytesAt s'.mem D n = if T.take t = bytesAt s.mem W t then xorKs (ciphOf s.mem Ctx R) (inc32 J) 0 (bytesAt s.mem D n)
        else bytesAt s.mem D n := by
  have hlt := hd.ok.lt
  have hR' := hR.2
  refine WP.seq5 (openCheckA_ok v L he hH hR hdat hlen hal ha htl h1 h16 hd hDW habs hj hcb) fun s₇ M => ?_
  generalize hT : toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
    [ofBytes (lensBlock a.length n)] ^^^ ciphOf s.mem Ctx R J) = T at M ⊢
  generalize hk : (if T.take t = bytesAt s.mem W t then 1 else 0) = k at M
  have he₇ := M.env
  have F₇ := M.frame
  have hcb₇ := M.cb
  have hz₇ := M.zf
  have hax₇ := M.aux
  have hrd₇' := M.rd
  have hwr₇' := M.wr
  have F₇' := wFrame_one (D := D) (n := n) (.inr rfl) F₇
  have kp₇ : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd' => F₇'.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd')
      (by decide)
  have hR₇ : RoundsAt s₇.mem W R := ⟨by rw [kp₇ 176 (.inl ⟨by decide, by decide⟩)]; exact hR.1, hR'⟩
  have hd₇ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₇ D n := hd.of_eq hrd₇' hwr₇'
  have hdat₇ : s₇.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by
    rw [kp₇ 200 (.inl ⟨by decide, by decide⟩)]; exact hdat
  have hlen₇ : s₇.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by
    rw [kp₇ 208 (.inl ⟨by decide, by decide⟩)]; exact hlen
  -- Decrypted only if the tags match.
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ ∧
      Frame (oneFrame W D SP n) s₇.mem s₈.mem ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr ∧
      s₈.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      bytesAt s₈.mem D n = if k = 0 then bytesAt s₇.mem D n
        else xorKs (ciphOf s₇.mem Ctx R) (inc32 J) 0 (bytesAt s₇.mem D n))
    (WP.ite (decide (k = 0)) (eval_e hz₇) (fun ht => ?_) (fun hf => ?_)) fun s₈ h₈ => ?_)
  · have h0 : k = 0 := by simpa using ht
    exact WP.block_nil ⟨he₇, Frame.refl _ _, rfl, rfl, hax₇, by simp [h0]⟩
  · have h0 : k ≠ 0 := by simpa using hf
    refine WP.mono (oneCrypt_ok v L (icb := inc32 J) he₇ hR₇ hdat₇ hlen₇ hd₇) fun s₈ ⟨co, hrd₈, hwr₈⟩ =>
      ⟨co.env, crFrame_one co.frame, hrd₈, hwr₈, ?_, ?_⟩
    · rw [co.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), hax₇]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hDW.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (a := 48) (n := 32) (d := 216) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm
    · simp only [h0, ↓reduceIte]
      exact co.out ⟨hcb₇, fun h => absurd rfl h⟩
  obtain ⟨he₈, f₈, hrd₈, hwr₈, hax₈, hD₈⟩ := h₈
  have q₉ := he₈.perm.wR (show 216 + 8 ≤ 2560 by decide)
  refine WP.run (Q := fun s₉ => s₉.gpr .rax = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rax → s₉.gpr r = s₈.gpr r) ∧
      s₉.mem = s₈.mem ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr)
    ⟨_, by xrun [he₈.r15, q₉], by simp [gpr_setReg, hax₈], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
    fun s₉ ⟨hax₉, hg₉, hm₉, hrd₉, hwr₉⟩ => ?_
  have dC : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm
  have dD : ∀ r ∈ (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP), (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hDW.sub_right (Lay.wSub (by decide))
    · exact hDW.sub_right (Lay.wSub (by decide))
    · exact hDW.sub_right (Lay.wSub (by decide))
    · exact hDW.sub_right (Lay.wSub (by decide))
    · exact hd.ok.stk.symm
  have hc₇ : ciphOf s₇.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame F₇ dC hR'
  have hp₇ : bytesAt s₇.mem D n = bytesAt s.mem D n := bytesAt_frame F₇ dD (by omega)
  refine ⟨he₈.keep (fun r hr => hg₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₉ hwr₉, by rw [hm₉]; exact F₇'.trans f₈,
    by rw [hrd₉, hrd₈, hrd₇'], by rw [hwr₉, hwr₈, hwr₇'], by rw [hax₉, hk], ?_⟩
  rw [hm₉, hD₈, hc₇, hp₇]
  by_cases hc : T.take t = bytesAt s.mem W t
  · simp only [hc, ↓reduceIte] at hk ⊢; subst hk; simp
  · simp only [hc, ↓reduceIte] at hk ⊢; subst hk; simp

end

/-- The result of `open`, from the parts. -/
abbrev OpenRes (ciph : Block → Block) (H : Block) (t : Nat) (iv c a tag : List Byte) (D : Addr) (n : Nat)
    (s : State) : Prop :=
  match Spec.Gcm.openResult ciph H t iv c a tag with
  | some pt => s.gpr .rax = 1 ∧ bytesAt s.mem D n = pt
  | none => s.gpr .rax = 0 ∧ bytesAt s.mem D n = c

/-- `vg_aes_gcm_open`. -/
theorem open_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.openX86_64.pre s) :
    WP isa («open» v.callees) s fun s' => gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
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
  refine WP.seq (WP.mono (openEntry_ok C hCtx hSP hA hD hn hW) fun s₁ ⟨E, hbx₁, htl₁, fE⟩ => ?_)
  generalize ht : (stackArg s 3).toNat = t
  have hbx₁' : s₁.gpr .rbx = BitVec.ofNat 64 t := by rw [hbx₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₁' : s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [htl₁, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (tagLenOk_ok s₁ hbx₁' (ht ▸ (stackArg s 3).isLt)) fun s₂ ⟨hz₂, k₂⟩ => ?_)
  have E₂ : OneEntry s Ctx W SP A D n s₂ := E.keep L (fun r hr => k₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k₂.rd k₂.wr (by rw [k₂.mem]; exact Frame.refl _ _)
  have dR : ∀ r ∈ [oneR W], (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.rW.sub_right (Lay.wSub (by decide))
  have dDR : ∀ r ∈ [oneR W], (⟨D, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))
  have dWR : ∀ r ∈ [oneR W], (⟨W, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hlt := C.data.ok.lt
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ ∧ SavedAt s₅.mem W s ∧
      s₅.mem.readW SP 64 = s.mem.readW SP 64 ∧
      OpenRes (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) t (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al)
        (bytesAt s.mem W t) D n s₅)
    (WP.ite (!Spec.Gcm.tagLenOk t) (eval_e hz₂) (fun hbad => ?_) (fun hok => ?_)) fun s₅ h₅ => ?_)
  · -- A length §5.2.1.2 does not allow.
    have hbad' : Spec.Gcm.tagLenOk t = false := by simpa using hbad
    refine WP.run (Q := fun s₅ => s₅.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → s₅.gpr r = s₂.gpr r) ∧ s₅.mem = s₂.mem ∧
        s₅.rd = s₂.rd ∧ s₅.wr = s₂.wr)
      ⟨_, by xrun [], by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], by rfl, by rfl, by rfl⟩
      fun s₅ ⟨hax, hg₅, hm₅, hrd₅, hwr₅⟩ => ?_
    refine ⟨E₂.env.keep (fun r hr => hg₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₅ hwr₅, by rw [hm₅]; exact E₂.saved, ?_, ?_⟩
    · rw [hm₅, k₂.mem, ret_kept fE dR]
    · simp only [OpenRes, Spec.Gcm.openResult, hbad', Bool.false_eq_true, ↓reduceIte]
      exact ⟨hax, by rw [hm₅, k₂.mem, bytesAt_frame fE dDR (by omega)]⟩
  · -- An allowed length.
    have hok' : Spec.Gcm.tagLenOk t = true := by simpa using hok
    have hb : 1 ≤ t ∧ t ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok'
      omega
    refine WP.seq (WP.mono (oneMid_ok v C E₂ hNp hnl hal) fun s₃ M => ?_)
    generalize hH : ctxH s.mem Ctx = H at M
    generalize hiv : bytesAt s.mem Np nl = iv at M
    generalize ha : bytesAt s.mem A al = a at M
    have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
      rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hal' : a.length = al := by rw [← ha, length_bytesAt]
    have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
      rw [M.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w (by decide)).symm) (by decide), k₂.mem, htl₁']
    refine WP.mono (openCheck_ok v L M.env M.hH (hR ▸ M.rounds) M.dat M.len hal₃ hal' htl₃ hb.1 hb.2
      (C.data.of_eq M.rd M.wr) C.dE M.abs M.j0 M.cb) fun s₄ ⟨he₄, f₄, _, _, hax₄, hD₄⟩ => ?_
    -- From the entry to `s₃`.
    have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
        ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
      intro p k h₁ h₂ r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.symm
    have hc₃ : ciphOf s₃.mem Ctx R = ctxCiph s.mem Ctx R := ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
    have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
      bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by omega)
    have hw₃ : bytesAt s₃.mem W t = bytesAt s.mem W t := by
      rw [bytesAt_take _ _ hb.2, bytesAt_take s.mem _ hb.2, bytesAt_frame M.fr (fun r hr => ?_) (by decide), k₂.mem,
        bytesAt_frame fE dWR (by decide)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (a := 0) (n := 16) (by decide)).symm.sub_left
          (by simpa using Region.sub_prefix (base := W) (show 16 ≤ 16 by decide))
    have dRet : ∀ r ∈ oneFrame W D SP n, (⟨SP, 8⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact C.rW.sub_right (Region.sub_prefix (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rW.sub_right (Lay.wSub (by decide))
      · exact C.rD
      · exact ret_below SP
    refine ⟨he₄, M.saved.frame f₄ (saved_oneFrame L C.dE), ?_, ?_⟩
    · rw [ret_kept f₄ dRet, ret_kept M.frame (fun r hr => ?_)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact C.rW
      · exact ret_below SP
    · rw [hc₃, hp₃, hw₃] at hax₄
      rw [hc₃, hp₃, hw₃, ← Proof.Gcm.gctr_eq] at hD₄
      simp only [OpenRes, Spec.Gcm.openResult, hok', ↓reduceIte, Spec.Gcm.decryptWith,
        Proof.Gcm.fullTag_eq, length_bytesAt, ← Proof.Gcm.gctr_eq]
      split at hax₄
      · next e => simp only [e, ↓reduceIte] at hD₄ ⊢; exact ⟨hax₄, hD₄⟩
      · next e => simp only [e, ↓reduceIte] at hD₄ ⊢; exact ⟨hax₄, hD₄⟩
  obtain ⟨he₅, hsv₅, hret₅, hres⟩ := h₅
  refine WP.mono (exit_ok he₅.r15 (by rw [he₅.rsp, hSP]) (covers_left he₅.perm.w) hsv₅ (by rw [hSP, hret₅]))
    fun s' ⟨hg, hm, hax⟩ => ⟨hg, ?_⟩
  simp only [Proof.AesGcm.openX86_64, Proof.AesGcm.arg]
  rw [hCtx, hNp, hnl, hA, hal, hD, hn, hW, hR, ht]
  simp only [OpenRes] at hres
  split
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩
  · next h => rw [h] at hres; exact ⟨by rw [hax, hres.1]; rfl, by rw [hm]; exact hres.2⟩

end VG.Proof.AesGcm.X86_64
