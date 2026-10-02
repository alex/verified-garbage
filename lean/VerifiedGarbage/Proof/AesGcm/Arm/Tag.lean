import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk

/-!
# AES-GCM on ARMv7: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `r5:r4` and `r7:r6` bytes, copies the accumulator `S` to `W + o`
and XORs `CIPH_K(J₀)` into it with `vg_aes_ctr32`, from the counter block
`J₀` at the state (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)
open VG.Proof.Cmac (store4)

/-- The regions `tag o` writes. -/
abbrev tagFrame (st w sp : BitVec 32) (o : Nat) : List Region :=
  [⟨State.addr st, 32⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 o, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (c st w sp k7 k8 : BitVec 32) (o R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  out : bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ (State.addr c) R J)
  frame : Frame (tagFrame st w sp o) m₀ s.mem

/-- After the lengths block: what the arguments of the call need. -/
structure TagMid (c st w sp k7 k8 : BitVec 32) (R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 16) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  hJ : blockAt s.mem (State.addr st) = J
  hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R
  frame : Frame (Proof.AesGcm.Arm.tFrame st w sp 16) m₀ s.mem

theorem bytesAt_copy4 (m : Mem) (p q : Addr) :
    bytesAt (store4 m p (m.readW q 32) (m.readW (q + BitVec.ofNat 64 4) 32) (m.readW (q + BitVec.ofNat 64 8) 32)
      (m.readW (q + BitVec.ofNat 64 12) 32)) p 16 = bytesAt m q 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← Cmac.bytesAt_split4]

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- The lengths block absorbed, before the copy. -/
theorem tagLens_ok {R : Nat} {H J : Block} {s : State} (he : Env c st w sp k7 k8 s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (State.addr st) = J) :
    WP isa (lens 16) s (TagMid c st w sp k7 k8 R H (blockAt s.mem (State.addr st + BitVec.ofNat 64 16)) J
      (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat s.mem) := by
  refine WP.mono (lens_ok L (yo := 16) (.inr rfl) he hH) fun s₁ ⟨he₁, _, hY₁, f₁⟩ => ?_
  have dJ : ∀ r ∈ Proof.AesGcm.Arm.tFrame st w sp 16, (⟨State.addr st, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
        (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  refine ⟨he₁, hY₁, by rw [blockAt_frame f₁ dJ, hJ], ciph_frame f₁ (fun r hr => ?_) hR, f₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem sepW {m : Mem} {a b : Addr} {v : BitVec 32} (h : (⟨a, 4⟩ : Region).Disjoint ⟨b, 4⟩) :
    (m.writeW b v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (h.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32`. -/
theorem tagArgs_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa (tagArgs o) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 o) (s.mem.readW (State.addr st + BitVec.ofNat 64 16) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 16 + BitVec.ofNat 64 4) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 16 + BitVec.ofNat 64 12) 32) ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = k8 ∧ s'.gpr .r2 = st ∧ s'.gpr .r3 = w + BitVec.ofNat 32 o ∧
      s'.gpr .r12 = BitVec.ofNat 32 1 ∧ s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h8 := he.r8; have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have r₀ := he.perm.stR (show 16 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 20 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 24 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 28 + 4 ≤ 80 by decide)
  have w₀ := he.perm.wW (show o + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show o + 4 + 4 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show o + 8 + 4 ≤ 2560 by omega)
  have w₃ := he.perm.wW (show o + 12 + 4 ≤ 2560 by omega)
  have q : ∀ a d, a + 4 ≤ 80 → d + 4 ≤ o + 16 → o ≤ d →
      (⟨State.addr st + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ h₃ => L.st_w h₁ (by omega)
  have o₀ : o < 4096 := by omega
  have o₁ : o + 4 < 4096 := by omega
  have o₂ : o + 8 < 4096 := by omega
  have o₃ : o + 12 < 4096 := by omega
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  have e₁ := L.wA (d := o) (by omega)
  have e₂ := L.wA (d := o + 4) (by omega)
  have e₃ := L.wA (d := o + 8) (by omega)
  have e₄ := L.wA (d := o + 12) (by omega)
  have p₁ := fun m v => sepW (m := m) (v := v) (q 20 o (by decide) (by omega) (by omega))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 24 o (by decide) (by omega) (by omega))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 24 (o + 4) (by decide) (by omega) (by omega))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 28 o (by decide) (by omega) (by omega))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 28 (o + 4) (by decide) (by omega) (by omega))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 28 (o + 8) (by decide) (by omega) (by omega))
  refine ⟨_, by simp only [tagArgs]; arun [h10, h11, L.stA, e₁, e₂, e₃, e₄, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂,
    o₃, eo, p₁, p₂, p₃, p₄, p₅, p₆], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h11]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

/-- The copy and the call of `vg_aes_ctr32` on it. -/
theorem tagCall_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H Y J : Block} {aLen cLen : Nat} {m₀ : Mem} {s : State}
    (h : TagMid c st w sp k7 k8 R H Y J aLen cLen m₀ s) (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.seq (.block (tagArgs o)) ctrFrame) s (TagOut c st w sp k7 k8 o R H Y J aLen cLen m₀) := by
  have he := h.env
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  obtain ⟨s₂, run₂, hm₂, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tagArgs_ok L ho he
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂
  have hk := he₂.sp
  have eT := L.wA (d := o) (by omega)
  have eS := L.wA (d := 512) (by decide)
  have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 o, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hT : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 o) 16 = bytesAt s.mem (State.addr st + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, bytesAt_copy4]
  have dJo : (⟨State.addr st, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem (State.addr st) = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, h.hJ]
  have hc₂ : ciphOf s₂.mem (State.addr c) R = ciphOf m₀ (State.addr c) R := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) hR, h.hc]
  have hS : (⟨State.addr st, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  have hcall : CtrCall s₂ c st (w + BitVec.ofNat 32 o) (w + BitVec.ofNat 32 512) R 1 := by
    refine ⟨h0, by rw [h1, h8], h2, h3, h12, hlr, hR, by rw [hk]; exact L.sp8, by have := L.cw; omega,
      by have := L.sw; omega, by rw [L.wN (by omega)]; have := L.ww; omega, by rw [L.wN (by decide)]; have := L.ww; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [eT, eS, hk]
    · exact L.cs.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Region.sub_prefix (by decide))
    · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))
    · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
    · simpa using dJo
    · exact hS
    · simpa using Lay.w_w (w := w) (a := o) (n := 16) (d := 512) (k := 2048) (by omega) (by omega) (by decide)
    · exact L.kc.sub_right (Region.sub_prefix (by decide))
    · simpa using L.stk_st (a := 0) (n := 16) (by decide)
    · simpa using L.stk_w (a := o) (n := 16) (by omega)
    · exact L.stk_w (by decide)
    · exact covers_prefix he₂.perm.ctx (by decide)
    · exact covers_cons (covers_prefix he₂.perm.st (by decide))
        (covers_cons (he₂.perm.wC (by omega)) (he₂.perm.wC (by decide)))
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gframe := g.frame
  simp only [eT, eS, hk] at gout gframe
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_⟩
  · rw [Cmac.bytesAt_blockAt, gout.1, hJ₂,
      show Spec.Gcm.aesWith R (bytesAt s₂.mem (State.addr c) (16 * (R + 1))) = ciphOf s₂.mem (State.addr c) R from rfl,
      hc₂, show blockAt s₂.mem (State.addr w + BitVec.ofNat 64 o) = blockAt s.mem (State.addr st + BitVec.ofNat 64 16)
        by rw [blockAt, blockAt, hT], h.hY]
  · have fA : Frame (tagFrame st w sp o) m₀ s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (State.addr st) (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    refine (fA.trans (f₂.sub fun r hr => ?_)).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env c st w sp k7 k8 s)
    (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (State.addr st) = J) :
    WP isa (tag o) s (TagOut c st w sp k7 k8 o R H (blockAt s.mem (State.addr st + BitVec.ofNat 64 16)) J
      (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat s.mem) :=
  WP.seq (WP.mono (tagLens_ok L he hR hH hJ) fun _ hm => tagCall_ok L ho hm h8 hR)

end

end VG.Proof.AesGcm.Arm
