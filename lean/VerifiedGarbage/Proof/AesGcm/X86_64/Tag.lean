import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt

/-!
# AES-GCM on x86-64: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `rbx` and `rbp` bytes, copies the accumulator `S` to `W + o` and
XORs `CIPH_K(J₀)` into it with `vg_aes_ctr32`, from the counter block `J₀`
at the state (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W SP : Addr) (o : Nat) : List Region :=
  [⟨St, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩,
    below SP 8]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (Ctx St W SP : Addr) (o R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  out : bytesAt s.mem (W + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ Ctx R J)
  frame : Frame (tagFrame St W SP o) m₀ s.mem

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

omit L in
theorem ctr32_single (ciph : Block → Block) (icb x : Block) : Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

omit L in
theorem bytesAt_copy2 (m : Mem) {p q : Addr} (hd : (⟨p, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    bytesAt ((m.writeW p (m.readW q 64)).writeW (p + BitVec.ofNat 64 8)
      ((m.writeW p (m.readW q 64)).readW (q + BitVec.ofNat 64 8) 64)) p 16 = bytesAt m q 16 := by
  rw [Cmac.bytesAt_store2, Mem.readW_writeW_sep (Region.Disjoint.sep hd.symm (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide), Cmac.le8_readW, Cmac.le8_readW, ← Cmac.bytesAt_split]

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env Ctx St W SP s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hR : RoundsAt s.mem W R) (hJ : blockAt s.mem St = J) :
    WP isa (tag v.callees o) s (TagOut Ctx St W SP o R H (blockAt s.mem (St + BitVec.ofNat 64 16)) J
      (s.gpr .rbx).toNat (s.gpr .rbp).toNat s.mem) := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  refine WP.seq (WP.mono (lens_ok v L (yo := 16) (.inr rfl) he hH) fun s₁ ⟨he₁, hH₁, hY₁, f₁⟩ => ?_)
  have h13 := he₁.r13; have h14 := he₁.r14; have h15 := he₁.r15
  have dJ : ∀ r ∈ tFrame St W SP 16, (⟨St, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  have hJ₁ : blockAt s₁.mem St = J := by rw [blockAt_frame f₁ dJ, hJ]
  have hR₁ : RoundsAt s₁.mem W R := rounds_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w (by decide)).symm) hR
  have hc₁ : ciphOf s₁.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm) hR.2
  have r₁ := he₁.perm.stR (show 16 + 8 ≤ 80 by decide)
  have r₂ := he₁.perm.stR (show 24 + 8 ≤ 80 by decide)
  have r₃ := he₁.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have w₁ := he₁.perm.wW (show o + 8 ≤ 2560 by omega)
  have w₂ := he₁.perm.wW (show o + 8 + 8 ≤ 2560 by omega)
  have dsep : (⟨W + BitVec.ofNat 64 o, 8⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8, 8⟩ := by
    rw [add_ofNat_assoc]
    exact (L.st_w (a := 24) (n := 8) (by decide) (by omega)).symm
  obtain ⟨s₂, run₂, hm₂, hdi, hsi, hdx, hcx, h8, h9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)),
        .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)),
        .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++ ptr .r9 .r15 scrO) s₁ = some s₂ ∧
      s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 o) (s₁.mem.readW (St + BitVec.ofNat 64 16) 64)).writeW
        (W + BitVec.ofNat 64 o + BitVec.ofNat 64 8)
        ((s₁.mem.writeW (W + BitVec.ofNat 64 o) (s₁.mem.readW (St + BitVec.ofNat 64 16) 64)).readW
          (St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) 64) ∧
      s₂.gpr .rdi = Ctx ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = St ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 o ∧ s₂.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₂.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s₂.gpr r = s₁.gpr r) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have hsep : ∀ (m : Mem) (x y : BitVec 64), ((m.writeW (W + BitVec.ofNat 64 o) x).writeW
        (W + BitVec.ofNat 64 (o + 8)) y).readW (W + BitVec.ofNat 64 176) 64 = m.readW (W + BitVec.ofNat 64 176) 64 := by
      intro m x y
      rw [Mem.readW_writeW_sep (Region.Disjoint.sep (L.w_w (a := 176) (n := 8) (d := o + 8) (k := 8) (by omega)
          (by decide) (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
        Mem.readW_writeW_sep (Region.Disjoint.sep (L.w_w (a := 176) (n := 8) (d := o) (k := 8) (by omega)
          (by decide) (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    have e24 : St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 = St + BitVec.ofNat 64 24 := add_ofNat_assoc ..
    have eo : W + BitVec.ofNat 64 o + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (o + 8) := add_ofNat_assoc ..
    rw [e24, eo]
    refine ⟨_, by xrun [h13, h14, h15, r₁, r₂, r₃, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hsep, hR₁.1]
    · simp [gpr_setReg, h14]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r a b c d e f g; simp [gpr_setReg, a, b, c, d, e, f, g]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hk := he₂.rsp
  have f₂ : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s₁.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (W + BitVec.ofNat 64 o) 16 = bytesAt s₁.mem (St + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, bytesAt_copy2 _ dsep]
  have dJo : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem St = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, hJ₁]
  have hc₂ : ciphOf s₂.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) hR.2, hc₁]
  have hR₂ : RoundsAt s₂.mem W R := rounds_frame f₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by decide) (by omega)) hR₁
  have hS : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  have hcall : CtrCall s₂ Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1 := by
    refine ⟨hdi, hsi, hdx, hcx, h8, h9, hR.2, by have := L.ww; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
      by simpa using (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      dJo, hS, L.w_w (by omega) (by omega) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
    · rw [hk]; simpa using L.stk_st (a := 0) (n := 16) (by decide)
    · rw [hk]; exact L.stk_w (by omega)
    · rw [hk]; exact L.stk_w (by decide)
    · refine covers_cons ?_ (covers_cons ?_ (covers_cons (covers_left (he₂.perm.wC (by omega)))
        (covers_left (he₂.perm.wC (by decide)))))
      · exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₂.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · simpa using covers_left (he₂.perm.stC (d := 0) (n := 16) (by decide))
    · exact covers_cons (by simpa using he₂.perm.stC (d := 0) (n := 16) (by decide))
        (covers_cons (he₂.perm.wC (by omega)) (he₂.perm.wC (by decide)))
  refine WP.mono (ctr_call v.ctr hcall) fun s₃ g => ?_
  have gout := g.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  refine ⟨he₂.of_saved g.saved g.rd g.wr, ?_, ?_, ?_⟩
  · refine rounds_frame g.frame (fun r hr => ?_) hR₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using (L.st_w (a := 0) (n := 16) (d := 176) (k := 8) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact L.w_w (by omega) (by decide) (by omega)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [hk]; exact (L.stk_w (by decide)).symm
  · rw [Cmac.bytesAt_blockAt, gout.1, hJ₂,
      show Spec.Gcm.aesWith R (bytesAt s₂.mem Ctx (16 * (R + 1))) = ciphOf s₂.mem Ctx R from rfl, hc₂]
    congr 2
    rw [blockAt, hT, ← blockAt, hY₁]
  · have fA : Frame (tagFrame St W SP o) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    refine (fA.trans (f₂.sub fun r hr => ?_)).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Region.sub_prefix (base := St) (show 16 ≤ 32 by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · rw [hk]; exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.AesGcm.X86_64
