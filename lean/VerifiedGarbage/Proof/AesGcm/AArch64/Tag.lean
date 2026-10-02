import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt

/-!
# AES-GCM on AArch64: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `x26` and `x27` bytes (`lensSeg_ok`, `lensCall_ok`), copies the
accumulator `S` to `W + o` (`tagSeg_ok`) and XORs `CIPH_K(J₀)` into it with
`vg_aes_ctr32`, from the counter block `J₀` at the state (`tagCall_ok`);
`tag_ok` puts them together.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (St W : Addr) (o : Nat) : List Region :=
  [⟨St, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]

/-- Before the call of `tag o`: the accumulator `Y` copied to `W + o`, `J` at
the state. -/
structure Tag1 (Ctx St W SP : Addr) (k : Reg → BitVec 64) (o R : Nat) (Y J : Block) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  call : CtrCall s Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1
  cp : blockAt s.mem (W + BitVec.ofNat 64 o) = Y
  hJ : blockAt s.mem St = J
  frame : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] m₀ s.mem

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (after the
lengths block) and the counter block `J`. -/
structure TagOut (Ctx St W SP : Addr) (k : Reg → BitVec 64) (o R : Nat) (Y J : Block) (m₀ : Mem) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  kept : Kept k s
  out : bytesAt s.mem (W + BitVec.ofNat 64 o) 16 = toBytes (Y ^^^ ciphOf m₀ Ctx R J)
  frame : Frame (tagFrame St W o) m₀ s.mem

theorem bytesAt_copy2 (m : Mem) {p q : Addr} (hd : (⟨p, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    bytesAt ((m.writeW p (m.readW q 64)).writeW (p + BitVec.ofNat 64 8)
      ((m.writeW p (m.readW q 64)).readW (q + BitVec.ofNat 64 8) 64)) p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep (Region.Disjoint.sep hd.symm (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide), Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- The accumulator copied, and the arguments of the call. -/
theorem tagSeg_ok {k : Reg → BitVec 64} {o R : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env Ctx St W SP s)
    (hk : Kept k s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.block (tagSeg o)) s (Tag1 Ctx St W SP k o R (blockAt s.mem (St + BitVec.ofNat 64 16))
      (blockAt s.mem St) s.mem) := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have r₁ := he.perm.stR (show 16 + 8 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 24 + 8 ≤ 80 by decide)
  have w₁ := he.perm.wW (show o + 8 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show o + 8 + 8 ≤ 2560 by omega)
  have ho8 : (o + 8) % 8 = 0 ∧ o + 8 < 32768 := by omega
  have ho0 : o % 8 = 0 ∧ o < 32768 := by omega
  have ho' : o < 4096 := by omega
  have dsep : (⟨W + BitVec.ofNat 64 o, 8⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8, 8⟩ := by
    rw [add_ofNat_assoc]
    exact (L.st_w (a := 24) (n := 8) (by decide) (by omega)).symm
  obtain ⟨s₁, run₁, m₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, og, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (tagSeg o) s = some s₁ ∧
      s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 o) (s.mem.readW (St + BitVec.ofNat 64 16) 64)).writeW
        (W + BitVec.ofNat 64 (o + 8))
        ((s.mem.writeW (W + BitVec.ofNat 64 o) (s.mem.readW (St + BitVec.ofNat 64 16) 64)).readW
          (St + BitVec.ofNat 64 24) 64) ∧
      s₁.gpr .x0 = Ctx ∧ s₁.gpr .x1 = BitVec.ofNat 64 R ∧ s₁.gpr .x2 = St ∧
      s₁.gpr .x3 = W + BitVec.ofNat 64 o ∧ s₁.gpr .x4 = BitVec.ofNat 64 1 ∧
      s₁.gpr .x5 = W + BitVec.ofNat 64 512 ∧ Others [.x9, .x0, .x1, .x2, .x3, .x4, .x5] s s₁ ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [tagSeg]; arun [he.x19, he.x20, r₁, r₂, w₁, w₂, ho8, ho0, ho'], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write, Mem.writeW, Mem.readW, BitVec.setWidth_eq]
    · simp [gpr_write, he.x21]
    · simp [gpr_write, h22]
    · simp [gpr_write, he.x20]
    · simp [gpr_write, he.x19]
    · simp [gpr_write]
    · simp [gpr_write, he.x19]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => og r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  rw [show W + BitVec.ofNat 64 (o + 8) = W + BitVec.ofNat 64 o + BitVec.ofNat 64 8 from (add_ofNat_assoc ..).symm,
    show St + BitVec.ofNat 64 24 = St + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc]] at m₁
  have f₁ : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have dJo : (⟨St, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  refine ⟨he₁, hk.of_others og, ?_, ?_, ?_, f₁⟩
  · refine ⟨x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, hR,
      by have := L.ww; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, by decide,
      by simpa using (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (d := 0) (n := 16) (by decide)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      dJo, by simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩),
      L.w_w (by omega) (by omega) (by decide), ?_, ?_⟩
    · refine covers_cons ?_ (covers_cons ?_ (covers_cons (covers_left (he₁.perm.wC (by omega)))
        (covers_left (he₁.perm.wC (by decide)))))
      · exact fun a m' ⟨r, hr, hc'⟩ => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he₁.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
      · simpa using covers_left (he₁.perm.stC (d := 0) (n := 16) (by decide))
    · exact covers_cons (by simpa using he₁.perm.stC (d := 0) (n := 16) (by decide))
        (covers_cons (he₁.perm.wC (by omega)) (he₁.perm.wC (by decide)))
  · rw [blockAt, m₁, bytesAt_copy2 _ dsep]; rfl
  · exact blockAt_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo

/-- The call of `tag o`: `CIPH_K(J)` XORed into the copy. -/
theorem tagCall_ok (v : GcmImpl) {k : Reg → BitVec 64} {o R : Nat} (ho : o = 0 ∨ o = 112) {Y J : Block}
    {m₀ : Mem} {s : State} (h : Tag1 Ctx St W SP k o R Y J m₀ s) :
    WP isa (ctrCall v.callees) s (TagOut Ctx St W SP k o R Y J m₀) := by
  refine WP.mono (ctr_call v.ctr h.call) fun s₃ g => ?_
  have gout := g.out
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  have hc : ciphOf s.mem Ctx R = ciphOf m₀ Ctx R :=
    ciph_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) h.call.rounds
  refine ⟨h.env.of_saved g.saved g.sp g.rd g.wr, h.kept.of_saved g.saved, ?_, ?_⟩
  · rw [Proof.Cmac.bytesAt_blockAt, gout.1, h.hJ, h.cp,
      show Spec.Gcm.aesWith R (bytesAt s.mem Ctx (16 * (R + 1))) = ciphOf s.mem Ctx R from rfl, hc]
  · refine (h.frame.sub fun r hr => ?_).trans (g.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Region.sub_prefix (base := St) (show 16 ≤ 32 by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok (v : GcmImpl) {k : Reg → BitVec 64} {o o' R : Nat} (ho : o = 0 ∨ o = 112) {s : State}
    (he : Env Ctx St W SP s) (hk : Kept k s) (h22 : s.gpr .x22 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h25 : s.gpr .x25 = BitVec.ofNat 64 o') :
    WP isa (tag v.callees o) s (TagOut Ctx St W SP k o R
      (ghashFrom (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (blockAt s.mem (St + BitVec.ofNat 64 16))
        [ofBytes (lensBlock (s.gpr .x26).toNat (s.gpr .x27).toNat)]) (blockAt s.mem St) s.mem) := by
  refine WP.seq (WP.seq (WP.mono (lensSeg_ok L (yo := 16) (.inr rfl) he hk h25 (by decide)) fun s₁ h₁ =>
    WP.mono (lensCall_ok L (.inr rfl) v h₁) fun s₂ h₂ => ?_))
  have dJ : ∀ r ∈ tFrame St W 16, (⟨St, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using L.st_st (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
  have hJ₂ : blockAt s₂.mem St = blockAt s.mem St := blockAt_frame h₂.frame dJ
  have hc₂ : ciphOf s₂.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame h₂.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))) hR
  have hk₂ := h₂.kept
  refine WP.seq (WP.mono (tagSeg_ok L ho h₂.env h₂.kept (by rw [hk₂ .x22 (by decide), ← hk .x22 (by decide), h22]) hR)
    fun s₃ h₃ => WP.mono (tagCall_ok L v ho h₃) fun s₄ h₄ => ?_)
  refine ⟨h₄.env, h₄.kept, ?_, ?_⟩
  · rw [h₄.out, hc₂, hJ₂, h₂.out]
  · refine (h₂.frame.sub fun r hr => ?_).trans (h₄.frame.sub fun r hr => ⟨r, hr, fun _ h => h⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base St (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩

end

end VG.Proof.AesGcm.AArch64
