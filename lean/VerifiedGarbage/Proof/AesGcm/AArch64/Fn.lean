import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract

/-!
# AES-GCM on AArch64: what every function uses

Untrusted: everything here is checked by Lean. The postconditions quantify
over what the state represents (the nonce, the additional data, the text so
far), which the code never looks at: each function runs the same for all of
them, so one run satisfies each instance of its proof (`WP.forall_det`). The
pieces never write the saved registers (`saved_absFrame`, …), and `flush` of
no bytes changes no accumulator (`flush0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- The layout, from disjointness of the context, the state and `W`. -/
theorem Lay.of {Ctx St W : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 2560⟩) :
    Lay Ctx St W :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide))⟩

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ absFrame St W yo, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ tFrame St W yo, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame St W o, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_j0Frame : ∀ r ∈ j0Frame St W, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W s D n) :
    ∀ r ∈ crFrame St W D n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_cmp : ∀ r ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)], (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact L.w_w (.inl (by decide)) (by decide) (by decide)

theorem saved_tag16 : ∀ r ∈ [(⟨W, 16⟩ : Region)], (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simpa using L.w_w (a := 128) (n := 88) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)

/-- `flush` of no bytes: the accumulator as it was. -/
theorem flush0_ok (v : GcmImpl) {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {k : Reg → BitVec 64} {s : State}
    (he : Env Ctx St W SP s) (hk : Kept k s) (h25 : s.gpr .x25 = BitVec.ofNat 64 0) :
    WP isa (flush v.callees yo) s (TOut Ctx St W SP k yo 0 (blockAt s.mem (St + BitVec.ofNat 64 yo)) s.mem) := by
  refine WP.seq (WP.mono (padSeg_ok L hyo (P := St + BitVec.ofNat 64 32) he hk h25 (by decide)
    (by refine ⟨_, by arun [], ?_⟩; exact ⟨by simp [gpr_write, he.x20], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩)
    (covers_left (he.perm.stC (by omega))) (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))) fun s₁ h₁ => ?_)
  refine WP.mono (padCall_ok L hyo v h₁) fun s₂ h₂ => { h₂ with out := ?_ }
  rw [h₂.out]; rfl

end

end VG.Proof.AesGcm.AArch64
