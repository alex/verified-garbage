import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# AES-GCM on x86-64: what every function does

Untrusted: everything here is checked by Lean. Each function saves our
caller's `rbx, rbp, r12–r15` at `W + 128` (`save_ok`) and restores them
(`restore_ok`); the pieces it runs in between never write there.

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- Code never changes the permissions. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', e, q⟩ := h; exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (W : Addr) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

/-- The saved registers' slots. -/
abbrev savedR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 48⟩

theorem save_ok (s : State) (b : Reg) {W : Addr} (hb : s.gpr b = W) (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa (save b) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      SavedAt s'.mem W s ∧ Frame [savedR W] s.mem s'.mem := by
  have w₁ := in_off hw (show 128 + 8 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hw (show 136 + 8 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hw (show 144 + 8 ≤ 2560 by decide) (by decide)
  have w₄ := in_off hw (show 152 + 8 ≤ 2560 by decide) (by decide)
  have w₅ := in_off hw (show 160 + 8 ≤ 2560 by decide) (by decide)
  have w₆ := in_off hw (show 168 + 8 ≤ 2560 by decide) (by decide)
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have s128_136 := sep 128 136 (by decide) (by decide) (by decide)
  have s128_144 := sep 128 144 (by decide) (by decide) (by decide)
  have s128_152 := sep 128 152 (by decide) (by decide) (by decide)
  have s128_160 := sep 128 160 (by decide) (by decide) (by decide)
  have s128_168 := sep 128 168 (by decide) (by decide) (by decide)
  have s136_144 := sep 136 144 (by decide) (by decide) (by decide)
  have s136_152 := sep 136 152 (by decide) (by decide) (by decide)
  have s136_160 := sep 136 160 (by decide) (by decide) (by decide)
  have s136_168 := sep 136 168 (by decide) (by decide) (by decide)
  have s144_152 := sep 144 152 (by decide) (by decide) (by decide)
  have s144_160 := sep 144 160 (by decide) (by decide) (by decide)
  have s144_168 := sep 144 168 (by decide) (by decide) (by decide)
  have s152_160 := sep 152 160 (by decide) (by decide) (by decide)
  have s152_168 := sep 152 168 (by decide) (by decide) (by decide)
  have s160_168 := sep 160 168 (by decide) (by decide) (by decide)
  refine ⟨_, by simp only [save, saved, List.map]; xrun [hb, w₁, w₂, w₃, w₄, w₅, w₆], ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 3
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := first | decide | assumption) only [hb, Mem.readW_writeW_self64, Mem.readW_writeW_sep]
  · have c : ∀ d, 128 ≤ d → d + 8 ≤ 176 → (savedR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [hb]
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 136 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 144 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 152 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 160 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 168 (by decide) (by decide))
  all_goals rfl

theorem restore_ok (s : State) {W : Addr} (h15 : s.gpr .r15 = W) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr))
    {s₀ : State} (hs : SavedAt s.mem W s₀) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧
      (∀ r, r ∉ saved.map (·.1) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₁ := in_off hr (show 128 + 8 ≤ 2560 by decide) (by decide)
  have r₂ := in_off hr (show 136 + 8 ≤ 2560 by decide) (by decide)
  have r₃ := in_off hr (show 144 + 8 ≤ 2560 by decide) (by decide)
  have r₄ := in_off hr (show 152 + 8 ≤ 2560 by decide) (by decide)
  have r₅ := in_off hr (show 160 + 8 ≤ 2560 by decide) (by decide)
  have r₆ := in_off hr (show 168 + 8 ≤ 2560 by decide) (by decide)
  have e₁ := hs (.rbx, 128) (by simp [saved])
  have e₂ := hs (.rbp, 136) (by simp [saved])
  have e₃ := hs (.r12, 144) (by simp [saved])
  have e₄ := hs (.r13, 152) (by simp [saved])
  have e₅ := hs (.r14, 160) (by simp [saved])
  have e₆ := hs (.r15, 168) (by simp [saved])
  simp only at e₁ e₂ e₃ e₄ e₅ e₆
  refine ⟨_, by simp only [restore, saved, List.map]; xrun [h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, h15, e₁, e₂, e₃, e₄, e₅, e₆]
  · intro r hr
    simp only [saved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g⟩ := hr
    simp [gpr_setReg, a, b, c, d, f, g]
  all_goals rfl

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {W : Addr} {s₀ : State} (h : SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR W).Disjoint r) : SavedAt m' W s₀ := by
  intro p hp
  have hp' := hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hs : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ (savedR W) := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Offset.sub _ (by decide) (by decide)
  rw [hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

theorem ret_below (SP : Addr) : (⟨SP, 8⟩ : Region).Disjoint (below SP 8) :=
  Offset.base_disjoint_below SP (n := 8) (k := 8) (by decide)

/-- The return address stays where it is, outside a frame. -/
theorem ret_kept {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {SP : Addr}
    (hd : ∀ r ∈ rs, (⟨SP, 8⟩ : Region).Disjoint r) : m'.readW SP 64 = m.readW SP 64 :=
  hf.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) hd (by decide)

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : Addr} (h15 : s.gpr .r15 = W) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem W s₀)
    (hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .rax = s.gpr .rax := by
  obtain ⟨s', run, hsv, hother, hm, -, -⟩ := restore_ok s h15 hr hs
  refine WP.of_runBlock ⟨s', run, ⟨fun r hr => ?_, by rw [hm, hret]⟩, hm, hother .rax (by simp [saved])⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.rbx, 128) (by simp [saved])
  · exact hsv (.rbp, 136) (by simp [saved])
  · rw [hother .rsp (by simp [saved]), hsp]
  · exact hsv (.r12, 144) (by simp [saved])
  · exact hsv (.r13, 152) (by simp [saved])
  · exact hsv (.r14, 160) (by simp [saved])
  · exact hsv (.r15, 168) (by simp [saved])

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ absFrame St W SP yo, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ tFrame St W SP yo, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame St W SP o, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by omega)) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_j0Frame : ∀ r ∈ j0Frame St W SP, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) :
    ∀ r ∈ crFrame St W SP D n, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

end

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- The layout, from disjointness of the context, the state, `W` and the stack. -/
theorem Lay.of {Ctx St W SP : Addr} (cw : Ctx.toNat + 256 ≤ 2 ^ 64) (sw : St.toNat + 80 ≤ 2 ^ 64)
    (ww : W.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨Ctx, 256⟩ : Region).Disjoint ⟨St, 80⟩)
    (cW : (⟨Ctx, 256⟩ : Region).Disjoint ⟨W, 2560⟩) (sW : (⟨St, 80⟩ : Region).Disjoint ⟨W, 2560⟩)
    (kc : (below SP 8).Disjoint ⟨Ctx, 256⟩) (ks : (below SP 8).Disjoint ⟨St, 80⟩)
    (kw : (below SP 8).Disjoint ⟨W, 2560⟩) : Lay Ctx St W SP :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    kc, ks, kw⟩

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl


end VG.Proof.AesGcm.X86_64
