import VerifiedGarbage.Proof.AesGcm.Arm.J0

/-!
# AES-GCM on ARMv7: what every function does

Untrusted: everything here is checked by Lean. Each function saves our
caller's `r4`–`r11` and `lr` at `W + 128` (`save_ok`) and restores them
(`restore_ok`, `exit_ok`); the pieces it runs in between never write there.

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.MdStream.Arm (saveMem saveList_ok readW_writeW_save)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', e, q⟩ := h
  obtain ⟨-, hw, -⟩ := Exec.rdwr e
  exact ⟨t, s', e, q, (Exec.rdwr e).1, hw, Exec.sp e⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (w : BitVec 32) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (State.addr w + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- The saved registers' slots. -/
abbrev savedR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 128, 36⟩

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 164 := by decide

theorem saveMem_frame_off (m : Mem) (B : Addr) (g : Reg → BitVec 32) {lo L : Nat} (hL : lo + L < 2 ^ 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, lo ≤ p.2 ∧ p.2 + 4 ≤ lo + L) →
      Frame [⟨B + BitVec.ofNat 64 lo, L⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ h.1 (by omega) (by omega))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

set_option simprocs false in
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (saveMem m B g saved).readW (B + BitVec.ofNat 64 d) 32 = g r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-- Saving the registers at `b + 128`, where `b` holds `W`. -/
theorem save_ok {s : State} {b : Reg} {w : BitVec 32} (hb : s.gpr b = w) (hfit : w.toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr w, 2560⟩] s.wr) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → SavedAt s'.mem w s →
      Frame [savedR w] s.mem s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  refine saveList_ok (b := b) saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · have hbd := saved_bound p hp
    rw [hb]
    exact ⟨by omega, by omega, in_off hw (by omega) (by decide)⟩
  · intro p hp
    rw [m, hb]; exact saveMem_slot _ _ _ hp
  · rw [m, hb]; exact saveMem_frame_off _ _ _ (by decide) saved fun p hp => saved_bound p hp

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {w : BitVec 32} {s₀ : State} (h : SavedAt m w s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR w).Disjoint r) : SavedAt m' w s₀ := by
  intro p hp
  have hb := saved_bound p hp
  have hs : Region.Sub ⟨State.addr w + BitVec.ofNat 64 p.2, 4⟩ (savedR w) := Offset.sub _ hb.1 (by omega)
  rw [hf.readW (r := ⟨State.addr w + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

/-- The end of every function: our caller's registers restored. -/
theorem restore_ok {s s₀ : State} {w : BitVec 32} (h11 : s.gpr .r11 = w) (hfit : w.toNat + 2560 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr w, 2560⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem w s₀) (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hA : ∀ d, d < 2560 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₁ := in_off hr (show 128 + 4 ≤ 2560 by decide) (by decide)
  have r₂ := in_off hr (show 132 + 4 ≤ 2560 by decide) (by decide)
  have r₃ := in_off hr (show 136 + 4 ≤ 2560 by decide) (by decide)
  have r₄ := in_off hr (show 140 + 4 ≤ 2560 by decide) (by decide)
  have r₅ := in_off hr (show 144 + 4 ≤ 2560 by decide) (by decide)
  have r₆ := in_off hr (show 148 + 4 ≤ 2560 by decide) (by decide)
  have r₇ := in_off hr (show 152 + 4 ≤ 2560 by decide) (by decide)
  have r₈ := in_off hr (show 156 + 4 ≤ 2560 by decide) (by decide)
  have r₉ := in_off hr (show 160 + 4 ≤ 2560 by decide) (by decide)
  have e : ∀ p ∈ saved, s.mem.readW (State.addr w + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := hs
  have e₁ := e (.r4, 128) (by simp [saved]); have e₂ := e (.r5, 132) (by simp [saved])
  have e₃ := e (.r6, 136) (by simp [saved]); have e₄ := e (.r7, 140) (by simp [saved])
  have e₅ := e (.r8, 144) (by simp [saved]); have e₆ := e (.r9, 148) (by simp [saved])
  have e₇ := e (.r10, 152) (by simp [saved]); have e₈ := e (.r11, 156) (by simp [saved])
  have e₉ := e (.lr, 160) (by simp [saved])
  simp only at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  refine WP.of_runBlock ⟨_, by simp only [restore, restored, List.map]; arun [h11, hA, r₁, r₂, r₃, r₄, r₅, r₆, r₇,
    r₈, r₉], ⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]
  all_goals first | rfl | simp [gpr_setReg, sp_setReg, mem_setReg, rd_setReg, wr_setReg, hsp]

/-- The layout, from disjointness of the context, the state, `W` and the stack. -/
theorem Lay.of {c st w sp : BitVec 32} (cw : c.toNat + 256 ≤ 2 ^ 32) (sw : st.toNat + 80 ≤ 2 ^ 32)
    (ww : w.toNat + 2560 ≤ 2 ^ 32) (sp8 : 8 ≤ sp.toNat) (cs : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr st, 80⟩)
    (cW : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (sW : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (kc : (below sp).Disjoint ⟨State.addr c, 256⟩) (ks : (below sp).Disjoint ⟨State.addr st, 80⟩)
    (kw : (below sp).Disjoint ⟨State.addr w, 2560⟩) : Lay c st w sp :=
  ⟨cw, sw, ww, sp8, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    kc, ks, kw⟩

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ absFrame st w sp yo, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ tFrame st w sp yo, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame st w sp o, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by decide) (by omega)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_j0Frame : ∀ r ∈ j0Frame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_crFrame {c k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n) :
    ∀ r ∈ crFrame st w sp D n, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

end

end VG.Proof.AesGcm.Arm
