import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# AES-GCM on AArch64: saving and restoring our caller's registers

Untrusted: everything here is checked by Lean. Each function saves `x19`–`x28`
and `x30` at `W + 128` (`save_ok`) and restores them (`restore_ok`,
`exit_ok`); the pieces it runs in between never write there (`SavedAt.frame`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64

/-- The memory after saving the registers `g` at `W + 128`. -/
def savedMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (W + BitVec.ofNat 64 d) (g r)) m

/-- The saved registers' slots. -/
abbrev savedR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 88⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (W : Addr) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

theorem save_ok (s : State) (b : Reg) {W : Addr} (hb : s.gpr b = W) (hw : Covers [⟨W, 2560⟩] s.wr) :
    ∃ s', runBlock isa (save b) s = some s' ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = savedMem s.mem W s.gpr := by
  have w (d : Nat) (h : d + 8 ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 := in_off hw h (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [save, saved, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some, hb,
      w 128 (by decide), w 136 (by decide), w 144 (by decide), w 152 (by decide), w 160 (by decide),
      w 168 (by decide), w 176 (by decide), w 184 (by decide), w 192 (by decide), w 200 (by decide),
      w 208 (by decide)]
    rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) : SavedAt (savedMem m W g) W ⟨g, 0, false,
    fun _ => 0, m, [], [], fun _ => 0⟩ := by
  intro p h
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [savedMem, saved, List.foldl]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem SavedAt.of_gpr {m : Mem} {W : Addr} {s₀ s₁ : State} (h : SavedAt m W s₀) (hg : s₁.gpr = s₀.gpr) :
    SavedAt m W s₁ := fun p hp => by rw [h p hp, hg]

theorem savedAt_save (m : Mem) (W : Addr) (s₀ : State) : SavedAt (savedMem m W s₀.gpr) W s₀ :=
  (savedMem_slot m W s₀.gpr).of_gpr rfl

theorem slot_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 216) :
    (savedR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [savedR W] m (savedMem m W g) := by
  simp only [savedMem, saved, List.foldl]
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 216) := slot_contains W h₁ h₂
  exact (((((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 136 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 144 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 152 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 160 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 168 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 176 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 192 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 200 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 208 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {W : Addr} {s₀ : State} (h : SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR W).Disjoint r) : SavedAt m' W s₀ := by
  intro p hp
  have hp' := hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hs : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ (savedR W) := by
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Offset.sub _ (by decide) (by decide)
  rw [hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

theorem restore_ok (s : State) {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (W + BitVec.ofNat 64 p.2) 64) ∧
      (∀ r, r ∉ saved.map (·.1) → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r (d : Nat) (h : d + 8 ≤ 2560) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_off hr h (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, h19,
      r 128 (by decide), r 136 (by decide), r 144 (by decide), r 152 (by decide), r 160 (by decide),
      r 168 (by decide), r 176 (by decide), r 184 (by decide), r 192 (by decide), r 200 (by decide),
      r 208 (by decide)]
    rfl, ?_⟩
  refine ⟨fun p h => ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_write, Mem.readW]
  · simp only [saved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp [gpr_write, h]

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : Addr} (h19 : s.gpr .x19 = W) (hsp : s.sp = s₀.sp)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem W s₀) :
    WP isa (.block restore) s fun s' => GprAbi s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .x0 = s.gpr .x0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, hsv, hother, sp', hm, rd', wr'⟩ := restore_ok s h19 hr
  refine WP.of_runBlock ⟨s', run, ⟨fun r hr' => ?_, by rw [sp', hsp]⟩, hm, hother .x0 (by decide), rd', wr'⟩
  have hin : r ∈ saved.map (·.1) := (by decide : ∀ r ∈ preserved, r ∈ saved.map (·.1)) r hr'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hin
  rw [hsv p hp, hs p hp]

end VG.Proof.AesGcm.AArch64
