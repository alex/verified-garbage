import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify

/-!
# AES-GCM on AArch64: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. `work` comes from the stack;
the entry saves our caller's registers there, keeps the arguments it needs
later at `W + 216` (`oneEntry_ok`, `OneE`), and puts the state at
`W + 16` (`oneLay`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x4)).writeW (W + BitVec.ofNat 64 224) (g .x5)).writeW
    (W + BitVec.ofNat 64 232) (g .x6)).writeW (W + BitVec.ofNat 64 240) (g .x7)

/-- What the entry keeps at `W + 128`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 128⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) :
    (entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [entryR W] m (entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) := entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x4 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x5 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x6 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x7 := by
  simp only [entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

/-- After the entry. -/
theorem oneEntry_ok {s : State} {Ctx W : Addr} (hW : stackArg s 0 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8) (hCtx : s.gpr .x0 = Ctx)
    (hperm : Perm Ctx (W + BitVec.ofNat 64 16) W s) :
    WP isa (.block oneEntry) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W s.sp s' ∧
      s'.gpr .x22 = s.gpr .x1 ∧ s'.gpr .x23 = s.gpr .x2 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = 0 ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.gpr .x4 ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = s.gpr .x5 ∧
      s'.mem.readW (W + BitVec.ofNat 64 232) 64 = s.gpr .x6 ∧
      s'.mem.readW (W + BitVec.ofNat 64 240) 64 = s.gpr .x7 ∧
      Frame [entryR W] s.mem s'.mem ∧ SavedAt s'.mem W s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, run₀, x9₀, g₀, sp₀, m₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [.ldrSp .x9 0] s = some s₀ ∧
      s₀.gpr .x9 = W ∧ (∀ r, r ≠ .x9 → s₀.gpr r = s.gpr r) ∧ s₀.sp = s.sp ∧ s₀.mem = s.mem ∧
      s₀.rd = s.rd ∧ s₀.wr = s.wr := by
    refine ⟨_, by arun [hsp], ?_⟩
    refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
    rw [← hW]
    simp [gpr_write, stackArg, stackArgAddr, Mem.readW]
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := hperm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s₀ .x9 x9₀ hperm₀.w
  have w (d : Nat) (h : d + 8 ≤ 2560) := in_off hperm₀.w h (by decide)
  rw [← wr₁] at w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x22₂, x23₂, x24₂, x26₂, x27₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
        .str .x .x5 .x19 alenO, .str .x .x6 .x19 dataO, .str .x .x7 .x19 lenO, mov .x23 .x2,
        mov .x24 .x3, mov .x26 .x3, imm .x27 0] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .x21 = Ctx ∧ s₂.gpr .x22 = s.gpr .x1 ∧
      s₂.gpr .x23 = s.gpr .x2 ∧ s₂.gpr .x24 = s.gpr .x3 ∧ s₂.gpr .x26 = s.gpr .x3 ∧ s₂.gpr .x27 = 0 ∧
      s₂.sp = s₁.sp ∧
      s₂.mem = (((s₁.mem.writeW (W + BitVec.ofNat 64 216) (s.gpr .x4)).writeW (W + BitVec.ofNat 64 224)
        (s.gpr .x5)).writeW (W + BitVec.ofNat 64 232) (s.gpr .x6)).writeW (W + BitVec.ofNat 64 240) (s.gpr .x7) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have gx : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r hr => by rw [g₁, g₀ r hr]
    have x9₁ : s₁.gpr .x9 = W := by rw [g₁, x9₀]
    have w₁ := w 216 (by decide)
    have w₂ := w 224 (by decide)
    have w₃ := w 232 (by decide)
    have w₄ := w 240 (by decide)
    refine ⟨_, by arun [x9₁, BitVec.add_zero, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩
    · simp [gpr_write, x9₁]
    · simp [gpr_write, x9₁]
    · simp [gpr_write, gx .x0 (by decide), hCtx]
    · simp [gpr_write, gx .x1 (by decide)]
    · simp [gpr_write, gx .x2 (by decide)]
    · simp [gpr_write, gx .x3 (by decide)]
    · simp [gpr_write, gx .x3 (by decide)]
    · simp [gpr_write]
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, gpr_write, ite_true, ite_false, reduceCtorEq,
        gx .x4 (by decide), gx .x5 (by decide), gx .x6 (by decide), gx .x7 (by decide), x9₁]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hm : s₂.mem = entryMem s.mem W s₀.gpr := by
    rw [m₂, m₁, m₀, entryMem, g₀ .x4 (by decide), g₀ .x5 (by decide), g₀ .x6 (by decide), g₀ .x7 (by decide)]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := entryMem_slot s.mem W s₀.gpr
  rw [g₀ .x4 (by decide)] at e₁
  rw [g₀ .x5 (by decide)] at e₂
  rw [g₀ .x6 (by decide)] at e₃
  rw [g₀ .x7 (by decide)] at e₄
  refine ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁, sp₀], hperm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])⟩,
    x22₂, x23₂, x24₂, x26₂, x27₂, by rw [hm]; exact e₁, by rw [hm]; exact e₂, by rw [hm]; exact e₃,
    by rw [hm]; exact e₄, by rw [hm]; exact entryMem_frame _ _ _,
    by rw [hm]; exact entryMem_saved _ _ fun p hp => g₀ p.1 (by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [rd₂, rd₁, rd₀], by rw [wr₂, wr₁, wr₀]⟩

end VG.Proof.AesGcm.AArch64
