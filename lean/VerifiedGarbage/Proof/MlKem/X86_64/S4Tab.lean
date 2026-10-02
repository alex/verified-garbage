import VerifiedGarbage.Proof.MlKem.X86_64.S4Parse

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the table

After the squeezes, the code writes the table of the sampling and the
constants of the vector code over the states, quadword by quadword (`tab_ok`);
with the output of the squeezes, which it does not touch, they make `PInv σ 0`
(`pinv0_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.Sha3.X86_64 (wp_movi64 wp_store wp_nil)

/-- During the writes of the table, from `s₀`. -/
structure TabInv (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨at' σ 0, 2240⟩] s₀.mem s.mem
  tab : ∀ i < n, s.mem.readW (at' σ (8 * i)) 64 = tabQ i

theorem tab_step {σ : State} (hp : Pre σ) {s₀ : State} (he : Env σ s₀) {i : Nat} (hi : i < 280) {s : State}
    (h : TabInv σ s₀ i s) :
    WP isa (.block [.movImm64 .rax (tabQ i), .store (at_ .rbx (8 * i)) .rax]) s (TabInv σ s₀ (i + 1)) := by
  have hbx : s.gpr .rbx = scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_store (a := at' σ (8 * i)) (by rw [ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.wr, h.keep.2.2, he.wr]; exact in_scr hp rfl (by omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (8 * i)) (tabQ i) := by rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨⟨fun g hg => by rw [g₂, u₁.other g (by simpa using hg), h.keep.gpr hg], by rw [r₂, u₁.rd, h.keep.2.1],
    by rw [w₂, u₁.wr, h.keep.2.2]⟩, ?_, fun i' hi' => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · rw [hm]
    by_cases e : i' = i
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [rd64_off (by omega) (by omega) (by omega)]
      exact h.tab i' (by omega)

theorem tabBuild_eq : tabBuild = (List.range 280).flatMap fun i =>
    [.movImm64 .rax (tabQ i), .store (at_ .rbx (8 * i)) .rax] := rfl

/-- The table and the constants. -/
theorem tab_ok {σ : State} (hp : Pre σ) {s₀ : State} (he : Env σ s₀) :
    WP isa (.block tabBuild) s₀ (TabInv σ s₀ 280) := by
  rw [tabBuild_eq]
  exact wp_range_flatMap (M := isa) (TabInv σ s₀) (fun i s hi h => tab_step hp he hi h) 280 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩

/-- After the squeezes and the table, before the first polynomial. -/
theorem pinv0_ok {σ : State} (hp : Pre σ) {s : State} (h : SqInv σ 3 s) :
    WP isa (.block tabBuild) s (PInv σ 0) := by
  refine WP.mono (tab_ok hp h.env) fun s' h' => ?_
  have hsub : ∀ r ∈ [(⟨at' σ 0, 2240⟩ : Region)], Region.Sub r ⟨scr σ, oSave⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low h.env hsub h'.frame h'.keep.2.1 h'.keep.2.2 fun r hr => h'.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    ⟨fun k hk p hp' => ?_, fun i hi => h'.tab i hi⟩, by rw [h'.keep.gpr (by decide), h.r14]; rfl,
    fun _ h _ _ => absurd h (by omega)⟩
  have hd := Offset.disjoint (scr σ) (d := oBuf) (n := 2016) (e := 0) (k := 2240) (.inr (by simp only [oBuf]; omega))
    (by simp only [oBuf]; omega) (by omega)
  rw [buf_frame (by simpa using hd) h'.frame hk hp']
  exact h.buf k hk p (by omega)

end VG.Proof.MlKem.X86_64.S4
