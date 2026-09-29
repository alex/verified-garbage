import VerifiedGarbage.Proof.MlKem.AArch64.KgA

/-!
# ML-KEM-768 on AArch64: `vg_mlkem768_keygen`, the matrix `Â`

Untrusted: everything here is checked by Lean. `Â[i, j]` for the nine
`(i, j)` (entry `e = 3i + j`), each with `sample_ntt`'s stronger contract:
it is reduced, and the result is 1 exactly when `SampleNTT` with 280
iterations succeeds; `x24` is the AND of the results.
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- `ρ`. -/
abbrev rhoK (s₀ : State) : List Byte := kgRho (dB s₀)

/-- Entry `e` of `Â`, at `s`. -/
abbrev aAt (s₀ : State) (m : Mem) (e : Nat) : Poly := polyAt m (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))

/-- Whether the first `k` `SampleNTT`s succeed. -/
def allOk (s₀ : State) (k : Nat) : Prop := ∀ e < k, (sampleNTT 280 (matSeed (rhoK s₀) (e / 3) (e % 3))).isSome

instance (s₀ : State) (k : Nat) : Decidable (allOk s₀ k) := by unfold allOk; infer_instance

/-- After `k` entries of `Â`. -/
structure BInv (s₀ : State) (k : Nat) (s : State) : Prop where
  kb : KB s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = kgSigma (dB s₀)
  acc : s.gpr .x24 = if allOk s₀ k then 1 else 0
  red : ∀ e < k, Reduced s.mem (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))
  res : ∀ e < k, sampleNTT 280 (matSeed (rhoK s₀) (e / 3) (e % 3)) = none ∨
    sampleNTT 280 (matSeed (rhoK s₀) (e / 3) (e % 3)) = some (aAt s₀ s.mem e)

theorem BInv.zero {s₀ s : State} (h : AfterA s₀ s) : BInv s₀ 0 s :=
  ⟨h.kb, h.rho, h.sig, by rw [h.x24, ite_eq_left (show allOk s₀ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩

theorem and_acc {a b : BitVec 64} {p q : Prop} [Decidable p] [Decidable q]
    (ha : a = if p then 1 else 0) (hb : (b = 1 ∧ q) ∨ (b = 0 ∧ ¬ q)) :
    a &&& b = if p ∧ q then 1 else 0 := by
  rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · by_cases hp : p
    · rw [ha, ite_eq_left hp, ite_eq_left ⟨hp, hq⟩]; rfl
    · rw [ha, ite_eq_right hp, ite_eq_right (fun h => hp h.1)]; rfl
  · rw [ite_eq_right (fun h => hq h.2)]
    by_cases hp : p
    · rw [ha, ite_eq_left hp]; rfl
    · rw [ha, ite_eq_right hp]; rfl

theorem allOk_succ {s₀ : State} {k : Nat} :
    allOk s₀ (k + 1) ↔ allOk s₀ k ∧ (sampleNTT 280 (matSeed (rhoK s₀) (k / 3) (k % 3))).isSome := by
  constructor
  · intro h; exact ⟨fun e he => h e (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ e he
    rcases (by omega : e < k ∨ e = k) with he | rfl
    · exact h e he
    · exact hk

/-- The seed `ρ ‖ j ‖ i`. -/
theorem seed_eq {m : Mem} {p : Addr} {ρ : List Byte} (hρ : bytesAt m p 32 = ρ) {j i : Byte}
    (hj : m (p + BitVec.ofNat 64 32) = j) (hi : m (p + BitVec.ofNat 64 33) = i) :
    bytesAt m p 34 = ρ ++ [j, i] := by
  rw [show 34 = 32 + 2 from rfl, bytesAt_add, hρ]
  refine congrArg (ρ ++ ·) (bytesAt_eq rfl fun k hk => ?_)
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [ptr_zero]; exact hj
  · rw [ptr_add]; exact hi

theorem sample_step {s₀ : State} (hp : Pre s₀) {i j : Nat} (hi : i < 3) (hj : j < 3) {s : State}
    (h : BInv s₀ (3 * i + j) s) : WP isa (kgSample i j) s (BInv s₀ (3 * i + j + 1)) := by
  have e : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by
    rw [h.kb.x28]
  have hk : 3 * i + j < 9 := by omega
  refine WP.seq ?_
  rw [List.append_assoc, List.append_assoc]
  have in₁ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (kA s₀ 3 + BitVec.ofNat 64 (SB + 32)) 1 :=
    fun hu => by
      rw [hu]
      exact in_R (cov_w hp h.kb (b := 3) (o := SB + 32) (l := 2) (by decide) (by decide)) (k := 0)
        (by decide) (by decide)
  have in₂ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (kA s₀ 3 + BitVec.ofNat 64 (SB + 33)) 1 :=
    fun hu => by
      rw [hu]
      exact in_R (cov_w hp h.kb (b := 3) (o := SB + 32) (l := 2) (by decide) (by decide)) (k := 1)
        (by decide) (by decide)
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := kA s₀ 3 + BitVec.ofNat 64 (SB + 32)) (by decide)
    (by rw [h₁.get .x28, e]) (in₁ h₁.wr) fun s₂ h₂ => ?_
  refine wp_movz fun s₃ h₃ e₃ => wp_strb (a := kA s₀ 3 + BitVec.ofNat 64 (SB + 33)) (by decide)
    (by rw [h₃.get .x28, h₂.gpr, h₁.get .x28, e]) (in₂ (by rw [h₃.wr, h₂.wr, h₁.wr])) fun s₄ h₄ => ?_
  refine wp_ptrTo (by decide) (by decide) fun s₅ h₅ e₅ => wp_ptrTo (by decide)
    (by simp only [aOff, AH]; omega) fun s₆ h₆ e₆ => wp_ptrTo' (by decide) (by decide)
    fun s₇ h₇ e₇ => ?_
  have g28 : s₄.gpr .x28 = kA s₀ 3 := by rw [h₄.gpr, h₃.get .x28, h₂.gpr, h₁.get .x28, h.kb.x28]
  have k₇ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep).trans
    h₇.keep
  have m₇ : s₇.mem = (s.mem.writeW (kA s₀ 3 + BitVec.ofNat 64 (SB + 32)) ((s₁.gpr .x9).setWidth 8)).writeW
      (kA s₀ 3 + BitVec.ofNat 64 (SB + 33)) ((s₃.gpr .x9).setWidth 8) := by
    rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have f₇ : Frame [R (kA s₀) 3 (SB + 32) 2] s.mem s₇.mem := by
    rw [m₇]
    have hm : R (kA s₀) 3 (SB + 32) 2 ∈ [R (kA s₀) 3 (SB + 32) 2] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (R.contains (k := 0) (by decide) (by decide))).writeW hm _
      (R.contains (k := 1) (by decide) (by decide))
  have kb₇ : KB s₀ s₇ := h.kb.frame k₇ f₇ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (by decide) (by decide) (by decide) (by decide)
  have sd : ∀ o, o < 32 → s₇.mem (kA s₀ 3 + BitVec.ofNat 64 SB + BitVec.ofNat 64 o) =
      s.mem (kA s₀ 3 + BitVec.ofNat 64 SB + BitVec.ofNat 64 o) := fun o ho => by
    rw [ptr_add]
    exact f₇ _ fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact R.disj hp.args (b₁ := 3) (o₁ := SB + o) (l₁ := 1) (by decide) (by decide)
        (by simp only [SB, kL]; omega) (by decide) (by simp only [SB]; omega) _
        (Region.contains_self _ _) hc
  have seed : bytesAt s₇.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 34 = matSeed (rhoK s₀) i j := by
    refine seed_eq (by rw [bytesAt_congr sd]; exact h.rho) ?_ ?_
    · rw [m₇, ptr_add, writeW8_apply, ite_eq_right (addr_ne _ (by decide) (by decide) (by decide)),
        writeW8_apply, ite_eq_left rfl, e₁]
      exact sfx8 (by omega)
    · rw [m₇, ptr_add, writeW8_apply, ite_eq_left rfl, e₃]
      exact sfx8 (by omega)
  have sp₇ : s₇.sp = s₀.sp := kb₇.sp
  have x0₇ : s₇.gpr .x0 = kA s₀ 3 + BitVec.ofNat 64 SB := by rw [h₇.get .x0, h₆.get .x0, e₅, g28]
  have x1₇ : s₇.gpr .x1 = kA s₀ 3 + BitVec.ofNat 64 (aOff i j) := by rw [h₇.get .x1, e₆, h₅.get .x28, g28]
  have x2₇ : s₇.gpr .x2 = kA s₀ 3 + BitVec.ofNat 64 SS := by
    rw [e₇, h₆.get .x28, h₅.get .x28, g28]
  have fa : aOff i j + 1024 ≤ kL 3 := by simp only [aOff, AH, kL]; omega
  refine WP.seq <| sample_call x0₇ x1₇ x2₇
    (R.disj hp.args (by decide) (by decide) (by decide) fa (by simp only [aOff, AH, SB]; omega))
    (R.disj hp.args (by decide) (by decide) (by decide) (by decide) (by decide))
    (R.disj hp.args (by decide) (by decide) fa (by decide) (by simp only [aOff, AH, SS]; omega))
    (by rw [sp₇]; exact hp.sp16) (stk_R hp kb₇ (by decide) (by decide)) (stk_R hp kb₇ (by decide) fa)
    (stk_R hp kb₇ (by decide) (by decide))
    (covers_cons (cov_r hp kb₇ (by decide) (by decide)) (covers_cons (cov_r hp kb₇ (by decide) fa)
      (cov_r hp kb₇ (by decide) (by decide))))
    (covers_cons (cov_w hp kb₇ (by decide) fa) (cov_w hp kb₇ (by decide) (by decide)))
    fun s₈ k₈ r₈ o₈ => ?_
  rw [sp₇] at k₈
  have kb₈ : KB s₀ s₈ := kb₇.call k₈ fun r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact kb_disj hp (by decide) fa (by simp only [aOff, AH, SV]; omega) (by decide)
    · exact kb_disj hp (by decide) (by decide) (by decide) (by decide)
    · exact kb_below hp
  refine wp_and fun s₉ h₉ e₉ => wp_nil ?_
  have kb₉ := kb₈.block h₉.keep h₉.mem (by decide)
  have fr : Frame [R (kA s₀) 3 (SB + 32) 2, R (kA s₀) 3 (aOff i j) 1024, R (kA s₀) 3 SS 2048,
      below s₀.sp 16] s.mem s₉.mem := by
    rw [h₉.mem]
    exact (f₇.mono (by simp)).trans (k₈.frame.mono (by simp))
  have far : ∀ {o l : Nat}, o + l ≤ kL 3 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) →
      (o + l ≤ aOff i j ∨ aOff i j + 1024 ≤ o) → (o + l ≤ SS ∨ SS + 2048 ≤ o) →
      ∀ r ∈ [R (kA s₀) 3 (SB + 32) 2, R (kA s₀) 3 (aOff i j) 1024, R (kA s₀) 3 SS 2048, below s₀.sp 16],
        (R (kA s₀) 3 o l).Disjoint r := fun f h1 h2 h3 r hr => by
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact R.disj hp.args (by decide) (by decide) f (by decide) (by omega)
    · exact R.disj hp.args (by decide) (by decide) f fa (by omega)
    · exact R.disj hp.args (by decide) (by decide) f (by decide) (by omega)
    · exact below_R hp (by decide) f
  have hke : (3 * i + j) / 3 = i ∧ (3 * i + j) % 3 = j := by omega
  have ae : ∀ {e : Nat}, e < 3 * i + j →
      ∀ r ∈ [R (kA s₀) 3 (SB + 32) 2, R (kA s₀) 3 (aOff i j) 1024, R (kA s₀) 3 SS 2048, below s₀.sp 16],
        (polyRegion (kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e))).Disjoint r :=
    fun he => far (by simp only [AH, kL]; omega) (by simp only [AH, SB]; omega)
      (by simp only [aOff, AH]; omega) (by simp only [AH, SS]; omega)
  rw [seed] at o₈
  have x0v : (s₈.gpr .x0 = 1 ∧ (sampleNTT 280 (matSeed (rhoK s₀) i j)).isSome) ∨
      (s₈.gpr .x0 = 0 ∧ ¬ (sampleNTT 280 (matSeed (rhoK s₀) i j)).isSome) := by
    rcases o₈ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2]; rfl⟩
    · exact .inr ⟨h1, by rw [h2]; simp⟩
  have g24 : s₈.gpr .x24 = s.gpr .x24 := by rw [k₈.cs _ (by decide) (by decide), k₇.get .x24]
  have acc : s₉.gpr .x24 = if allOk s₀ (3 * i + j) ∧ (sampleNTT 280 (matSeed (rhoK s₀) i j)).isSome
      then 1 else 0 := by
    rw [e₉, g24, and_acc h.acc x0v]
  refine ⟨kb₉, ?_, ?_, ?_, fun e he => ?_, fun e he => ?_⟩
  · rw [bytesAt_frame fr (far (by decide) (by decide) (by simp only [aOff, AH, SB]; omega)
      (by decide)) (by decide)]
    exact h.rho
  · rw [bytesAt_frame fr (far (by decide) (by decide) (by simp only [aOff, AH, SG]; omega)
      (by decide)) (by decide)]
    exact h.sig
  · rw [acc]
    by_cases hA : allOk s₀ (3 * i + j + 1)
    · have hA' := allOk_succ.mp hA
      rw [hke.1, hke.2] at hA'
      rw [ite_eq_left hA', ite_eq_left hA]
    · have hA' : ¬ (allOk s₀ (3 * i + j) ∧ (sampleNTT 280 (matSeed (rhoK s₀) i j)).isSome) := fun h' =>
        hA (allOk_succ.mpr (by rw [hke.1, hke.2]; exact h'))
      rw [ite_eq_right hA', ite_eq_right hA]
  · rcases (by omega : e < 3 * i + j ∨ e = 3 * i + j) with he | rfl
    · exact reduced_frame fr (ae he) (h.red e he)
    · rw [h₉.mem]; simpa only [aOff] using r₈
  · rcases (by omega : e < 3 * i + j ∨ e = 3 * i + j) with he | rfl
    · rw [aAt, polyAt_frame fr (ae he)]; exact h.res e he
    · rw [hke.1, hke.2, aAt, h₉.mem]
      rcases o₈ with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact .inr (by simpa only [aOff] using h2)
      · exact .inl h2

theorem b_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : AfterA s₀ s) : WP isa kgB s (BInv s₀ 9) :=
  WP.seq (WP.mono (sample_step hp (i := 0) (j := 0) (by decide) (by decide) (BInv.zero h)) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 0) (j := 1) (by decide) (by decide) h) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 0) (j := 2) (by decide) (by decide) h) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 1) (j := 0) (by decide) (by decide) h) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 1) (j := 1) (by decide) (by decide) h) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 1) (j := 2) (by decide) (by decide) h) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 2) (j := 0) (by decide) (by decide) h) fun _ h =>
  WP.seq (WP.mono (sample_step hp (i := 2) (j := 1) (by decide) (by decide) h) fun _ h =>
    sample_step hp (i := 2) (j := 2) (by decide) (by decide) h))))))))

end VG.Proof.MlKem.AArch64.KeyGen
