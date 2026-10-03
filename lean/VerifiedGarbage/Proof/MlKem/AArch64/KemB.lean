import VerifiedGarbage.Proof.MlKem.AArch64.KemOps

/-!
# ML-KEM on AArch64: the matrix `Â` of `encaps` and `decaps`

`Â[i, j]` for the `k²` entries `(i, j)` (entry `e = k i + j`), from the seed `ρ` at
`SB`, each with `sample_ntt`'s stronger contract: it is reduced, and the
result is 1 exactly when `SampleNTT` with 280 iterations succeeds; `x24` is
the AND of the results. The matrix writes only the last two bytes of the seed,
`Â`, `sample_ntt`'s working space and the stack below the stack pointer
(`bW`).

Constant time, relating two runs with the same pointers and the same `ρ`:
the arguments of each call by the taint analysis, and the calls by
`sample_ntt`'s own constant time (`matrix_rct`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem.AArch64.KeyGen (and_acc)

variable {P : KemLay} {L : Layout}

/-- Whether the first `n` `SampleNTT`s from `ρ` succeed. -/
def okR (P : KemLay) (ρ : List Byte) (n : Nat) : Prop :=
  ∀ e < n, (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome

instance (ρ : List Byte) (n : Nat) : Decidable (okR P ρ n) := by unfold okR; infer_instance

theorem okR_succ {ρ : List Byte} {k : Nat} :
    okR P ρ (k + 1) ↔ okR P ρ k ∧ (sampleNTT 280 (matSeed ρ (k / P.k) (k % P.k))).isSome := by
  constructor
  · intro h; exact ⟨fun e he => h e (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ e he
    rcases (by omega : e < k ∨ e = k) with he | rfl
    · exact h e he
    · exact hk

/-- What the matrix writes. -/
abbrev bW (P : KemLay) (L : Layout) (s₀ : State) : List Region :=
  [R (kA s₀) L.sc (SB + 32) 2, R (kA s₀) L.sc AH (1024 * (P.k * P.k)), R (kA s₀) L.sc SS 2048, below s₀.sp 16]

/-- Entry `e` of `Â`. -/
abbrev aP (L : Layout) (s₀ : State) (e : Nat) : Addr := sA L s₀ (AH + 1024 * e)

/-- After `n` entries of `Â`, from memory `mA`. -/
structure BInv (P : KemLay) (L : Layout) (s₀ : State) (mA : Mem) (ρ : List Byte) (n : Nat) (s : State) :
    Prop where
  kb : KB P L s₀ s
  fr : Frame (bW P L s₀) mA s.mem
  rho : bytesAt s.mem (sA L s₀ SB) 32 = ρ
  acc : s.gpr .x24 = if okR P ρ n then 1 else 0
  red : ∀ e < n, Reduced s.mem (aP L s₀ e)
  res : ∀ e < n, sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k)) = none ∨
    sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k)) = some (polyAt s.mem (aP L s₀ e))

theorem BInv.zero {s₀ s : State} {ρ : List Byte} (hk : KB P L s₀ s) (h24 : s.gpr .x24 = 1)
    (hρ : bytesAt s.mem (sA L s₀ SB) 32 = ρ) : BInv P L s₀ s.mem ρ 0 s :=
  ⟨hk, Frame.refl _ _, hρ, by rw [h24, ite_eq_left (show okR P ρ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩

/-- Before `SampleNTT(ρ ‖ j ‖ i)`: its seed, and its arguments. -/
structure Mid (P : KemLay) (L : Layout) (s₀ : State) (mA : Mem) (ρ : List Byte) (i j : Nat) (s : State) :
    Prop where
  b : BInv P L s₀ mA ρ (P.k * i + j) s
  seed : bytesAt s.mem (sA L s₀ SB) 34 = matSeed ρ i j
  x0 : s.gpr .x0 = sA L s₀ SB
  x1 : s.gpr .x1 = sA L s₀ (aOff P i j)
  x2 : s.gpr .x2 = sA L s₀ SS

theorem setup_ok {s₀ : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : BInv P L s₀ mA ρ (P.k * i + j) s) :
    WP isa (.block (P.kemSetup i j)) s (Mid P L s₀ mA ρ i j) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have e := e28 h.kb
  rw [KemLay.kemSetup, List.append_assoc, List.append_assoc]
  have in₁ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (sA L s₀ (SB + 32)) 1 :=
    fun hu => by
      rw [hu]
      exact in_R (cov_s hp h.kb (o := SB + 32) (l := 2) (by kom)) (k := 0) (by decide) (by decide)
  have in₂ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (sA L s₀ (SB + 33)) 1 :=
    fun hu => by
      rw [hu]
      exact in_R (cov_s hp h.kb (o := SB + 32) (l := 2) (by kom)) (k := 1) (by decide) (by decide)
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := sA L s₀ (SB + 32)) (by decide)
    (by rw [h₁.get .x28, e]) (in₁ h₁.wr) fun s₂ h₂ => ?_
  refine wp_movz fun s₃ h₃ e₃ => wp_strb (a := sA L s₀ (SB + 33)) (by decide)
    (by rw [h₃.get .x28, h₂.gpr, h₁.get .x28, e]) (in₂ (by rw [h₃.wr, h₂.wr, h₁.wr])) fun s₄ h₄ => ?_
  refine wp_ptrTo (by decide) (by decide) fun s₅ h₅ e₅ => wp_ptrTo (by decide)
    (by lom) fun s₆ h₆ e₆ => wp_ptrTo' (by decide) (by decide)
    fun s₇ h₇ e₇ => ?_
  have g28 : s₄.gpr .x28 = kA s₀ L.sc := by rw [h₄.gpr, h₃.get .x28, h₂.gpr, h₁.get .x28, h.kb.x28]
  have k₇ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep).trans
    h₇.keep
  have m₇ : s₇.mem = (s.mem.writeW (sA L s₀ (SB + 32)) ((s₁.gpr .x9).setWidth 8)).writeW
      (sA L s₀ (SB + 33)) ((s₃.gpr .x9).setWidth 8) := by
    rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have f₇ : Frame [R (kA s₀) L.sc (SB + 32) 2] s.mem s₇.mem := by
    rw [m₇]
    have hm : R (kA s₀) L.sc (SB + 32) 2 ∈ [R (kA s₀) L.sc (SB + 32) 2] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (R.contains (k := 0) (by decide) (by decide))).writeW hm _
      (R.contains (k := 1) (by decide) (by decide))
  have kb₇ : KB P L s₀ s₇ := h.kb.frame k₇ f₇ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have sd : ∀ o, o < 32 → s₇.mem (sA L s₀ SB + BitVec.ofNat 64 o) = s.mem (sA L s₀ SB + BitVec.ofNat 64 o) :=
    fun o ho => by
      rw [ptr_add]
      exact f₇ _ fun r hr hc => by
        rw [List.mem_singleton.mp hr] at hc
        exact sdisj hp (o₁ := SB + o) (l₁ := 1) (by lom) (by lom)
          (by simp only [SB]; omega) _ (Region.contains_self _ _) hc
  have ae : ∀ {e : Nat}, e < P.k * i + j →
      ∀ r ∈ [R (kA s₀) L.sc (SB + 32) 2], (polyRegion (aP L s₀ e)).Disjoint r :=
    fun he r hr => by
      rw [List.mem_singleton.mp hr]
      exact sdisj hp (by lom) (by lom) (by simp only [AH, SB]; omega)
  refine ⟨⟨kb₇, h.fr.trans (f₇.mono (by simp)), by rw [bytesAt_congr sd]; exact h.rho,
    by rw [k₇.get .x24]; exact h.acc, fun e he => reduced_frame f₇ (ae he) (h.red e he), fun e he => ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [polyAt_frame f₇ (ae he)]; exact h.res e he
  · refine seed_eq (by rw [bytesAt_congr sd]; exact h.rho) ?_ ?_
    · rw [m₇, ptr_add, writeW8_apply, ite_eq_right (addr_ne _ (by decide) (by decide) (by decide)),
        writeW8_apply, ite_eq_left rfl, e₁]
      exact sfx8 (by lom)
    · rw [m₇, ptr_add, writeW8_apply, ite_eq_left rfl, e₃]
      exact sfx8 (by lom)
  · rw [h₇.get .x0, h₆.get .x0, e₅, g28]
  · rw [h₇.get .x1, e₆, h₅.get .x28, g28]
  · rw [e₇, h₆.get .x28, h₅.get .x28, g28]

/-- The arguments of `SampleNTT` for `Â[i, j]`. -/
theorem Mid.args {s₀ : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : Mid P L s₀ mA ρ i j s) :
    SampleArgs s (sA L s₀ SB) (sA L s₀ (aOff P i j)) (sA L s₀ SS) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have kb := h.b.kb
  have f : ∀ {o l : Nat}, o + l ≤ 4248 → o + l ≤ SV P + 48 := fun h => by lom
  have fa : aOff P i j + 1024 ≤ SV P + 48 := by lom
  have fs : ∀ {o l : Nat}, o + l ≤ SV P + 48 → o + l ≤ L.len L.sc := hp.fs
  exact ⟨h.x0, h.x1, h.x2,
    sdisj hp (f (by decide)) fa (.inl (by lom)),
    sdisj hp (f (by decide)) (f (by decide)) (by decide),
    sdisj hp fa (f (by decide)) (.inr (by lom)),
    by rw [kb.sp]; exact hp.sp16, stk_R hp kb hp.scb (fs (f (by decide))), stk_R hp kb hp.scb (fs fa),
    stk_R hp kb hp.scb (fs (f (by decide))),
    covers_cons (cov_sr hp kb (f (by decide))) (covers_cons (cov_sr hp kb fa) (cov_sr hp kb (f (by decide)))),
    covers_cons (cov_s hp kb fa) (cov_s hp kb (f (by decide)))⟩

theorem call_ok {s₀ : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : Mid P L s₀ mA ρ i j s) :
    WP isa (kgCallWith keccak.callee) s (BInv P L s₀ mA ρ (P.k * i + j + 1)) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have kb := h.b.kb
  have f : ∀ {o l : Nat}, o + l ≤ 4248 → o + l ≤ SV P + 48 := fun h => by lom
  have fa : aOff P i j + 1024 ≤ SV P + 48 := by lom
  have A := h.args hp hi hj
  refine WP.seq <| sample_callWith keccak A.h0 A.h1 A.h2 A.d₁ A.d₂ A.d₃ A.hsp A.k₁ A.k₂ A.k₃ A.hc A.hw
    fun s₈ k₈ r₈ o₈ => ?_
  rw [kb.sp] at k₈
  have kb₈ : KB P L s₀ s₈ := kb.call k₈ fun r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact safe_scr hp (by lom)
    · exact safe_scr hp (by lom)
    · exact safe_below hp
  refine wp_and fun s₉ h₉ e₉ => wp_nil ?_
  have kb₉ := kb₈.block h₉.keep h₉.mem (by decide)
  have fr : Frame [R (kA s₀) L.sc (aOff P i j) 1024, R (kA s₀) L.sc SS 2048, below s₀.sp 16] s.mem s₉.mem := by
    rw [h₉.mem]; exact k₈.frame
  have far : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ aOff P i j ∨ aOff P i j + 1024 ≤ o) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) →
      ∀ r ∈ [R (kA s₀) L.sc (aOff P i j) 1024, R (kA s₀) L.sc SS 2048, below s₀.sp 16],
        (R (kA s₀) L.sc o l).Disjoint r := fun fo h2 h3 r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact sdisj hp fo fa h2
    · exact sdisj hp fo (f (by decide)) h3
    · exact below_R hp hp.scb (hp.fs fo)
  have hke := ij_div (i := i) hj
  have ae : ∀ {e : Nat}, e < P.k * i + j →
      ∀ r ∈ [R (kA s₀) L.sc (aOff P i j) 1024, R (kA s₀) L.sc SS 2048, below s₀.sp 16],
        (polyRegion (aP L s₀ e)).Disjoint r :=
    fun he => far (by lom) (by lom) (by lom)
  rw [h.seed] at o₈
  have x0v : (s₈.gpr .x0 = 1 ∧ (sampleNTT 280 (matSeed ρ i j)).isSome) ∨
      (s₈.gpr .x0 = 0 ∧ ¬ (sampleNTT 280 (matSeed ρ i j)).isSome) := by
    rcases o₈ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2]; rfl⟩
    · exact .inr ⟨h1, by rw [h2]; simp⟩
  have g24 : s₈.gpr .x24 = s.gpr .x24 := k₈.cs _ (by decide) (by decide)
  have acc : s₉.gpr .x24 = if okR P ρ (P.k * i + j) ∧ (sampleNTT 280 (matSeed ρ i j)).isSome then 1 else 0 := by
    rw [e₉, g24, and_acc h.b.acc x0v]
  refine ⟨kb₉, h.b.fr.trans (fr.sub fun r hr => ?_), ?_, ?_, fun e he => ?_, fun e he => ?_⟩
  · rcases mem3 hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        R.sub2 (by simp only [aOff]; omega) (by simp only [aOff]; omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame fr (far (f (by decide)) (.inl (by lom)) (by decide)) (by decide)]
    exact h.b.rho
  · rw [acc]
    by_cases hA : okR P ρ (P.k * i + j + 1)
    · have hA' := okR_succ.mp hA
      rw [hke.1, hke.2] at hA'
      rw [ite_eq_left hA', ite_eq_left hA]
    · have hA' : ¬ (okR P ρ (P.k * i + j) ∧ (sampleNTT 280 (matSeed ρ i j)).isSome) := fun h' =>
        hA (okR_succ.mpr (by rw [hke.1, hke.2]; exact h'))
      rw [ite_eq_right hA', ite_eq_right hA]
  · rcases (by omega : e < P.k * i + j ∨ e = P.k * i + j) with he | rfl
    · exact reduced_frame fr (ae he) (h.b.red e he)
    · rw [h₉.mem]; simpa only [aOff] using r₈
  · rcases (by omega : e < P.k * i + j ∨ e = P.k * i + j) with he | rfl
    · rw [polyAt_frame fr (ae he)]; exact h.b.res e he
    · rw [hke.1, hke.2, h₉.mem]
      rcases o₈ with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact .inr (by simpa only [aOff] using h2)
      · exact .inl h2

theorem sample_step {s₀ : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : BInv P L s₀ mA ρ (P.k * i + j) s) :
    WP isa (P.kemSampleWith keccak.callee i j) s (BInv P L s₀ mA ρ (P.k * i + j + 1)) :=
  WP.seq (WP.mono (setup_ok hp hi hj h) fun _ m => call_ok hp hi hj m)

theorem matrix_ok {s₀ : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {s : State}
    (h : BInv P L s₀ mA ρ 0 s) : WP isa (P.kemMatrixWith keccak.callee) s (BInv P L s₀ mA ρ (P.k * P.k)) :=
  WPs.seqs (matrix_ne_nil hp.wf.facts.1)
    (WPs.matrix (fun _ hi _ hj _ h => sample_step hp hi hj h) (Nat.le_refl _) h)

/-! ## After the matrix -/

/-- `SampleNTT` succeeds on every entry exactly when `x24` is 1; then its
entries are `Â`'s. -/
theorem BInv.outcome {s₀ : State} {mA : Mem} {ρ : List Byte} {s : State}
    (h : BInv P L s₀ mA ρ (P.k * P.k) s) :
    (s.gpr .x24 = 1 ∧ ∀ i < P.k, ∀ j < P.k,
      sampleNTT 280 (matSeed ρ i j) = some (polyAt s.mem (sA L s₀ (aOff P i j)))) ∨
    (s.gpr .x24 = 0 ∧ ∃ i < P.k, ∃ j < P.k, sampleNTT 280 (matSeed ρ i j) = none) := by
  by_cases hA : okR P ρ (P.k * P.k)
  · refine .inl ⟨by rw [h.acc, ite_eq_left hA], fun i hi j hj => ?_⟩
    have he : P.k * i + j < P.k * P.k := ij_lt hi hj
    have hke := ij_div (i := i) hj
    have r := h.res (P.k * i + j) he
    have ok := hA (P.k * i + j) he
    rw [hke.1, hke.2] at r ok
    rcases r with r | r
    · rw [r] at ok; simp at ok
    · exact r
  · refine .inr ⟨by rw [h.acc, ite_eq_right hA], ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    exact ⟨e / P.k, div_lt he, e % P.k, mod_lt he, Option.not_isSome_iff_eq_none.mp hn⟩

theorem BInv.reduced {s₀ : State} {mA : Mem} {ρ : List Byte} {s : State} (h : BInv P L s₀ mA ρ (P.k * P.k) s)
    {i j : Nat} (hi : i < P.k) (hj : j < P.k) : Reduced s.mem (sA L s₀ (aOff P i j)) :=
  h.red (P.k * i + j) (ij_lt hi hj)

/-! ## Constant time -/

/-- The arguments of `sample_ntt` depend only on the pointer to `scratch`:
decided for each parameter set. -/
def SetupTaint (P : KemLay) : Prop := ∀ i < P.k, ∀ j < P.k, ∃ hc : Taint.Hint taint.T,
    (taint.check (Taint.ofRegs [.x28]) (.block (P.kemSetup i j)) hc).isSome = true

/-- Two runs with the same pointer to `scratch` and the same stack pointer. -/
structure Two (P : KemLay) (L : Layout) (σ₁ σ₂ : State) : Prop where
  p₁ : Pre P L σ₁
  p₂ : Pre P L σ₂
  sc : kA σ₁ L.sc = kA σ₂ L.sc
  sp : σ₁.sp = σ₂.sp

theorem call_rct {σ₁ σ₂ : State} (ht : Two P L σ₁ σ₂) {m₁ m₂ : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => Mid P L σ₁ m₁ ρ i j s₁ ∧ Mid P L σ₂ m₂ ρ i j s₂) (kgCallWith keccak.callee)
      fun _ _ => True := by
  refine RelCT.seq (RelCT.wp (F₁ := fun s : State => s.sp = σ₁.sp) (F₂ := fun s : State => s.sp = σ₂.sp)
    (sample_ctWith keccak (sd := sA L σ₁ SB) (a := sA L σ₁ (aOff P i j)) (w := sA L σ₁ SS) fun s₁ s₂ h => ?_)
      fun s₁ s₂ h => ⟨?_, ?_⟩)
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => agree_of (by rw [h.2.1, h.2.2, ht.sp])
      fun r hr => by cases hr) (by taint_decide))
  · have A₂ := h.2.args ht.p₂ hi hj
    simp only [sA, ← ht.sc] at A₂
    refine ⟨h.1.args ht.p₁ hi hj, A₂, ?_, by rw [h.1.b.kb.sp, h.2.b.kb.sp, ht.sp]⟩
    rw [h.1.seed]
    have s₂ := h.2.seed
    simp only [sA, ← ht.sc] at s₂
    rw [s₂]
  · exact WP.mono ((h.1.args ht.p₁ hi hj).spWith keccak) fun s' e => by rw [e, h.1.b.kb.sp]
  · exact WP.mono ((h.2.args ht.p₂ hi hj).spWith keccak) fun s' e => by rw [e, h.2.b.kb.sp]

theorem sample_rct (hs : SetupTaint P) {σ₁ σ₂ : State} (ht : Two P L σ₁ σ₂) {m₁ m₂ : Mem} {ρ : List Byte}
    {i j : Nat} (hi : i < P.k) (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => BInv P L σ₁ m₁ ρ (P.k * i + j) s₁ ∧ BInv P L σ₂ m₂ ρ (P.k * i + j) s₂)
      (P.kemSampleWith keccak.callee i j)
      fun s₁ s₂ => BInv P L σ₁ m₁ ρ (P.k * i + j + 1) s₁ ∧ BInv P L σ₂ m₂ ρ (P.k * i + j + 1) s₂ := by
  have hck := (hs i hi j hj).choose_spec
  refine RelCT.seq (R := fun s₁ s₂ => Mid P L σ₁ m₁ ρ i j s₁ ∧ Mid P L σ₂ m₂ ρ i j s₂)
    (RelCT.mono (RelCT.wp (F₁ := Mid P L σ₁ m₁ ρ i j) (F₂ := Mid P L σ₂ m₂ ρ i j)
      (RelCT.taint (A := taint) (Taint.ofRegs [.x28]) (fun s₁ s₂ h =>
        agree_of (by rw [h.1.kb.sp, h.2.kb.sp, ht.sp]) fun r hr => by
          rw [List.mem_singleton.mp hr, h.1.kb.x28, h.2.kb.x28, ht.sc]) hck)
      fun s₁ s₂ h => ⟨setup_ok ht.p₁ hi hj h.1, setup_ok ht.p₂ hi hj h.2⟩) (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono (RelCT.wp (F₁ := BInv P L σ₁ m₁ ρ (P.k * i + j + 1)) (F₂ := BInv P L σ₂ m₂ ρ (P.k * i + j + 1))
      (call_rct ht hi hj) fun s₁ s₂ h => ⟨call_ok ht.p₁ hi hj h.1, call_ok ht.p₂ hi hj h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)

theorem matrix_rct (hs : SetupTaint P) {σ₁ σ₂ : State} (ht : Two P L σ₁ σ₂) {m₁ m₂ : Mem} {ρ : List Byte} :
    RelCT isa (fun s₁ s₂ => BInv P L σ₁ m₁ ρ 0 s₁ ∧ BInv P L σ₂ m₂ ρ 0 s₂) (P.kemMatrixWith keccak.callee)
      fun s₁ s₂ => BInv P L σ₁ m₁ ρ (P.k * P.k) s₁ ∧ BInv P L σ₂ m₂ ρ (P.k * P.k) s₂ :=
  RelCTs.seqs (matrix_ne_nil ht.p₁.wf.facts.1)
    (RelCTs.matrix (I := fun e s₁ s₂ => BInv P L σ₁ m₁ ρ e s₁ ∧ BInv P L σ₂ m₂ ρ e s₂)
      (fun _ hi _ hj => sample_rct hs ht hi hj) (Nat.le_refl _))

end VG.Proof.MlKem.AArch64.Kem
