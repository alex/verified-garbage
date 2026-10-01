import VerifiedGarbage.Proof.MlKem1024.AArch64.KgEnd

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`

Untrusted: everything here is checked by Lean. Correctness is the prologue
and `G` (`a_ok`), the matrix (`b_ok`), then `ŝ`, `ê`, `t̂` and the end
(`c_ok`); the result is 1 exactly when every `SampleNTT` finishes within 280
iterations (`post_of`).

Constant time up to `ρ`, relating two runs (`RelCT`) from states that agree
on the pointers and on `ρ`: the prologue and `G`, and everything after the
matrix, by the taint analysis (their addresses and branches depend only on
the pointers); each entry of the matrix by the taint analysis for the
arguments of `sample_ntt`, then `sample_ntt`'s own constant time
(`RelCT.call`), since both runs call it on the same seed `ρ ‖ j ‖ i`.
-/

namespace VG.Proof.MlKem1024.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KG VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-! ## Correctness -/

theorem a_ok {s₀ : State} (hp : Pre s₀) : WP isa kgA s₀ (AfterA s₀) :=
  WP.seq (WP.mono (prologue_ok hp) fun _ h => g_ok hp h)

theorem c_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : BInv s₀ 16 s) :
    WP isa kgC s (Done s₀ s.mem (s.gpr .x24)) := by
  have c : CInv s₀ s.mem (s.gpr .x24) s := ⟨h.kb, h.rho, h.sig, rfl, fun e he => ⟨h.red e he, rfl⟩⟩
  have s0 : SInv s₀ s.mem (s.gpr .x24) 0 s :=
    ⟨c, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WP.seq (WP.mono (s_step hp (j := 0) (by decide) s0) fun _ h₁ =>
    WP.seq (WP.mono (s_step hp (j := 1) (by decide) h₁) fun _ h₂ =>
    WP.seq (WP.mono (s_step hp (j := 2) (by decide) h₂) fun _ h₃ =>
    WP.seq (WP.mono (s_step hp (j := 3) (by decide) h₃) fun _ h₄ =>
    WP.seq (WP.mono (t_step hp (i := 0) (by decide)
      ⟨h₄.c, h₄.sp, h₄.dk, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun _ t₁ =>
    WP.seq (WP.mono (t_step hp (i := 1) (by decide) t₁) fun _ t₂ =>
    WP.seq (WP.mono (t_step hp (i := 2) (by decide) t₂) fun _ t₃ =>
    WP.seq (WP.mono (t_step hp (i := 3) (by decide) t₃) fun _ t₄ => end_ok hp t₄))))))))

theorem post_of {s₀ sB s' : State} (hB : BInv s₀ 16 sB) (hD : Done s₀ sB.mem (sB.gpr .x24) s') :
    keyGen1024AArch64.post s₀ s' := by
  show Outcome (fun iters => keyGenInternal mlKem1024 iters (bytesAt s₀.mem (s₀.gpr .x0) 32)
    (bytesAt s₀.mem (s₀.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x1) 1568, bytesAt s'.mem (s₀.gpr .x2) 3168)
  have ed : bytesAt s₀.mem (s₀.gpr .x0) 32 = dB s₀ := by
    show _ = bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 0) 32
    rw [ptr_zero]
  have ez : bytesAt s₀.mem (s₀.gpr .x0 + 32) 32 = zB s₀ := rfl
  have ek : bytesAt s'.mem (s₀.gpr .x1) 1568 = ekPKE1024 (aM s₀ sB.mem) (dB s₀) := hD.ek
  have dk : bytesAt s'.mem (s₀.gpr .x2) 3168 = dkPKE1024 (dB s₀) ++ ekPKE1024 (aM s₀ sB.mem) (dB s₀) ++
      H (ekPKE1024 (aM s₀ sB.mem) (dB s₀)) ++ zB s₀ := hD.dk
  rw [ed, ez, ek, dk, hD.x0, hB.acc]
  by_cases hA : allOk s₀ 16
  · rw [ite_eq_left hA]
    refine .inl ⟨rfl, 280, ?_⟩
    show keyGenInternal mlKem1024 280 (dB s₀) (zB s₀) = _
    rw [keyGenInternal1024, kpkeKeyGen1024_some (a := aM s₀ sB.mem) fun i hi j hj => ?_]
    · rfl
    · have he : 4 * i + j < 16 := by omega
      have hke : (4 * i + j) / 4 = i ∧ (4 * i + j) % 4 = j := by omega
      have r := hB.res (4 * i + j) he
      have ok := hA (4 * i + j) he
      rw [hke.1, hke.2] at r ok
      rcases r with r | r
      · rw [r] at ok; simp at ok
      · exact r
  · rw [ite_eq_right hA]
    refine .inr ⟨rfl, ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < 16 ∧ ¬ (sampleNTT 280 (matSeed (rhoK s₀) (e / 4) (e % 4))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    show keyGenInternal mlKem1024 280 _ _ = none
    rw [keyGenInternal1024, kpkeKeyGen1024_none (i := e / 4) (j := e % 4) (by omega) (by omega)
      (Option.not_isSome_iff_eq_none.mp hn)]
    rfl

theorem correct {s₀ : State} (hs : keyGen1024AArch64.pre s₀) :
    WP isa keyGen s₀ fun s' => abiPreserved s₀ s' ∧ keyGen1024AArch64.post s₀ s' := by
  apply WP.withPreservedV (hc := by decide +kernel)
  have hp := pre_of hs
  exact WP.seq (WP.mono (a_ok hp) fun _ hA => WP.seq (WP.mono (b_ok hp hA) fun _ hB =>
    WP.mono (c_ok hp hB) fun _ hD => ⟨hD.abi, post_of hB hD⟩))

/-! ## Constant time -/

/-- Two runs from states the contract relates. -/
abbrev Pub3 (σ₁ σ₂ : State) : Prop :=
  keyGen1024AArch64.pre σ₁ ∧ keyGen1024AArch64.pre σ₂ ∧ keyGen1024AArch64.pub σ₁ σ₂

theorem Pub3.kA {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : ∀ b, kA σ₁ b = kA σ₂ b
  | 0 => h.2.2.1
  | 1 => h.2.2.2.1
  | 2 => h.2.2.2.2.1
  | _ + 3 => h.2.2.2.2.2.1

theorem Pub3.sp {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : σ₁.sp = σ₂.sp := h.2.2.2.2.2.2.1

theorem Pub3.rho {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : rhoK σ₁ = rhoK σ₂ := by
  have e := Sample.map_toNat_inj h.2.2.2.2.2.2.2
  show kgRho1024 (bytesAt σ₁.mem (σ₁.gpr .x0 + BitVec.ofNat 64 0) 32) =
    kgRho1024 (bytesAt σ₂.mem (σ₂.gpr .x0 + BitVec.ofNat 64 0) 32)
  rw [ptr_zero, ptr_zero]
  exact e

/-- `SampleNTT` on the same seed in both runs. -/
theorem call_rct {σ₁ σ₂ : State} (hpub : Pub3 σ₁ σ₂) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelCT isa (fun s₁ s₂ => Mid σ₁ i j s₁ ∧ Mid σ₂ i j s₂) kgCall fun _ _ => True := by
  have hp₁ := pre_of hpub.1
  have hp₂ := pre_of hpub.2.1
  refine RelCT.seq (RelCT.wp (F₁ := fun s : State => s.sp = σ₁.sp) (F₂ := fun s : State => s.sp = σ₂.sp)
    (sample_ct (sd := kA σ₁ 3 + BitVec.ofNat 64 SB) (a := kA σ₁ 3 + BitVec.ofNat 64 (aOff i j))
      (w := kA σ₁ 3 + BitVec.ofNat 64 SS) fun s₁ s₂ h => ?_) fun s₁ s₂ h => ⟨?_, ?_⟩)
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => agree_of (by rw [h.2.1, h.2.2, hpub.sp])
      fun r hr => by cases hr) (by taint_decide))
  · have A₂ := h.2.args hp₂ hi hj
    rw [← hpub.kA 3] at A₂
    refine ⟨h.1.args hp₁ hi hj, A₂, ?_, by rw [h.1.b.kb.sp, h.2.b.kb.sp, hpub.sp]⟩
    rw [h.1.seed, hpub.kA 3, h.2.seed, hpub.rho]
  · exact WP.mono (h.1.args hp₁ hi hj).sp fun s' e => by rw [e, h.1.b.kb.sp]
  · exact WP.mono (h.2.args hp₂ hi hj).sp fun s' e => by rw [e, h.2.b.kb.sp]

/-- The arguments of `sample_ntt` depend only on the pointer to `scratch`. -/
theorem setup_taint : ∀ i < 4, ∀ j < 4, ∃ hc : Taint.Hint taint.T,
    (taint.check (Taint.ofRegs [.x28]) (.block (kgSetup i j)) hc).isSome = true := by
  intro i hi j hj
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  exact ⟨_, by taint_decide⟩

/-- `Â[i, j]` in both runs. -/
theorem sample_rct {σ₁ σ₂ : State} (hpub : Pub3 σ₁ σ₂) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelCT isa (fun s₁ s₂ => BInv σ₁ (4 * i + j) s₁ ∧ BInv σ₂ (4 * i + j) s₂) (kgSample i j)
      fun s₁ s₂ => BInv σ₁ (4 * i + j + 1) s₁ ∧ BInv σ₂ (4 * i + j + 1) s₂ := by
  have hp₁ := pre_of hpub.1
  have hp₂ := pre_of hpub.2.1
  have hck := (setup_taint i hi j hj).choose_spec
  refine RelCT.seq (R := fun s₁ s₂ => Mid σ₁ i j s₁ ∧ Mid σ₂ i j s₂)
    (RelCT.mono (RelCT.wp (F₁ := Mid σ₁ i j) (F₂ := Mid σ₂ i j)
      (RelCT.taint (A := taint) (Taint.ofRegs [.x28]) (fun s₁ s₂ h =>
        agree_of (by rw [h.1.kb.sp, h.2.kb.sp, hpub.sp]) fun r hr => by
          rw [List.mem_singleton.mp hr, h.1.kb.x28, h.2.kb.x28, hpub.kA 3]) hck)
      fun s₁ s₂ h => ⟨setup_ok hp₁ hi hj h.1, setup_ok hp₂ hi hj h.2⟩) (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono (RelCT.wp (F₁ := BInv σ₁ (4 * i + j + 1)) (F₂ := BInv σ₂ (4 * i + j + 1))
      (call_rct hpub hi hj) fun s₁ s₂ h => ⟨call_ok hp₁ hi hj h.1, call_ok hp₂ hi hj h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)

theorem b_rct : RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, Pub3 σ₁ σ₂ ∧ AfterA σ₁ s₁ ∧ AfterA σ₂ s₂) kgB
    fun s₁ s₂ => ∃ σ₁ σ₂, Pub3 σ₁ σ₂ ∧ BInv σ₁ 16 s₁ ∧ BInv σ₂ 16 s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State) s₁ s₂ =>
      Pub3 x.1 x.2 ∧ BInv x.1 0 s₁ ∧ BInv x.2 0 s₂) fun x => ?_)
    (fun _ _ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂), hpub, BInv.zero a₁, BInv.zero a₂⟩) fun _ _ h => h
  by_cases hpub : Pub3 x.1 x.2
  · refine RelCT.mono (P := fun s₁ s₂ => BInv x.1 0 s₁ ∧ BInv x.2 0 s₂)
      (Q := fun s₁ s₂ => BInv x.1 16 s₁ ∧ BInv x.2 16 s₂) ?_ (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2, hpub, h⟩
    exact RelCT.seq (sample_rct hpub (i := 0) (j := 0) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 0) (j := 1) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 0) (j := 2) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 0) (j := 3) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 1) (j := 0) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 1) (j := 1) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 1) (j := 2) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 1) (j := 3) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 2) (j := 0) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 2) (j := 1) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 2) (j := 2) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 2) (j := 3) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 3) (j := 0) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 3) (j := 1) (by decide) (by decide)) <|
      RelCT.seq (sample_rct hpub (i := 3) (j := 2) (by decide) (by decide))
        (sample_rct hpub (i := 3) (j := 3) (by decide) (by decide))
  · exact RelCT.of_false fun _ _ h => hpub h.1

theorem c_rct : RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂, Pub3 σ₁ σ₂ ∧ BInv σ₁ 16 s₁ ∧ BInv σ₂ 16 s₂) kgC
    fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x25, .x26, .x27, .x28]) (fun s₁ s₂ ⟨σ₁, σ₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, hpub.sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25, hpub.kA 0]
      · rw [b₁.kb.x26, b₂.kb.x26, hpub.kA 1]
      · rw [b₁.kb.x27, b₂.kb.x27, hpub.kA 2]
      · rw [b₁.kb.x28, b₂.kb.x28, hpub.kA 3]) (by taint_decide)

theorem ct : ConstantTime isa keyGen1024AArch64.pre keyGen1024AArch64.pub keyGen :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, -, -⟩ := h
        simp [e0, e1, e2, e3])) (by taint_decide)).wpDep (F := fun σ s => AfterA σ s)
      fun _ _ h => ⟨a_ok (pre_of h.1), a_ok (pre_of h.2.1)⟩)
    (RelCT.seq b_rct c_rct))

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem keyGen_correct (s : State) (hs : keyGen1024AArch64.pre s) :
    ∃ t s', Exec isa keyGen s t s' ∧ abiPreserved s s' ∧ keyGen1024AArch64.post s s' :=
  correct hs

theorem keyGen_verified :
    Verified AArch64.target keyGen (Spec.MlKem1024.keyGenContract AArch64.abi 16) :=
  Verified.of_correct keyGen_correct ct (by
    mlkem_implies [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, keyGen1024AArch64,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem1024.AArch64.KeyGen
