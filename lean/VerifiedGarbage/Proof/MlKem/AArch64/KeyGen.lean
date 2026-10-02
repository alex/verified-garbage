import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd

/-!
# ML-KEM on AArch64: `vg_mlkem768_keygen` and `vg_mlkem1024_keygen`

Correctness is the prologue and `G` (`a_ok`), the matrix (`b_ok`), then `ŝ`,
`ê`, `t̂` and the end (`c_ok`); the result is 1 exactly when every `SampleNTT`
finishes within 280 iterations (`post_of`).

Constant time up to `ρ`, relating two runs (`RelCT`) from states that agree
on the pointers and on `ρ`: the prologue and `G`, and everything after the
matrix, by the taint analysis (their addresses and branches depend only on
the pointers); each entry of the matrix by the taint analysis for the
arguments of `sample_ntt`, then `sample_ntt`'s own constant time
(`RelCT.call`), since both runs call it on the same seed `ρ ‖ j ‖ i`.

The proof is stated once for a well-formed parameter set (`KemLay.Wf`),
with the taint analyses of its code (`KgTaints`), which are decided on the
code of each parameter set; the end of this file is ML-KEM-768's instance
(and `Proof/MlKem1024/AArch64/KeyGen.lean` ML-KEM-1024's).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-! ## Correctness -/

theorem a_ok {s₀ : State} (hp : Pre P s₀) : WP isa (P.kgAWith keccak.callee) s₀ (AfterA P s₀) :=
  WP.seq (WP.mono (prologue_ok hp) fun _ h => g_ok hp h)

theorem c_ok {s₀ : State} (hp : Pre P s₀) {s : State} (h : BInv P s₀ (P.k * P.k) s) :
    WP isa (P.kgCWith keccak.callee) s (Done P s₀ s.mem (s.gpr .x24)) := by
  have k1 := hp.wf.facts.1
  have c : CInv P s₀ s.mem (s.gpr .x24) s := ⟨h.kb, h.rho, h.sig, rfl, fun e he => ⟨h.red e he, rfl⟩⟩
  have s0 : SInv P s₀ s.mem (s.gpr .x24) 0 s :=
    ⟨c, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (WPs.range (I := SInv P s₀ s.mem (s.gpr .x24))
    (fun j hj _ h => s_step hp hj h) s0) fun s₁ h₁ => ?_)))
  have t0 : TL P s₀ s.mem (s.gpr .x24) 0 s₁ := ⟨h₁.c, h₁.sp, h₁.dk, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WPs.mono (WPs.range (I := TL P s₀ s.mem (s.gpr .x24)) (fun i hi _ h => t_step hp hi h) t0)
    fun s₂ h₂ => WPs.single (end_ok hp h₂)

theorem post_of {s₀ sB s' : State} (hB : BInv P s₀ (P.k * P.k) sB) (hD : Done P s₀ sB.mem (sB.gpr .x24) s') :
    (keyGenAArch64 P).post s₀ s' := by
  show Outcome (fun iters => keyGenInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) 32)
    (bytesAt s₀.mem (s₀.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x1) P.ekLen, bytesAt s'.mem (s₀.gpr .x2) P.dkLen)
  have ed : bytesAt s₀.mem (s₀.gpr .x0) 32 = dB s₀ := by
    show _ = bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 0) 32
    rw [ptr_zero]
  have ez : bytesAt s₀.mem (s₀.gpr .x0 + 32) 32 = zB s₀ := rfl
  have ek : bytesAt s'.mem (s₀.gpr .x1) P.ekLen = KPke.ekPKE P.params (aM P s₀ sB.mem) (dB s₀) := hD.ek
  have dk : bytesAt s'.mem (s₀.gpr .x2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aM P s₀ sB.mem) (dB s₀) ++ H (KPke.ekPKE P.params (aM P s₀ sB.mem) (dB s₀)) ++
      zB s₀ := hD.dk
  rw [ed, ez, ek, dk, hD.x0, hB.acc]
  by_cases hA : allOk P s₀ (P.k * P.k)
  · rw [ite_eq_left hA]
    refine .inl ⟨rfl, 280, ?_⟩
    show keyGenInternal P.params 280 (dB s₀) (zB s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some (p := P.params) rfl (a := aM P s₀ sB.mem)
      fun i hi j hj => ?_]
    · rfl
    · have hi : i < P.k := hi
      have hj : j < P.k := hj
      have he : P.k * i + j < P.k * P.k := ij_lt hi hj
      have hke := ij_div (i := i) hj
      have r := hB.res (P.k * i + j) he
      have ok := hA (P.k * i + j) he
      rw [hke.1, hke.2] at r ok
      rcases r with r | r
      · rw [r] at ok; simp at ok
      · exact r
  · rw [ite_eq_right hA]
    refine .inr ⟨rfl, ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed (rhoK P s₀) (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    show keyGenInternal P.params 280 _ _ = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (p := P.params) (i := e / P.k) (j := e % P.k)
      (div_lt he) (mod_lt he) (Option.not_isSome_iff_eq_none.mp hn)]
    rfl

theorem correct (hP : P.Wf) {s₀ : State} (hs : (keyGenAArch64 P).pre s₀) :
    WP isa (P.keyGenWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ (keyGenAArch64 P).post s₀ s' := by
  have hp := pre_of hP hs
  exact WP.seq (WP.mono (a_ok hp) fun _ hA => WP.seq (WP.mono (b_ok hp hA) fun _ hB =>
    WP.mono (c_ok hp hB) fun _ hD => ⟨hD.abi, post_of hB hD⟩))

/-! ## Constant time -/

/-- The taint analyses of `P`'s code, decided for each parameter set: the
code before and after the matrix (with the Keccak functions `keccak`), and
the arguments of each `sample_ntt`. -/
structure KgTaints (P : KemLay) (keccak : VG.Proof.Sha3.AArch64.Permutation) : Prop where
  a : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (P.kgAWith keccak.callee) h).isSome = true
  c : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (P.kgCWith keccak.callee) h).isSome = true
  setup : ∀ i < P.k, ∀ j < P.k, ∃ hc : Taint.Hint taint.T,
    (taint.check (Taint.ofRegs [.x28]) (.block (P.kgSetup i j)) hc).isSome = true

/-- Two runs from states the contract relates. -/
abbrev Pub3 (P : KemLay) (σ₁ σ₂ : State) : Prop :=
  (keyGenAArch64 P).pre σ₁ ∧ (keyGenAArch64 P).pre σ₂ ∧ (keyGenAArch64 P).pub σ₁ σ₂

theorem Pub3.kA {σ₁ σ₂ : State} (h : Pub3 P σ₁ σ₂) : ∀ b, kA σ₁ b = kA σ₂ b
  | 0 => h.2.2.1
  | 1 => h.2.2.2.1
  | 2 => h.2.2.2.2.1
  | _ + 3 => h.2.2.2.2.2.1

theorem Pub3.sp {σ₁ σ₂ : State} (h : Pub3 P σ₁ σ₂) : σ₁.sp = σ₂.sp := h.2.2.2.2.2.2.1

theorem Pub3.rho {σ₁ σ₂ : State} (h : Pub3 P σ₁ σ₂) : rhoK P σ₁ = rhoK P σ₂ := by
  have e := map_toNat_inj h.2.2.2.2.2.2.2
  show KPke.kgRho P.params (bytesAt σ₁.mem (σ₁.gpr .x0 + BitVec.ofNat 64 0) 32) =
    KPke.kgRho P.params (bytesAt σ₂.mem (σ₂.gpr .x0 + BitVec.ofNat 64 0) 32)
  rw [ptr_zero, ptr_zero]
  exact e

variable (hP : P.Wf)
include hP

/-- `SampleNTT` on the same seed in both runs. -/
theorem call_rct {σ₁ σ₂ : State} (hpub : Pub3 P σ₁ σ₂) {i j : Nat} (hi : i < P.k) (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => Mid P σ₁ i j s₁ ∧ Mid P σ₂ i j s₂) (kgCallWith keccak.callee) fun _ _ => True := by
  have hp₁ := pre_of hP hpub.1
  have hp₂ := pre_of hP hpub.2.1
  refine RelCT.seq (RelCT.wp (F₁ := fun s : State => s.sp = σ₁.sp) (F₂ := fun s : State => s.sp = σ₂.sp)
    (sample_ctWith keccak (sd := kA σ₁ 3 + BitVec.ofNat 64 SB) (a := kA σ₁ 3 + BitVec.ofNat 64 (aOff P i j))
      (w := kA σ₁ 3 + BitVec.ofNat 64 SS) fun s₁ s₂ h => ?_) fun s₁ s₂ h => ⟨?_, ?_⟩)
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => agree_of (by rw [h.2.1, h.2.2, hpub.sp])
      fun r hr => by cases hr) (by taint_decide))
  · have A₂ := h.2.args hp₂ hi hj
    rw [← hpub.kA 3] at A₂
    refine ⟨h.1.args hp₁ hi hj, A₂, ?_, by rw [h.1.b.kb.sp, h.2.b.kb.sp, hpub.sp]⟩
    rw [h.1.seed, hpub.kA 3, h.2.seed, hpub.rho]
  · exact WP.mono ((h.1.args hp₁ hi hj).spWith keccak) fun s' e => by rw [e, h.1.b.kb.sp]
  · exact WP.mono ((h.2.args hp₂ hi hj).spWith keccak) fun s' e => by rw [e, h.2.b.kb.sp]

/-- `Â[i, j]` in both runs. -/
theorem sample_rct (ht : KgTaints P keccak) {σ₁ σ₂ : State} (hpub : Pub3 P σ₁ σ₂) {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => BInv P σ₁ (P.k * i + j) s₁ ∧ BInv P σ₂ (P.k * i + j) s₂)
      (P.kgSampleWith keccak.callee i j)
      fun s₁ s₂ => BInv P σ₁ (P.k * i + j + 1) s₁ ∧ BInv P σ₂ (P.k * i + j + 1) s₂ := by
  have hp₁ := pre_of hP hpub.1
  have hp₂ := pre_of hP hpub.2.1
  have hck := (ht.setup i hi j hj).choose_spec
  refine RelCT.seq (R := fun s₁ s₂ => Mid P σ₁ i j s₁ ∧ Mid P σ₂ i j s₂)
    (RelCT.mono (RelCT.wp (F₁ := Mid P σ₁ i j) (F₂ := Mid P σ₂ i j)
      (RelCT.taint (A := taint) (Taint.ofRegs [.x28]) (fun s₁ s₂ h =>
        agree_of (by rw [h.1.kb.sp, h.2.kb.sp, hpub.sp]) fun r hr => by
          rw [List.mem_singleton.mp hr, h.1.kb.x28, h.2.kb.x28, hpub.kA 3]) hck)
      fun s₁ s₂ h => ⟨setup_ok hp₁ hi hj h.1, setup_ok hp₂ hi hj h.2⟩) (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono (RelCT.wp (F₁ := BInv P σ₁ (P.k * i + j + 1)) (F₂ := BInv P σ₂ (P.k * i + j + 1))
      (call_rct hP hpub hi hj) fun s₁ s₂ h => ⟨call_ok hp₁ hi hj h.1, call_ok hp₂ hi hj h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)

theorem b_rct (ht : KgTaints P keccak) :
    RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, Pub3 P σ₁ σ₂ ∧ AfterA P σ₁ s₁ ∧ AfterA P σ₂ s₂)
      (P.kgBWith keccak.callee)
      fun s₁ s₂ => ∃ σ₁ σ₂, Pub3 P σ₁ σ₂ ∧ BInv P σ₁ (P.k * P.k) s₁ ∧ BInv P σ₂ (P.k * P.k) s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State) s₁ s₂ =>
      Pub3 P x.1 x.2 ∧ BInv P x.1 0 s₁ ∧ BInv P x.2 0 s₂) fun x => ?_)
    (fun _ _ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂), hpub, BInv.zero a₁, BInv.zero a₂⟩) fun _ _ h => h
  by_cases hpub : Pub3 P x.1 x.2
  · refine RelCT.mono (P := fun s₁ s₂ => BInv P x.1 0 s₁ ∧ BInv P x.2 0 s₂)
      (Q := fun s₁ s₂ => BInv P x.1 (P.k * P.k) s₁ ∧ BInv P x.2 (P.k * P.k) s₂) ?_ (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2, hpub, h⟩
    exact RelCTs.seqs (matrix_ne_nil hP.facts.1) (RelCTs.matrix (I := fun e s₁ s₂ => BInv P x.1 e s₁ ∧ BInv P x.2 e s₂)
      (fun i hi j hj => sample_rct hP ht hpub hi hj) (Nat.le_refl _))
  · exact RelCT.of_false fun _ _ h => hpub h.1

omit hP in
theorem c_rct (ht : KgTaints P keccak) :
    RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂, Pub3 P σ₁ σ₂ ∧ BInv P σ₁ (P.k * P.k) s₁ ∧ BInv P σ₂ (P.k * P.k) s₂)
      (P.kgCWith keccak.callee) fun _ _ => True :=
  VectorTaint.relCT (Taint.ofRegs [.x25, .x26, .x27, .x28]) (fun s₁ s₂ ⟨σ₁, σ₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, hpub.sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25, hpub.kA 0]
      · rw [b₁.kb.x26, b₂.kb.x26, hpub.kA 1]
      · rw [b₁.kb.x27, b₂.kb.x27, hpub.kA 2]
      · rw [b₁.kb.x28, b₂.kb.x28, hpub.kA 3]) ht.c.choose_spec

theorem ct (ht : KgTaints P keccak) :
    ConstantTime isa (keyGenAArch64 P).pre (keyGenAArch64 P).pub (P.keyGenWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, -, -⟩ := h
        simp [e0, e1, e2, e3])) ht.a.choose_spec).wpDep (F := fun σ s => AfterA P σ s)
      fun _ _ h => ⟨a_ok (pre_of hP h.1), a_ok (pre_of hP h.2.1)⟩)
    (RelCT.seq (b_rct hP ht) (c_rct ht)))

theorem keyGen_correct {s : State} (hs : (keyGenAArch64 P).pre s) :
    ∃ t s', Exec isa (P.keyGenWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (keyGenAArch64 P).post s s' :=
  correct hP hs

omit hP

/-! ## ML-KEM-768 -/

theorem wf768 : lay768.Wf := ⟨by decide⟩

theorem taints768 : KgTaints lay768 keccak :=
  ⟨keccak.mlkemKgATaint, keccak.mlkemKgCTaint, by
    intro i hi j hj
    change i < 3 at hi
    change j < 3 at hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
    exact ⟨_, by taint_decide⟩⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem keyGen_correctWith (s : State) (hs : (keyGenAArch64 lay768).pre s) :
    ∃ t s', Exec isa (keyGenWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (keyGenAArch64 lay768).post s s' :=
  keyGen_correct wf768 hs

theorem keyGen_verifiedWith :
    Verified AArch64.target (keyGenWith keccak.callee) (Spec.MlKem.keyGenContract AArch64.abi 16) :=
  Verified.of_correct (keyGen_correctWith (keccak := keccak)) (ct wf768 taints768) (by
    mlkem_implies [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenAArch64, lay768, KemLay.params, Spec.MlKem.mlKem768,
      KemLay.ekLen, KemLay.dkLen, AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem keyGen_verified :
    Verified AArch64.target keyGen (Spec.MlKem.keyGenContract AArch64.abi 16) :=
  keyGen_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem.AArch64.KeyGen
