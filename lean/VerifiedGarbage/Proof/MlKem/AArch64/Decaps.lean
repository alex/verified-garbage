import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp
import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-!
# ML-KEM on AArch64: `vg_mlkem768_decaps` and `vg_mlkem1024_decaps`

Correctness is the first phase (`a_ok`: `m'`, `G(m' ‖ h)`, `ρ`), the matrix
(`matrix_ok`), then `c'` (`encrypt_ok`), `K̄`, the comparison, the key and the
epilogue (`c_ok`).

Constant time up to `ρ`, relating two runs from states that agree on the
pointers and on `ρ`: the first and last phases by the taint analysis (which
the comparison and the choice of the key pass: they do not branch), the
matrix by `matrix_rct`.

The proof is stated once for a well-formed parameter set, with the taint
analyses of its code (`DeTaints`) decided on each; the end of this file is
ML-KEM-768's instance (and `Proof/MlKem1024/AArch64/Decaps.lean` ML-KEM-1024's).
-/

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

theorem encArgs (hP : P.Wf) : EncArgs P (deL P) 0 (384 * P.k) 3 (CB P) :=
  ⟨by decide, by dek, by simp only [deL, List.getD_cons_zero]; lom, by decide, by dek,
    by simp only [deL, List.getD_cons_succ, List.getD_cons_zero]; lom, .inr rfl⟩

theorem drop_take_slice (L : List Byte) {a n b c : Nat} (h : b + c ≤ n) :
    (((L.drop a).take n).drop b).take c = (L.drop (a + b)).take c := by
  rw [slice_take _ h, List.drop_drop]

theorem ekT_eq (s₀ : State) : ∀ j < P.k,
    decode12 (bytesAt s₀.mem (kA s₀ ((deL P).slot 0) + BitVec.ofNat 64 (384 * P.k + 384 * j)) 384) =
      ekT (KPke.dkEk P.params (dkD P s₀)) j := fun j hj => by
  have := mul_succ_le (a := 384) hj
  rw [ekT, KPke.dkEk, drop_take_slice _ (show 384 * j + 384 ≤ 384 * P.params.k + 32 by
      show _ ≤ 384 * P.k + 32; omega), show 384 * P.params.k = 384 * P.k from rfl,
    bytesAt_slice _ _ (show 384 * P.k + 384 * j + 384 ≤ P.dkLen by simp only [KemLay.dkLen]; omega)]
  rfl

/-- `c'`. -/
abbrev cpr (P : KemLay) (s₀ : State) (mB : Mem) : List Byte :=
  KPke.ct P.params (aM P (deL P) s₀ mB) (KPke.dkEk P.params (dkD P s₀)) (mD P s₀) (gD P s₀).2

/-- `K̄ = J(z ‖ c)`. -/
abbrev jD (P : KemLay) (s₀ : State) : List Byte := J (KPke.dkZ P.params (dkD P s₀) ++ cD P s₀)

/-- What the function leaves. -/
structure Done (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = if cD P s₀ = cpr P s₀ mB then (gD P s₀).1 else jD P s₀

/-- A buffer of `scratch` below `ŷ` apart from what `K-PKE.Encrypt` writes. -/
theorem far_encW {s₀ : State} (hp : Pre P (deL P) s₀) {o l : Nat} (h1 : 840 ≤ o)
    (h2 : o + l ≤ RB + 32 ∨ RB + 33 ≤ o) (h3 : o + l ≤ PB) :
    ∀ r ∈ encW P (deL P) s₀ 3 (CB P), (R (kA s₀) (deL P).sc o l).Disjoint r := by
  have hw := hp.wf
  have f : o + l ≤ SV P + 48 := by lom
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact sdisj hp f (by lom) (.inr (by omega))
  · exact sdisj hp f (by lom) (by simp only [RB] at h2 ⊢; omega)
  · exact sdisj hp f (by lom) (.inl h3)
  · exact below_R hp hp.scb (hp.fs f)
  · exact sdisj hp f (by lom) (.inl (by lom))

theorem c_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {uA sB : State} (hA : AfterA P s₀ uA)
    (hB : BInv P (deL P) s₀ uA.mem (rhoD P s₀) (P.k * P.k) sB) :
    WP isa (P.deCWith keccak.callee) sB (Done P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
  have fbw : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW P (deL P) s₀, (R (kA s₀) (deL P).sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by lom) h1
      · exact sdisj hp f (by lom) (.inl h2)
      · exact sdisj hp f (by lom) h3
      · exact below_R hp hp.scb (hp.fs f)
  have r₀ : bytesAt sB.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m₀ : bytesAt sB.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have kp₀ : bytesAt sB.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame hB.fr (fbw (o := KP) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.kp
  have e0 : EInv P (deL P) s₀ 3 (CB P) sB.mem sB.mem (sB.gpr .x24) (gD P s₀).2 (mD P s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r₀, m₀, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  -- `c'`
  refine WP.seq (WP.mono (encrypt_ok hp hc (encArgs hw) (T := ekT (KPke.dkEk P.params (dkD P s₀))) (ekT_eq s₀) e0)
    fun s₁ ⟨e₁, v₁⟩ => ?_)
  have kb₁ := e₁.kb
  have c₁ : bytesAt s₁.mem (sA (deL P) s₀ (CB P)) P.ctLen = cpr P s₀ sB.mem :=
    ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aM P (deL P) s₀ sB.mem) (gD P s₀).2 i))
      (fun i hi => by rw [ptr_add]; exact e₁.u i hi) (by rw [ptr_add]; exact v₁)
  have kp₁ : bytesAt s₁.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]; exact kp₀
  -- `K̄ = J(z ‖ c)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₁ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x25, 768 * P.k + 64, 32⟩, ⟨.x26, 0, P.ctLen⟩]) (outs := [⟨.x28, JB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 0) hp kb₁ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek)
      · exact pieceOk (k := 1) hp kb₁ (by decide) (by dek) (.inl (by dek)) (by dek) (by dek))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₁ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have kb₂ := kb₁.hash hp k₂ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, JB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by dek))⟩
  have msg : (List.map (pbytes s₁) [⟨.x25, 768 * P.k + 64, 32⟩, ⟨.x26, 0, P.ctLen⟩]).flatten =
      KPke.dkZ P.params (dkD P s₀) ++ cD P s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb₁.x25, kb₁.x26]
    have hc : bytesAt s₁.mem (kA s₀ ((deL P).slot 1)) P.ctLen = cD P s₀ := kb₁.ro (b := 1) (by dek)
    rw [slice_eq kb₁ (b := 0) (by decide) (by dek), ptr_zero, hc]
    rfl
  have jb₂ : bytesAt s₂.mem (sA (deL P) s₀ JB) 32 = jD P s₀ := by
    obtain ⟨o, -⟩ := o₂
    rw [msg, e28 kb₁] at o
    rw [o]; show _ = J (KPke.dkZ P.params (dkD P s₀) ++ cD P s₀); rw [J_eq]; rfl
  have k₂' := k₂
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₁.x28, kb₁.sp] at k₂'
  have far₂ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt s₂.mem (sA (deL P) s₀ o) l = bytesAt s₁.mem (sA (deL P) s₀ o) l := fun f h1 h2 => by
    refine bytesAt_frame k₂'.frame (fun r hr => ?_) (by lom)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (.inr (by simp only [KEM.ST]; omega))
    · exact sdisj hp f (by lom) (.inr (by simp only [KEM.WK]; omega))
    · exact below_R hp hp.scb (hp.fs f)
    · exact sdisj hp f (by lom) h2
  have c₂ : bytesAt s₂.mem (sA (deL P) s₀ (CB P)) P.ctLen = cpr P s₀ sB.mem := by
    rw [far₂ (by lom) (by lom) (by lom)]; exact c₁
  have kp₂ : bytesAt s₂.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [far₂ (by lom) (by decide) (by decide)]; exact kp₁
  have x24₂ : s₂.gpr .x24 = sB.gpr .x24 := by rw [k₂.cs _ (by decide) (by decide), e₁.x24]
  -- `c = c'`
  refine WP.seq (WP.mono (cmp_ok hp kb₂ c₂) fun s₃ ⟨k₃, m₃, x₃⟩ => ?_)
  have kb₃ := kb₂.block k₃ m₃ (by decide)
  -- the key
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok hp kb₃ (e := decide (cD P s₀ = cpr P s₀ sB.mem)) (by
    rw [x₃]; by_cases h : cD P s₀ = cpr P s₀ sB.mem <;> simp [h])) fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact safe_R hp (b := 2) ⟨by dek, by dek⟩ (by dek) (.inl (by dek))
  refine WP.mono (epilogue_ok hp kb₄) fun s' ⟨abi, x0, hm⟩ => ⟨abi, ?_, ?_⟩
  · rw [x0, k₄.get .x24, k₃.get .x24, x24₂]
  · rw [hm, b₄, m₃, kp₂, jb₂]
    by_cases h : cD P s₀ = cpr P s₀ sB.mem <;> simp [h]

/-! ## Correctness -/

theorem post_of {s₀ sB s' : State} {mA : Mem} (hB : BInv P (deL P) s₀ mA (rhoD P s₀) (P.k * P.k) sB)
    (hD : Done P s₀ sB.mem (sB.gpr .x24) s') : (decapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => decapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.dkLen)
    (bytesAt s₀.mem (s₀.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s₀.gpr .x2) 32)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 =
      if cD P s₀ = cpr P s₀ sB.mem then (gD P s₀).1 else jD P s₀ := hD.key
  rw [key, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩ (a := aM P (deL P) s₀ sB.mem)
      fun i hi j hj => by rw [KPke.ekRho_dkEk]; exact hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = none
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj (by rw [KPke.ekRho_dkEk]; exact hn)]
    rfl

theorem correct (hP : P.Wf) (hc : Calls P) {s₀ : State} (hs : (decapsAArch64 P).pre s₀) :
    WP isa (P.decapsWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ (decapsAArch64 P).post s₀ s' := by
  have hp := pre_of hP hs
  exact WP.seq (WP.mono (a_ok hp hc) fun _ hA => WP.seq (WP.mono
    (matrix_ok hp (BInv.zero hA.kb hA.x24 hA.rho)) fun _ hB =>
    WP.mono (c_ok hp hc hA hB) fun _ hD => ⟨hD.abi, post_of hB hD⟩))

/-! ## Constant time -/

/-- The taint analyses of `P`'s code, decided for each parameter set: the
code before and after the matrix (with the Keccak functions `keccak`), and
the arguments of each `sample_ntt`. -/
structure DeTaints (P : KemLay) (keccak : VG.Proof.Sha3.AArch64.Permutation) : Prop where
  a : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (P.deAWith keccak.callee) h).isSome = true
  c : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (P.deCWith keccak.callee) h).isSome = true
  setup : SetupTaint P

/-- Two runs from states the contract relates. -/
abbrev Pub3 (P : KemLay) (σ₁ σ₂ : State) : Prop :=
  (decapsAArch64 P).pre σ₁ ∧ (decapsAArch64 P).pre σ₂ ∧ (decapsAArch64 P).pub σ₁ σ₂

theorem Pub3.two (hP : P.Wf) {σ₁ σ₂ : State} (h : Pub3 P σ₁ σ₂) : Two P (deL P) σ₁ σ₂ :=
  ⟨pre_of hP h.1, pre_of hP h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem Pub3.rho {σ₁ σ₂ : State} (h : Pub3 P σ₁ σ₂) : rhoD P σ₁ = rhoD P σ₂ :=
  map_toNat_inj h.2.2.2.2.2.2.2

theorem b_rct (hP : P.Wf) (ht : DeTaints P keccak) :
    RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, Pub3 P σ₁ σ₂ ∧ AfterA P σ₁ s₁ ∧ AfterA P σ₂ s₂)
      (P.kemMatrixWith keccak.callee)
    fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, Pub3 P σ₁ σ₂ ∧ BInv P (deL P) σ₁ m₁ (rhoD P σ₁) (P.k * P.k) s₁ ∧
      BInv P (deL P) σ₂ m₂ (rhoD P σ₁) (P.k * P.k) s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State × Mem × Mem) s₁ s₂ =>
      Pub3 P x.1 x.2.1 ∧ BInv P (deL P) x.1 x.2.2.1 (rhoD P x.1) 0 s₁ ∧
        BInv P (deL P) x.2.1 x.2.2.2 (rhoD P x.1) 0 s₂)
      fun x => ?_)
    (fun s₁ s₂ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂, s₁.mem, s₂.mem), hpub, BInv.zero a₁.kb a₁.x24 a₁.rho,
      BInv.zero a₂.kb a₂.x24 (by rw [a₂.rho, hpub.rho])⟩) fun _ _ h => h
  by_cases hpub : Pub3 P x.1 x.2.1
  · exact RelCT.mono (matrix_rct ht.setup (hpub.two hP)) (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hpub, h⟩
  · exact RelCT.of_false fun _ _ h => hpub h.1

theorem c_rct (hP : P.Wf) (ht : DeTaints P keccak) :
    RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, Pub3 P σ₁ σ₂ ∧ BInv P (deL P) σ₁ m₁ (rhoD P σ₁) (P.k * P.k) s₁ ∧
      BInv P (deL P) σ₂ m₂ (rhoD P σ₁) (P.k * P.k) s₂) (P.deCWith keccak.callee) fun _ _ => True :=
  VectorTaint.relCT (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (fun s₁ s₂ ⟨σ₁, σ₂, m₁, m₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, (hpub.two hP).sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25]; exact hpub.2.2.1
      · rw [b₁.kb.x26, b₂.kb.x26]; exact hpub.2.2.2.1
      · rw [b₁.kb.x27, b₂.kb.x27]; exact hpub.2.2.2.2.1
      · rw [b₁.kb.x28, b₂.kb.x28]; exact hpub.2.2.2.2.2.1) ht.c.choose_spec

theorem ct (hP : P.Wf) (hc : Calls P) (ht : DeTaints P keccak) :
    ConstantTime isa (decapsAArch64 P).pre (decapsAArch64 P).pub (P.decapsWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, -, -⟩ := h
        simp [e0, e1, e2, e3])) ht.a.choose_spec).wpDep (F := fun σ s => AfterA P σ s)
      fun _ _ h => ⟨a_ok (pre_of hP h.1) hc, a_ok (pre_of hP h.2.1) hc⟩)
    (RelCT.seq (b_rct hP ht) (c_rct hP ht)))

theorem decaps_correct (hP : P.Wf) (hc : Calls P) {s : State} (hs : (decapsAArch64 P).pre s) :
    ∃ t s', Exec isa (P.decapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (decapsAArch64 P).post s s' :=
  correct hP hc hs

/-! ## ML-KEM-768 -/

theorem taints768 : DeTaints lay768 keccak :=
  ⟨keccak.mlkemDeATaint, keccak.mlkemDeCTaint, Encaps.setupTaint768⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem decaps_correctWith (s : State) (hs : (decapsAArch64 lay768).pre s) :
    ∃ t s', Exec isa (decapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (decapsAArch64 lay768).post s s' :=
  decaps_correct KeyGen.wf768 Encaps.calls768 hs

theorem decaps_verifiedWith :
    Verified AArch64.target (decapsWith keccak.callee) (Spec.MlKem.decapsContract AArch64.abi 16) :=
  Verified.of_correct (decaps_correctWith (keccak := keccak)) (ct KeyGen.wf768 Encaps.calls768 taints768) (by
    mlkem_implies [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsAArch64, lay768, KemLay.params,
      Spec.MlKem.mlKem768, KemLay.dkLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem decaps_verified :
    Verified AArch64.target decaps (Spec.MlKem.decapsContract AArch64.abi 16) :=
  decaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem.AArch64.Decaps
