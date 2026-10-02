import VerifiedGarbage.Proof.MlKem1024.AArch64.DecapsCmp

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`

Correctness is the first phase (`a_ok`: `m'`, `G(m' ‖ h)`, `ρ`), the matrix
(`matrix_ok`), then `c'` (`encrypt_ok`), `K̄`, the comparison, the key and the
epilogue (`c_ok`).

Constant time up to `ρ`, relating two runs from states that agree on the
pointers and on `ρ`: the first and last phases by the taint analysis (which
the comparison and the choice of the key pass: they do not branch), the
matrix by `matrix_rct`.
-/

namespace VG.Proof.MlKem1024.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KEM VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash hashWith copy32 slotReg argReg kemOwn)
open VG.Proof.MlKem1024.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

theorem encArgs : EncArgs deL 0 1536 3 CB :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, .inr rfl⟩

theorem drop_take_slice (L : List Byte) {a n b c : Nat} (h : b + c ≤ n) :
    (((L.drop a).take n).drop b).take c = (L.drop (a + b)).take c := by
  rw [slice_take _ h, List.drop_drop]

theorem ekT_eq (s₀ : State) : ∀ j < 4,
    decode12 (bytesAt s₀.mem (kA s₀ (deL.slot 0) + BitVec.ofNat 64 (1536 + 384 * j)) 384) =
      ekT (dkEk1024 (dkD s₀)) j := fun j hj => by
  rw [ekT, dkEk1024, KPke.dkEk, drop_take_slice _ (show 384 * j + 384 ≤ 384 * mlKem1024.k + 32 by show _ ≤ 1568; omega),
    show 384 * mlKem1024.k = 1536 from rfl,
    bytesAt_slice _ _ (show 1536 + 384 * j + 384 ≤ 3168 by omega)]
  rfl

/-- `c'`. -/
abbrev cpr (s₀ : State) (mB : Mem) : List Byte := ct1024 (aM deL s₀ mB) (dkEk1024 (dkD s₀)) (mD s₀) (gD s₀).2

/-- `K̄ = J(z ‖ c)`. -/
abbrev jD (s₀ : State) : List Byte := J (dkZ1024 (dkD s₀) ++ cD s₀)

/-- What the function leaves. -/
structure Done (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = if cD s₀ = cpr s₀ mB then (gD s₀).1 else jD s₀

/-- A buffer of `scratch` below `ŷ` apart from what `K-PKE.Encrypt` writes. -/
theorem far_encW {s₀ : State} (hp : Pre deL s₀) {o l : Nat} (h1 : 840 ≤ o) (h2 : o + l ≤ RB + 32 ∨ RB + 33 ≤ o)
    (h3 : o + l ≤ PB) : ∀ r ∈ encW deL s₀ 3 CB, (R (kA s₀) deL.sc o l).Disjoint r := by
  have f : o + l ≤ 49152 := by simp only [PB] at h3; omega
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact sdisj hp f (by decide) (.inr (by omega))
  · exact sdisj hp f (by decide) (by simp only [RB] at h2 ⊢; omega)
  · exact sdisj hp f (by decide) (.inl h3)
  · exact below_R hp hp.scb (by rw [hp.scl]; exact f)
  · exact sdisj hp f (by decide) (.inl (by simp only [PB, CB] at h3 ⊢; omega))

theorem c_ok {s₀ : State} (hp : Pre deL s₀) {uA sB : State} (hA : AfterA s₀ uA)
    (hB : BInv deL s₀ uA.mem (rhoD s₀) 16 sB) : WP isa (deCWith keccak.callee) sB (Done s₀ sB.mem (sB.gpr .x24)) := by
  have fbw : ∀ {o l : Nat}, o + l ≤ 49152 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW deL s₀, (R (kA s₀) deL.sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by decide) h1
      · exact sdisj hp f (by decide) (.inl h2)
      · exact sdisj hp f (by decide) h3
      · exact below_R hp hp.scb f
  have r₀ : bytesAt sB.mem (sA deL s₀ RB) 32 = (gD s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m₀ : bytesAt sB.mem (sA deL s₀ MB) 32 = mD s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have kp₀ : bytesAt sB.mem (sA deL s₀ KP) 32 = (gD s₀).1 := by
    rw [bytesAt_frame hB.fr (fbw (o := KP) (l := 32) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.kp
  have e0 : EInv deL s₀ 3 CB sB.mem sB.mem (sB.gpr .x24) (gD s₀).2 (mD s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r₀, m₀, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  -- `c'`
  refine WP.seq (WP.mono (encrypt_ok hp encArgs (T := ekT (dkEk1024 (dkD s₀))) (ekT_eq s₀) e0)
    fun s₁ ⟨e₁, v₁⟩ => ?_)
  have kb₁ := e₁.kb
  have c₁ : bytesAt s₁.mem (sA deL s₀ CB) 1568 = cpr s₀ sB.mem :=
    ct_at (U := fun i => compressEncode 11 (encU1024 (aM deL s₀ sB.mem) (gD s₀).2 i))
      (fun i hi => by rw [ptr_add]; exact e₁.u i hi) (by rw [ptr_add]; exact v₁)
  have kp₁ : bytesAt s₁.mem (sA deL s₀ KP) 32 = (gD s₀).1 := by
    rw [bytesAt_frame e₁.fr (far_encW hp (by decide) (by decide) (by decide)) (by decide)]; exact kp₀
  -- `K̄ = J(z ‖ c)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₁ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x25, 3136, 32⟩, ⟨.x26, 0, 1568⟩]) (outs := [⟨.x28, JB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 0) hp kb₁ (by decide) (by decide) (.inl (by decide)) (by decide) (by decide)
      · exact pieceOk (k := 1) hp kb₁ (by decide) (by decide) (.inl (by decide)) (by decide) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₁ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have kb₂ := kb₁.hash hp k₂ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, JB, 32, rfl, by decide, by decide, by decide, .inr (.inr (by decide))⟩
  have msg : (List.map (pbytes s₁) [⟨.x25, 3136, 32⟩, ⟨.x26, 0, 1568⟩]).flatten = dkZ1024 (dkD s₀) ++ cD s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb₁.x25, kb₁.x26]
    have hc : bytesAt s₁.mem (kA s₀ (deL.slot 1)) 1568 = cD s₀ := kb₁.ro (b := 1) (by decide)
    rw [slice_eq kb₁ (b := 0) (by decide) (by decide), ptr_zero, hc]
    rfl
  have jb₂ : bytesAt s₂.mem (sA deL s₀ JB) 32 = jD s₀ := by
    obtain ⟨o, -⟩ := o₂
    rw [msg, e28 kb₁] at o
    rw [o]; show _ = J (dkZ1024 (dkD s₀) ++ cD s₀); rw [J_eq]; rfl
  have k₂' := k₂
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₁.x28, kb₁.sp] at k₂'
  have far₂ : ∀ {o l : Nat}, o + l ≤ 49152 → 840 ≤ o → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt s₂.mem (sA deL s₀ o) l = bytesAt s₁.mem (sA deL s₀ o) l := fun f h1 h2 => by
    refine bytesAt_frame k₂'.frame (fun r hr => ?_) (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp f (by decide) (.inr (by simp only [KEM.ST]; omega))
    · exact sdisj hp f (by decide) (.inr (by simp only [KEM.WK]; omega))
    · exact below_R hp hp.scb (by rw [hp.scl]; exact f)
    · exact sdisj hp f (by decide) h2
  have c₂ : bytesAt s₂.mem (sA deL s₀ CB) 1568 = cpr s₀ sB.mem := by
    rw [far₂ (by decide) (by decide) (by decide)]; exact c₁
  have kp₂ : bytesAt s₂.mem (sA deL s₀ KP) 32 = (gD s₀).1 := by
    rw [far₂ (by decide) (by decide) (by decide)]; exact kp₁
  have x24₂ : s₂.gpr .x24 = sB.gpr .x24 := by rw [k₂.cs _ (by decide) (by decide), e₁.x24]
  -- `c = c'`
  refine WP.seq (WP.mono (cmp_ok hp kb₂ c₂) fun s₃ ⟨k₃, m₃, x₃⟩ => ?_)
  have kb₃ := kb₂.block k₃ m₃ (by decide)
  -- the key
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok hp kb₃ (e := decide (cD s₀ = cpr s₀ sB.mem)) (by
    rw [x₃]; by_cases h : cD s₀ = cpr s₀ sB.mem <;> simp [h])) fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact safe_R hp (b := 2) ⟨by decide, by decide⟩ (by decide) (.inl (by decide))
  refine WP.mono (epilogue_ok hp kb₄) fun s' ⟨abi, x0, hm⟩ => ⟨abi, ?_, ?_⟩
  · rw [x0, k₄.get .x24, k₃.get .x24, x24₂]
  · rw [hm, b₄, m₃, kp₂, jb₂]
    by_cases h : cD s₀ = cpr s₀ sB.mem <;> simp [h]

/-! ## Correctness -/

theorem post_of {s₀ sB s' : State} {mA : Mem} (hB : BInv deL s₀ mA (rhoD s₀) 16 sB)
    (hD : Done s₀ sB.mem (sB.gpr .x24) s') : decaps1024AArch64.post s₀ s' := by
  show Outcome (fun iters => decapsInternal mlKem1024 iters (bytesAt s₀.mem (s₀.gpr .x0) 3168)
    (bytesAt s₀.mem (s₀.gpr .x1) 1568)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s₀.gpr .x2) 32)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 =
      if cD s₀ = cpr s₀ sB.mem then (gD s₀).1 else jD s₀ := hD.key
  rw [key, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show decapsInternal mlKem1024 280 (dkD s₀) (cD s₀) = _
    rw [decapsInternal1024, kpkeEncrypt1024_some (a := aM deL s₀ sB.mem) fun i hi j hj => by
      rw [KPke.ekRho_dkEk]; exact hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show decapsInternal mlKem1024 280 (dkD s₀) (cD s₀) = none
    rw [decapsInternal1024, kpkeEncrypt1024_none hi hj (by rw [KPke.ekRho_dkEk]; exact hn)]
    rfl

theorem correct {s₀ : State} (hs : decaps1024AArch64.pre s₀) :
    WP isa (decapsWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ decaps1024AArch64.post s₀ s' := by
  have hp := pre_of hs
  exact WP.seq (WP.mono (a_ok hp) fun _ hA => WP.seq (WP.mono
    (matrix_ok hp (BInv.zero hA.kb hA.x24 hA.rho)) fun _ hB =>
    WP.mono (c_ok hp hA hB) fun _ hD => ⟨hD.abi, post_of hB hD⟩))

/-! ## Constant time -/

/-- Two runs from states the contract relates. -/
abbrev Pub3 (σ₁ σ₂ : State) : Prop :=
  decaps1024AArch64.pre σ₁ ∧ decaps1024AArch64.pre σ₂ ∧ decaps1024AArch64.pub σ₁ σ₂

theorem Pub3.two {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : Two deL σ₁ σ₂ :=
  ⟨pre_of h.1, pre_of h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem Pub3.rho {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : rhoD σ₁ = rhoD σ₂ :=
  VG.Proof.MlKem.map_toNat_inj h.2.2.2.2.2.2.2

theorem b_rct : RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, Pub3 σ₁ σ₂ ∧ AfterA σ₁ s₁ ∧ AfterA σ₂ s₂) (kemMatrixWith keccak.callee)
    fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, Pub3 σ₁ σ₂ ∧ BInv deL σ₁ m₁ (rhoD σ₁) 16 s₁ ∧ BInv deL σ₂ m₂ (rhoD σ₁) 16 s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State × Mem × Mem) s₁ s₂ =>
      Pub3 x.1 x.2.1 ∧ BInv deL x.1 x.2.2.1 (rhoD x.1) 0 s₁ ∧ BInv deL x.2.1 x.2.2.2 (rhoD x.1) 0 s₂)
      fun x => ?_)
    (fun s₁ s₂ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂, s₁.mem, s₂.mem), hpub, BInv.zero a₁.kb a₁.x24 a₁.rho,
      BInv.zero a₂.kb a₂.x24 (by rw [a₂.rho, hpub.rho])⟩) fun _ _ h => h
  by_cases hpub : Pub3 x.1 x.2.1
  · exact RelCT.mono (matrix_rct hpub.two) (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hpub, h⟩
  · exact RelCT.of_false fun _ _ h => hpub h.1

theorem c_rct : RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, Pub3 σ₁ σ₂ ∧ BInv deL σ₁ m₁ (rhoD σ₁) 16 s₁ ∧
    BInv deL σ₂ m₂ (rhoD σ₁) 16 s₂) (deCWith keccak.callee) fun _ _ => True :=
  VectorTaint.relCT (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (fun s₁ s₂ ⟨σ₁, σ₂, m₁, m₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, hpub.two.sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25]; exact hpub.2.2.1
      · rw [b₁.kb.x26, b₂.kb.x26]; exact hpub.2.2.2.1
      · rw [b₁.kb.x27, b₂.kb.x27]; exact hpub.2.2.2.2.1
      · rw [b₁.kb.x28, b₂.kb.x28]; exact hpub.2.2.2.2.2.1) keccak.mlkem1024DeCTaint.choose_spec

theorem ct : ConstantTime isa decaps1024AArch64.pre decaps1024AArch64.pub (decapsWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, -, -⟩ := h
        simp [e0, e1, e2, e3])) keccak.mlkem1024DeATaint.choose_spec).wpDep (F := fun σ s => AfterA σ s)
      fun _ _ h => ⟨a_ok (pre_of h.1), a_ok (pre_of h.2.1)⟩)
    (RelCT.seq b_rct c_rct))

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem decaps_correctWith (s : State) (hs : decaps1024AArch64.pre s) :
    ∃ t s', Exec isa (decapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ decaps1024AArch64.post s s' :=
  correct hs

theorem decaps_verifiedWith :
    Verified AArch64.target (decapsWith keccak.callee) (Spec.MlKem1024.decapsContract AArch64.abi 16) :=
  Verified.of_correct (decaps_correctWith (keccak := keccak)) (ct (keccak := keccak)) (by
    mlkem_implies [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decaps1024AArch64,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem decaps_verified :
    Verified AArch64.target decaps (Spec.MlKem1024.decapsContract AArch64.abi 16) :=
  decaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem1024.AArch64.Decaps
