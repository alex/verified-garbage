import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps

/-!
# ML-KEM-768 on AArch64: `vg_mlkem768_encaps`

Untrusted: everything here is checked by Lean. Correctness is the prologue,
`m`, `H(ek)`, `G(m ‖ H(ek))` and `ρ` (`a_ok`), the matrix (`matrix_ok`),
then `ŷ`, `u` and `v` (`encrypt_ok`) and the epilogue (`c_ok`).

Constant time up to `ρ`, relating two runs from states that agree on the
pointers and on `ρ`: the first and last phases by the taint analysis, the
matrix by `matrix_rct`.
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The contract the proof is written against; the artifact's is the
shared contract of `Spec/`, which implies it. AArch64 contract for
`(encapsWith keccak.callee)(ek = x0, m = x1, key = x2, ct = x3, scratch = x4) -> w0`. -/
def encapsAArch64 : Contract AArch64.isa where
  pre s :=
    let ek : Region := ⟨s.gpr .x0, 1184⟩
    let msg : Region := ⟨s.gpr .x1, 32⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let ct : Region := ⟨s.gpr .x3, 1088⟩
    let scratch : Region := ⟨s.gpr .x4, 32768⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [ek, msg] ∧ s.wr = [key, ct, scratch] ∧ ek.Disjoint key ∧ ek.Disjoint ct ∧
    ek.Disjoint scratch ∧ msg.Disjoint key ∧ msg.Disjoint ct ∧ msg.Disjoint scratch ∧ key.Disjoint ct ∧
    key.Disjoint scratch ∧ ct.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint ek ∧ stack.Disjoint msg ∧
    stack.Disjoint key ∧ stack.Disjoint ct ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => encapsInternal mlKem768 iters (bytesAt s.mem (s.gpr .x0) 1184)
        (bytesAt s.mem (s.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
      (bytesAt s'.mem (s.gpr .x2) 32, bytesAt s'.mem (s.gpr .x3) 1088)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
      leakRho (ekRho mlKem768 (bytesAt s₁.mem (s₁.gpr .x0) 1184)) =
        leakRho (ekRho mlKem768 (bytesAt s₂.mem (s₂.gpr .x0) 1184))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- 0 `ek`, 1 `m` (read); 2 `key`, 3 `ct`, 4 `scratch` (written); `ek`, `key`,
`ct` and `scratch` kept in `x25`–`x28`. -/
def enL : Layout where
  nb := 5
  nrd := 2
  len b := [1184, 32, 32, 1088, 32768].getD b 0
  slot k := [0, 2, 3, 4].getD k 4

theorem pre_of {s₀ : State} (h : encapsAArch64.pre s₀) : Pre enL s₀ := by
  obtain ⟨rd, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, sp16, k0, k1, k2, k3, k4⟩ := h
  refine ⟨by rw [rd]; rfl, by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    by decide, by decide, by decide⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [enL] at hb hc hw
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [enL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [enL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- `ek`. -/
abbrev ekE (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0) 1184
/-- `m`. -/
abbrev mE (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 1) 32
/-- `(K, r) = G(m ‖ H(ek))`. -/
abbrev gE (s₀ : State) : List Byte × List Byte := G (mE s₀ ++ H (ekE s₀))
/-- `ρ`. -/
abbrev rhoE (s₀ : State) : List Byte := ekRho mlKem768 (ekE s₀)

theorem sha3Suffix_eq : Spec.Sha3.sha3Suffix = BitVec.ofNat 8 6 := rfl

/-- After the first phase. -/
structure AfterA (s₀ s : State) : Prop where
  kb : KB enL s₀ s
  x24 : s.gpr .x24 = 1
  key : bytesAt s.mem (kA s₀ 2) 32 = (gE s₀).1
  r : bytesAt s.mem (sA enL s₀ RB) 32 = (gE s₀).2
  m : bytesAt s.mem (sA enL s₀ MB) 32 = mE s₀
  rho : bytesAt s.mem (sA enL s₀ SB) 32 = rhoE s₀

theorem a_ok {s₀ : State} (hp : Pre enL s₀) : WP isa (enAWith keccak.callee) s₀ (AfterA s₀) := by
  -- the prologue and `m`
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 1) (D := kA s₀ 4) (so := 0) (dO := MB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (by rw [h₁.keep.get .x1 (by decide)]; rfl) h₁.kb.x28
    (cov_r hp h₁.kb (b := 1) (by decide) (by decide)) (cov_s hp h₁.kb (by decide)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := h₁.kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by decide)
  have m₂ : bytesAt s₂.mem (sA enL s₀ MB) 32 = mE s₀ := by
    rw [show sA enL s₀ MB = kA s₀ 4 + BitVec.ofNat 64 MB from rfl, b₂,
      h₁.kb.ro_bytes (b := 1) (by decide) (by decide), ptr_zero]
  have x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, h₁.x24]
  -- `H(ek)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x25, 0, 1184⟩]) (outs := [⟨.x28, HB, 32⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 0) hp kb₂ (by decide) (by decide) (.inl (by decide)) (by decide) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₂ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, HB, 32, rfl, by decide, by decide, by decide, .inr (.inr (by decide))⟩
  have hek : bytesAt s₂.mem (s₂.gpr .x25 + BitVec.ofNat 64 0) 1184 = ekE s₀ := by
    rw [kb₂.x25, ptr_zero]
    exact kb₂.ro (b := 0) (by decide)
  have h₃ : bytesAt s₃.mem (sA enL s₀ HB) 32 = H (ekE s₀) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂] at o
    rw [hek] at o
    rw [o, H_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (sA enL s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact below_R hp hp.scb (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)) (by decide)]
    exact m₂
  -- `G(m ‖ H(ek))`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₃ (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]) (outs := [⟨.x26, 0, 32⟩, ⟨.x28, RB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 1) hp kb₃ (by decide) (by decide) (.inl (by decide)) (by decide) (by decide)
      · exact pieceOk (k := 3) hp kb₃ (by decide) (by decide) (.inr (by decide)) (by decide) (by decide))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, kb₃.x26, e28 kb₃]
      exact hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    fun s₄ ⟨k₄, o₄⟩ => ?_)
  have kb₄ := kb₃.hash hp k₄ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨1, 0, 32, rfl, by decide, by decide, by decide, .inl (by decide)⟩
    · exact ⟨3, RB, 32, rfl, by decide, by decide, by decide, .inr (.inr (by decide))⟩
  have msg : (List.map (pbytes s₃) [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]).flatten = mE s₀ ++ H (ekE s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₃]
    rw [m₃, h₃]
  obtain ⟨o₁, o₂, -⟩ := o₄
  rw [msg] at o₁ o₂
  have hG := G_eq (mE s₀ ++ H (ekE s₀))
  have key₄ : bytesAt s₄.mem (kA s₀ 2) 32 = (gE s₀).1 := by
    have e : kA s₀ 2 = s₃.gpr .x26 + BitVec.ofNat 64 0 := by rw [kb₃.x26, ptr_zero]; rfl
    rw [e, o₁]; show _ = (G (mE s₀ ++ H (ekE s₀))).1; rw [hG]; rfl
  have r₄ : bytesAt s₄.mem (sA enL s₀ RB) 32 = (gE s₀).2 := by
    rw [← e28 kb₃, o₂]; show _ = (G (mE s₀ ++ H (ekE s₀))).2; rw [hG]; rfl
  have k₄' := k₄
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₃.x28, kb₃.x26, kb₃.sp] at k₄'
  have m₄ : bytesAt s₄.mem (sA enL s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame k₄'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)
      · exact below_R hp hp.scb (by decide)
      · exact hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact sdisj hp (by decide) (by decide) (by decide)) (by decide)]
    exact m₃
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 4) (so := 1152) (dO := SB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) kb₄.x25 kb₄.x28 (cov_r hp kb₄ (b := 0) (by decide) (by decide)) (cov_s hp kb₄ (by decide)))
    fun s₅ ⟨k₅, f₅, b₅⟩ => ?_
  have kb₅ := kb₄.frame k₅ f₅ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by decide)
  have far₅ : ∀ {o l : Nat}, o + l ≤ 32768 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₅.mem (sA enL s₀ o) l = bytesAt s₄.mem (sA enL s₀ o) l := fun f h => by
    refine bytesAt_frame f₅ (fun r hr => ?_) (by omega)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by decide) h
  refine ⟨kb₅, by rw [k₅.get .x24, k₄.cs _ (by decide) (by decide), k₃.cs _ (by decide) (by decide), x24₂], ?_,
    by rw [far₅ (o := RB) (l := 32) (by decide) (by decide)]; exact r₄,
    by rw [far₅ (o := MB) (l := 32) (by decide) (by decide)]; exact m₄, ?_⟩
  · rw [bytesAt_frame f₅ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hp.args.disj 2 (by decide) 4 (by decide) (by decide) (by decide)).sub_right
        (R.sub (show SB + 32 ≤ 32768 by decide))) (by decide)]
    exact key₄
  · rw [show sA enL s₀ SB = kA s₀ 4 + BitVec.ofNat 64 SB from rfl, b₅,
      kb₄.ro_bytes (b := 0) (by decide) (by decide), ← bytesAt_slice _ _ (show 1152 + 32 ≤ 1184 by decide)]
    rfl

/-! ## `ŷ`, `u`, `v` and the epilogue -/

/-- What the function leaves. -/
structure Done (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = (gE s₀).1
  ct : bytesAt s.mem (kA s₀ 3) 1088 = ct768 (aM enL s₀ mB) (ekE s₀) (mE s₀) (gE s₀).2

theorem encArgs : EncArgs enL 0 0 2 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, .inl (by decide)⟩

theorem ekT_eq (s₀ : State) : ∀ j < 3,
    decode12 (bytesAt s₀.mem (kA s₀ (enL.slot 0) + BitVec.ofNat 64 (0 + 384 * j)) 384) = ekT (ekE s₀) j :=
  fun j hj => by
    rw [ekT, bytesAt_slice _ _ (show 384 * j + 384 ≤ 1184 by omega), Nat.zero_add]
    rfl

/-- The key is apart from what the rest writes. -/
theorem key_far {s₀ : State} (hp : Pre enL s₀) {r : Region}
    (h : r ∈ bW enL s₀ ∨ r ∈ encW enL s₀ 2 0) : Region.Disjoint ⟨kA s₀ 2, 32⟩ r := by
  have hs : ∀ {b o l : Nat}, b < 5 → b ≠ 2 → 2 ≤ b → o + l ≤ enL.len b →
      Region.Disjoint ⟨kA s₀ 2, 32⟩ (R (kA s₀) b o l) := fun hb hb2 hw f =>
    (hp.args.disj 2 (by decide) _ hb (Ne.symm hb2) (.inl (by decide))).sub_right (R.sub f)
  have hb : Region.Disjoint ⟨kA s₀ 2, 32⟩ (below s₀.sp 16) := by
    rw [below16]; exact (hp.args.stk 2 (by decide)).symm
  rcases h with h | h
  · rcases mem4 h with rfl | rfl | rfl | rfl
    · exact hs (b := 4) (by decide) (by decide) (by decide) (by decide)
    · exact hs (b := 4) (by decide) (by decide) (by decide) (by decide)
    · exact hs (b := 4) (by decide) (by decide) (by decide) (by decide)
    · exact hb
  · rcases mem5 h with rfl | rfl | rfl | rfl | rfl
    · exact hs (b := 4) (by decide) (by decide) (by decide) (by decide)
    · exact hs (b := 4) (by decide) (by decide) (by decide) (by decide)
    · exact hs (b := 4) (by decide) (by decide) (by decide) (by decide)
    · exact hb
    · exact hs (b := 3) (by decide) (by decide) (by decide) (by decide)

theorem c_ok {s₀ : State} (hp : Pre enL s₀) {uA sB : State} (hA : AfterA s₀ uA)
    (hB : BInv enL s₀ uA.mem (rhoE s₀) 9 sB) : WP isa (enCWith keccak.callee) sB (Done s₀ sB.mem (sB.gpr .x24)) := by
  have fbw : ∀ {o l : Nat}, o + l ≤ 32768 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW enL s₀, (R (kA s₀) enL.sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by decide) h1
      · exact sdisj hp f (by decide) (.inl h2)
      · exact sdisj hp f (by decide) h3
      · exact below_R hp hp.scb f
  have r : bytesAt sB.mem (sA enL s₀ RB) 32 = (gE s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m : bytesAt sB.mem (sA enL s₀ MB) 32 = mE s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by decide) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have key : bytesAt sB.mem (kA s₀ 2) 32 = (gE s₀).1 := by
    rw [bytesAt_frame hB.fr (fun r hr => key_far hp (.inl hr)) (by decide)]; exact hA.key
  have e0 : EInv enL s₀ 2 0 sB.mem sB.mem (sB.gpr .x24) (gE s₀).2 (mE s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r, m, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.seq (WP.mono (encrypt_ok hp encArgs (T := ekT (ekE s₀)) (ekT_eq s₀) e0) fun s₁ ⟨e₁, v₁⟩ => ?_)
  refine WP.mono (epilogue_ok hp e₁.kb) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, e₁.x24], ?_, ?_⟩
  · rw [hm, bytesAt_frame e₁.fr (fun r hr => key_far hp (.inr hr)) (by decide)]; exact key
  · rw [hm]
    exact ct_at (U := fun i => compressEncode 10 (encU (aM enL s₀ sB.mem) (gE s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)

/-! ## Correctness -/

theorem post_of {s₀ sB s' : State} {mA : Mem} (hB : BInv enL s₀ mA (rhoE s₀) 9 sB)
    (hD : Done s₀ sB.mem (sB.gpr .x24) s') : encapsAArch64.post s₀ s' := by
  show Outcome (fun iters => encapsInternal mlKem768 iters (bytesAt s₀.mem (s₀.gpr .x0) 1184)
    (bytesAt s₀.mem (s₀.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x2) 32, bytesAt s'.mem (s₀.gpr .x3) 1088)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 = (gE s₀).1 := hD.key
  have ct : bytesAt s'.mem (s₀.gpr .x3) 1088 = ct768 (aM enL s₀ sB.mem) (ekE s₀) (mE s₀) (gE s₀).2 := hD.ct
  rw [key, ct, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show encapsInternal mlKem768 280 (ekE s₀) (mE s₀) = _
    rw [encapsInternal768, kpkeEncrypt768_some (a := aM enL s₀ sB.mem) fun i hi j hj => hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show encapsInternal mlKem768 280 (ekE s₀) (mE s₀) = none
    rw [encapsInternal768, kpkeEncrypt768_none hi hj hn]
    rfl

theorem correct {s₀ : State} (hs : encapsAArch64.pre s₀) :
    WP isa (encapsWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ encapsAArch64.post s₀ s' := by
  have hp := pre_of hs
  exact WP.seq (WP.mono (a_ok hp) fun _ hA => WP.seq (WP.mono
    (matrix_ok hp (BInv.zero hA.kb hA.x24 hA.rho)) fun _ hB =>
    WP.mono (c_ok hp hA hB) fun _ hD => ⟨hD.abi, post_of hB hD⟩))

/-! ## Constant time -/

/-- Two runs from states the contract relates. -/
abbrev Pub3 (σ₁ σ₂ : State) : Prop :=
  encapsAArch64.pre σ₁ ∧ encapsAArch64.pre σ₂ ∧ encapsAArch64.pub σ₁ σ₂

theorem Pub3.two {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : Two enL σ₁ σ₂ :=
  ⟨pre_of h.1, pre_of h.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem Pub3.rho {σ₁ σ₂ : State} (h : Pub3 σ₁ σ₂) : rhoE σ₁ = rhoE σ₂ :=
  Sample.map_toNat_inj h.2.2.2.2.2.2.2.2

theorem b_rct : RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, Pub3 σ₁ σ₂ ∧ AfterA σ₁ s₁ ∧ AfterA σ₂ s₂) (kemMatrixWith keccak.callee)
    fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, Pub3 σ₁ σ₂ ∧ BInv enL σ₁ m₁ (rhoE σ₁) 9 s₁ ∧ BInv enL σ₂ m₂ (rhoE σ₁) 9 s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State × Mem × Mem) s₁ s₂ =>
      Pub3 x.1 x.2.1 ∧ BInv enL x.1 x.2.2.1 (rhoE x.1) 0 s₁ ∧ BInv enL x.2.1 x.2.2.2 (rhoE x.1) 0 s₂)
      fun x => ?_)
    (fun s₁ s₂ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂, s₁.mem, s₂.mem), hpub, BInv.zero a₁.kb a₁.x24 a₁.rho,
      BInv.zero a₂.kb a₂.x24 (by rw [a₂.rho, hpub.rho])⟩) fun _ _ h => h
  by_cases hpub : Pub3 x.1 x.2.1
  · exact RelCT.mono (matrix_rct hpub.two) (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hpub, h⟩
  · exact RelCT.of_false fun _ _ h => hpub h.1

theorem c_rct : RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, Pub3 σ₁ σ₂ ∧ BInv enL σ₁ m₁ (rhoE σ₁) 9 s₁ ∧
    BInv enL σ₂ m₂ (rhoE σ₁) 9 s₂) (enCWith keccak.callee) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (fun s₁ s₂ ⟨σ₁, σ₂, m₁, m₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, hpub.two.sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25]; exact hpub.2.2.1
      · rw [b₁.kb.x26, b₂.kb.x26]; exact hpub.2.2.2.2.1
      · rw [b₁.kb.x27, b₂.kb.x27]; exact hpub.2.2.2.2.2.1
      · rw [b₁.kb.x28, b₂.kb.x28]; exact hpub.2.2.2.2.2.2.1) keccak.mlkemEnCTaint.choose_spec

theorem ct : ConstantTime isa encapsAArch64.pre encapsAArch64.pub (encapsWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, e4, -, -⟩ := h
        simp [e0, e1, e2, e3, e4])) keccak.mlkemEnATaint.choose_spec).wpDep (F := fun σ s => AfterA σ s)
      fun _ _ h => ⟨a_ok (pre_of h.1), a_ok (pre_of h.2.1)⟩)
    (RelCT.seq b_rct c_rct))

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem encaps_correctWith (s : State) (hs : encapsAArch64.pre s) :
    ∃ t s', Exec isa (encapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ encapsAArch64.post s s' :=
  correct hs

theorem encaps_verifiedWith :
    Verified AArch64.target (encapsWith keccak.callee) (Spec.MlKem.encapsContract AArch64.abi 16) :=
  Verified.of_correct (encaps_correctWith (keccak := keccak)) (ct (keccak := keccak)) (by
    mlkem_implies [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, encapsAArch64,
      AArch64.abi, AArch64.argRegs] [sat] using sat)

theorem encaps_verified :
    Verified AArch64.target encaps (Spec.MlKem.encapsContract AArch64.abi 16) :=
  encaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem.AArch64.Encaps
