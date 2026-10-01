import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow

/-!
# ML-DSA key generation on AArch64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

Untrusted: everything here is checked by Lean. The function, piece by piece,
for any parameter set of Table 1 and any verified implementations of the
primitives (`keyGen_piece`): it returns 1 with `KeyGen_internal(ξ)` in `pk`
and `sk` if every sampler succeeded (for some bounds), and 0 if key
generation fails within the least bounds; it leaks only the pointers, `ρ`
and what `RejBoundedPoly` leaks; so it meets the shared contract
(`keyGen_verified`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {i : Nat}
    (hi : i < p.k) : Piece p S' (KRx p (p.ℓ + p.k) p.ℓ i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (mul_piece hP hF hi).seq (Piece.seq ?_ ((inv_piece hP hF hi).seq ((addS2_piece hP hF hi).seq
    ((p2r_piece hP hF hi).seq ((sbp_piece hP hF hi).seq (bp_piece hP hF hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => RowI p i (tIs p fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => mulAdd_piece hP hF hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pa_zero (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

theorem pk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : KR p σ A S R np nj p.k s) :
    bytesAt s.mem (pa s (.x26, 0)) p.pkLen = pkK p A S (rhoOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x26) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.pk0
  rw [hF.pk, pa_zero, Proof.MlKem.bytesAt_add, h0,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x26) 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : KR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem (pa s (.x27, 0)) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x27) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 32) 32 = kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 :=
    htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, pa_zero, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (oT0 p) 416 p.k, skK]
  rw [flatMap_congr_mem (g := fun r => bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    flatMap_congr_mem (g := fun i => bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trHash_chk {p : Params} (hF : PFacts p) :
    hashChk kgR (kgW p) [⟨.x26, 0, p.pkLen⟩] ⟨.x27, 64, 64⟩ = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> (unfold hashChk pieceChk; lay [hF.pk, hF.sk, hlen])

theorem trHash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P ((trHashWith keccak.callee) p) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaTrHashTaint p hp
  exact VectorTaint.relRegs bases hr hh

theorem trHash_piece {p : Params} (hF : PFacts p) {S' : Nat} (h16 : 16 ≤ S') (hSl : S' < 2 ^ 64) :
    Piece p S' (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) ((trHashWith keccak.callee) p) := by
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, rel_of (Q := Two p S') (trHash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHashWith
  refine WP.mono (shake_ok h16 hSl L (by simp) (trHash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨A, S, R, ?_, ?_⟩
  · exact h.keep hF hp hP' x' (by krchk hF)
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x27 ∈ bases by decide), ho]
    exact congrArg (Spec.MlDsa.H · 64) (pk_bytes hF h)

/-! ## The return -/

theorem outcome_of {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    (hl : 0 < p.ℓ) (hG : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf σ)) (R.setWidth 32)
      (pkK p A S (rhoOf p σ), skK p A S (rhoOf p σ) (kOf p σ)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (xiOf σ) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem epi_piece {p : Params} (hF : PFacts p) {S' : Nat} :
    Piece p S' (KFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s)
      (.block epi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, rel_of (Q := Two p S') (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := scr_ge hF; lay)
    rwa [pa, h.kc.top.x28] at this
  refine WP.mono (epi_ok h.kc.top hin) fun s' ⟨ha, hr, hm⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  have e26 : pa s (.x26, 0) = σ.gpr .x1 := by rw [pa_zero, h.kc.top.x26]
  have e27 : pa s (.x27, 0) = σ.gpr .x2 := by rw [pa_zero, h.kc.top.x27]
  rw [hr, h.x24, hm, ← e26, ← e27, pk_bytes hF h, sk_bytes hF h htr]
  exact outcome_of (by have := hF.l; omega) h.good

/-! ## The function -/

theorem rest_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) :
    Piece p S' (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p) ((restWith keccak.callee) P p) := by
  unfold restWith
  refine (copies_piece hF).seq (Piece.seq (J := KRx p (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := KRx p (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := KRx p (p.ℓ + p.k) p.ℓ p.k) ?_
      (trHash_piece hF hP.s16 hP.s64))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p r 0 0) (p.ℓ + p.k) 0 fun r _ hr => packS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => nttS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => row_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) :
    Piece p S' (fun σ s => s = σ)
      (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s) ((keyGenWith keccak.callee) P p) :=
  (pro_piece hF).seq ((seeds_piece hF hP.s16 hP.s64).seq ((sampA_piece hP hF).seq ((sampS_piece hP hF).seq
    ((rest_piece hP hF).seq (epi_piece hF)))))

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls that use at most `S`
bytes of stack, if the contract is satisfiable. -/
theorem keyGen_verified {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : ∃ s, (Spec.MlDsa.keyGenContract p AArch64.abi S).pre s) :
    Verified AArch64.target ((keyGenWith keccak.callee) P p) (Spec.MlDsa.keyGenContract p AArch64.abi S) :=
  ⟨fun σ hσ => (keyGen_piece hP (pfacts hp)).ok σ σ hσ rfl,
    relStart (Q := fun _ _ => True) (keyGen_piece hP (pfacts hp)).tr, hsat⟩

end VG.Proof.MlDsa.AArch64.KeyGen
