import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestRow

/-!
# ML-DSA key generation on x86-64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

Untrusted: everything here is checked by Lean. The function, piece by piece,
for any parameter set of Table 1 and any verified implementations of the
primitives (`keyGen_piece`): it returns 1 with `KeyGen_internal(ξ)` in `pk`
and `sk` if every sampler succeeded (for some bounds), and 0 if key
generation fails within the least bounds; it leaks only the pointers, `ρ`
and what `RejBoundedPoly` leaks; so it meets the shared contract
(`keyGen_verified`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR topEpi oSV)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    Piece p (KRx p (p.ℓ + p.k) p.ℓ i) (KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
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

theorem pk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : KR p σ A S R np nj p.k s) :
    bytesAt s.mem (pa s (.r12, 0)) p.pkLen = pkK p A S (rhoOf p σ) := by
  rw [hF.pk, Proof.MlKem.bytesAt_add, h.pk0, show pa s (.r12, 0) = s.gpr .r12 + BitVec.ofNat 64 0 from rfl,
    add_ofNat_zero, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .r12) 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : KR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (pa s (.r13, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem (pa s (.r13, 0)) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have e0 : pa s (.r13, 0) = s.gpr .r13 := by rw [pa, add_ofNat_zero]
  have h0 : bytesAt s.mem (s.gpr .r13) 32 = rhoOf p σ := by rw [← e0]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .r13 + BitVec.ofNat 64 32) 32 = kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .r13 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 := htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, e0, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .r13) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .r13) (oT0 p) 416 p.k, skK]
  rw [flatMap_congr_mem (g := fun r => bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    flatMap_congr_mem (g := fun i => bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (pa s (.r13, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trHash_piece {p : Params} (hF : PFacts p) : Piece p (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) (trHash p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hc : hashChk (kgB p) (kgW p) [((.r12, 0), p.pkLen)] 136 (.r13, 64) 64 = true := by
    rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> layk [hF.pk, hF.sk, hlen]
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, rel_of (Q := Two p) (RelCT.mono (hash_tr (kgB_bases p) hc (by decide))
    (fun _ _ h => h.lrel) fun _ _ h => h) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHash
  refine WP.mono (hash_okM hc (by decide) L) fun s' ⟨⟨hP', ho⟩, hx⟩ => ⟨A, S, R, ?_, ?_⟩
  · exact h.keep hF hp hP'.b hx (hP'.cs .r15 (by decide)) (by krchk hF)
  · simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, pk_bytes hF h] at ho
    rw [hP'.pa (show Reg.r13 ∈ calleeSaved by decide), ho, shake31', ← Proof.MlKem.shake256_eq]
    rfl

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

theorem epi_piece {p : Params} (hF : PFacts p) :
    Piece p (KFin p) (fun σ s => abiPreserved σ s ∧ (kgK p).post σ s) (.block topEpi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, rel_of (Q := Two p) (taintRel [.rbx] (fun x y h => two_rbx h)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
    L.cR (p := sc (oSV + 8 * k)) (l := 8) (by lay) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (WP.mx (noLd_spec (by rfl)) (topEpi_ok h.kc.top hin)) fun s' ⟨⟨hr, hg, hm⟩, hx⟩ =>
    ⟨⟨hg.1, hg.2, by rw [← MX, ← MX, hx, h.kc.mx]⟩, ?_⟩
  have e12 : pa s (.r12, 0) = σ.gpr .rsi := by rw [pa, h.kc.top.regs (.r12, .rsi) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rdx := by rw [pa, h.kc.top.regs (.r13, .rdx) (by decide), add_ofNat_zero]
  show Spec.MlDsa.Outcome _ _ _
  rw [hr, h.r15, hm, ← e12, ← e13, pk_bytes hF h, sk_bytes hF h htr]
  exact outcome_of (by have := hF.l; omega) h.good

/-! ## The function -/

theorem rest_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p) (rest P p) := by
  unfold rest
  refine (copies_piece hF).seq (Piece.seq (J := KRx p (p.ℓ + p.k) 0 0) ?_ (Piece.seq (J := KRx p (p.ℓ + p.k) p.ℓ 0) ?_
    (Piece.seq (J := KRx p (p.ℓ + p.k) p.ℓ p.k) ?_ (trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p r 0 0) (p.ℓ + p.k) 0 fun r _ hr => packS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p (p.ℓ + p.k) j 0) p.ℓ 0 fun j _ hj => nttS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p (p.ℓ + p.k) p.ℓ i) p.k 0 fun i _ hi => row_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) :
    Piece p (fun σ s => s = σ) (fun σ s => abiPreserved σ s ∧ (kgK p).post σ s) (keyGen P p) :=
  (pro_piece hF).seq ((seeds_piece hF).seq ((sampA_piece hP hF).seq ((sampS_piece hP hF).seq
    ((rest_piece hP hF).seq (epi_piece hF)))))

theorem keyGen_correct {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) (σ : State) (hp : (kgK p).pre σ) :
    ∃ t s', Exec isa (keyGen P p) σ t s' ∧ abiPreserved σ s' ∧ (kgK p).post σ s' :=
  (keyGen_piece hP hF).ok σ σ hp rfl

theorem keyGen_ct {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) :
    ConstantTime isa (kgK p).pre (kgK p).pub (keyGen P p) :=
  relStart (Q := fun _ _ => True) (keyGen_piece hP hF).tr

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, scrLen p⟩]

theorem keyGen_implies (p : Params) (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    (kgK p).Implies (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  { pre := by sig_implies_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK, X86_64.abi, VG.X86_64.argRegs]
    post := by sig_implies_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK, X86_64.abi, VG.X86_64.argRegs]
    pub := by
      intro s₁ s₂ _ _ h
      sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK, X86_64.abi, VG.X86_64.argRegs] at h
      obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
      exact ⟨hdi, hsi, hdx, hcx, hsp, hb⟩
    sat := by
      rcases hp with rfl | rfl | rfl
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using keyGenSat Spec.MlDsa.mlDsa44
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using keyGenSat Spec.MlDsa.mlDsa65
      · sig_implies_sat [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, kgK, X86_64.abi, VG.X86_64.argRegs]
          [keyGenSat] using keyGenSat Spec.MlDsa.mlDsa87 }

end VG.Proof.MlDsa.X86_64.KeyGen

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen (Prims keyGen)

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls. -/
theorem keyGen_verified {P : Prims} (hP : PrimsOk P) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified X86_64.target (keyGen P p) (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  Verified.of_correct (keyGen_correct hP (pfacts hp)) (keyGen_ct hP (pfacts hp)) (keyGen_implies p hp)

end VG.Proof.MlDsa.X86_64.KeyGen
