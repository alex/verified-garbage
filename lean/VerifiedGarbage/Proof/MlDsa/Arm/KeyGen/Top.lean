import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestRow

/-!
# ML-DSA key generation on 32-bit ARM: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

Untrusted: everything here is checked by Lean. The rows (`row_piece`), the
keys in memory (`pk_bytes`, `sk_bytes`), `tr = H(pk, 64)` (`trHash_piece`),
and the whole function, piece by piece, for any parameter set of Table 1
and any verified implementations of the primitives (`keyGen_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (topEnd)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK Good)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) {i : Nat} (hi : i < p.k) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (rowMul_piece hP hF hS hi).seq (Piece.seq ?_ ((rowInv_piece hP hF hS hi).seq ((rowAdd_piece hP hF hS hi).seq
    ((rowP2r_piece hP hF hS hi).seq ((rowSbp_piece hP hF hS hi).seq (rowBp_piece hP hF hS hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => RowI p STK i (tIs p STK fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => rowMulAdd_piece hP hF hS hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 32} {np nj : Nat} {s : State} (h : KR p STK σ A S R np nj p.k s) :
    bytesAt s.mem ((lay p STK σ).A 3 0) p.pkLen = pkK p A S (rhoOf p σ) := by
  rw [hF.pk, Proof.MlKem.bytesAt_add, h.pk0, Lay.A, add_ofNat_add, Nat.zero_add,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 32} {nj : Nat} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem ((lay p STK σ).A 4 0) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 := h.sk0
  have h1 := h.sk1
  simp only [Lay.A, add_ofNat_zero] at h0 h1 htr ⊢
  have h2 : bytesAt s.mem (State.addr ((lay p STK σ).ptr 4) + BitVec.ofNat 64 (32 + 32)) 64 =
    Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 := htr
  have hp : ∀ r ∈ List.range (p.ℓ + p.k), bytesAt s.mem (State.addr ((lay p STK σ).ptr 4) +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η := fun r hr =>
    h.packs r (List.mem_range.mp hr)
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem (State.addr ((lay p STK σ).ptr 4) +
      BitVec.ofNat 64 (oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096 := fun i hi =>
    (h.rows i (List.mem_range.mp hi)).2
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (oT0 p) 416 p.k, skK, flatMap_congr_mem hp,
    flatMap_congr_mem hr]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A S R, KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trPieces {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (hs : Site (lay p STK σ) kWb STK s) :
    (∀ pc ∈ ([⟨.r5, 0, p.pkLen⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc) ∧
    PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.r6, 64, 64⟩ : Impl.MlKem.Arm.Piece) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hpk := hF.lens
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hashLay, Lay.size, hF.sk, hlen, ite_true]) (.inr rfl)
    fun _ => by decide⟩
  rw [List.mem_singleton] at hpc; subst hpc
  exact pieceS hs rfl (show encodable (BitVec.ofNat 32 0) = true by decide) hF.encPk
    (show 0 < p.pkLen by rw [hF.pk]; omega) (show 0 + p.pkLen < 2 ^ 32 by omega)
    (by lsep hF [hashLay, Lay.size, hF.pk, ite_true]) (.inr rfl) fun h => absurd h (by decide)

theorem trHash_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 32} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s) :
    WP isa (trHash p) s (KFin p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  obtain ⟨hin, hq⟩ := trPieces hF hs
  unfold trHash
  refine WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
    (by simp) hin hq) fun s' ⟨k', o'⟩ => ⟨A, S, R, h.keep hF k' (by krchk hF), ?_⟩
  have o₃ : bytesAt s'.mem ((lay p STK σ).A 4 64) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e : bytesAt s.mem (State.addr ((lay p STK σ).ptr (ix Reg.r5)) + 0#64) p.pkLen = pkK p A S (rhoOf p σ) :=
    pk_bytes hF h
  rw [e, shake31]
  exact (Proof.MlKem.shake256_eq _ _).symm

theorem trHash_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ p.k) (KFin p STK) (trHash p) :=
  ⟨fun _ _ _ ⟨_, _, _, h⟩ => trHash_ok hF h,
    rel_of (ktwo fun σ => hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by simp)
      (fun s hs => (trPieces hF hs).1) (fun s hs => (trPieces hF hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (h : KFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      Arm.target.abiPreserved σ s' ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s' := by
  obtain ⟨A, S, R, h, htr⟩ := h
  have hs := h.kc.site
  have e0 : ∀ o, (hashLay (lay p STK σ) s fun _ => true).A 0 o = (lay p STK σ).A 0 o := fun o => by
    simp only [Lay.A, hashLay_ptr _ _ _ (show (0 : Nat) ≠ 1 by decide)]
  refine WP.mono (topEnd_ok (hs.ctx ktrue) (by rw [e0]; exact h.kc.sav) (by rw [e0]; exact h.kc.lr))
    fun s' ⟨pr, r0, m', sp'⟩ => ⟨⟨pr, sp'.trans h.kc.sp⟩, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  have e3 : BitVec.setWidth 64 (σ.gpr .r1) = (lay p STK σ).A 3 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  have e4 : BitVec.setWidth 64 (σ.gpr .r2) = (lay p STK σ).A 4 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  rw [setWidth_append32, r0, h.r11, m', e3, e4, pk_bytes hF h, sk_bytes hF h htr]
  exact Proof.MlDsa.KeyGen.outcome_keyGen (by have := hF.l; omega) h.good

theorem ktaint7 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) : RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint7 (fun _ _ h => h) h

theorem epi_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KFin p STK)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok hF h, rel_of (ktaint7 (by taint_decide))
    fun _ _ _ _ _ _ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The function -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem rest_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p STK) (rest P p) := by
  unfold rest
  refine (copies_piece hF).seq (Piece.seq (J := KRx p STK (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ p.k) ?_
      (trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p STK r 0 0) (p.ℓ + p.k) 0
      fun r _ hr => packS_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p STK (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => nttS_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p STK (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => row_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece :
    KPiece p STK (fun σ s => s = σ)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s)
      (keyGen P p) :=
  (pro_piece hF (by omega)).seq ((seeds_piece hF).seq ((sampA_piece hP hF hS).seq ((sampS_piece hP hF hS).seq
    ((rest_piece hP hF hS).seq (epi_piece hF)))))

end

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | .r3 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, scrLen p⟩]

end VG.Proof.MlDsa.Arm.KeyGen

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen (Prims keyGen)

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract with
36 bytes of stack, for any verified implementations `P` of the primitives
it calls with at most 28 bytes of stack. -/
theorem keyGen_verified {P : Prims} (hP : PrimsOk P 28) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified Arm.target (keyGen P p) (Spec.MlDsa.keyGenContract p Arm.abi 36) := by
  have hF := pfacts hp
  have hk := keyGen_piece hP hF (Nat.le_refl _)
  refine ⟨fun s hs => hk.ok s s (pre_of (n := 35) hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of (n := 35) h₁) (pre_of (n := 35) h₂)
      ⟨hsp, h0, h1, h2, h3, hl⟩ e₁ e₂
  · refine ⟨keyGenSat p, ?_⟩
    rcases hp with rfl | rfl | rfl <;>
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, keyGenSat]

end VG.Proof.MlDsa.Arm.KeyGen
