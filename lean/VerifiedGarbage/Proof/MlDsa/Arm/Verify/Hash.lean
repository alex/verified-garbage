import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row

/-!
# ML-DSA verification on 32-bit ARM: `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)`

Once every row of `w′₁` is packed to `B`, the commitment hash of `μ` and `B`,
to `CT` (`vhash_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv hashLay hashLay_ptr
  hashS hashS_tr pieceS ix_ne1 shake31)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlKem.Arm (hash)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt Reduced ntt simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

/-- The buffers of the sponge: `mu` and `scratch`. -/
abbrev Kmu : Nat → Bool := fun i => i == 3

theorem kmu : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → Kmu i = true → Kmu j = true → i ∈ vWb ∨ j ∈ vWb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [Kmu, beq_iff_eq] at hi hj; omega

/-- `w1Encode(w′₁)` of rows `A'`, `cc` and `h`. -/
abbrev w1Enc (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) : List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- After the hash. -/
abbrev KF (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R p.ℓ true p.k s ∧
    bytesAt s.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen

theorem vhPieces {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (hs : Site (vlay p STK σ) vWb STK s) :
    (∀ pc ∈ ([⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (vlay p STK σ) s Kmu) ix s false pc) ∧
    PieceOk (hashLay (vlay p STK σ) s Kmu) ix s true (⟨.r7, oCT, p.ctildeLen⟩ : Impl.MlKem.Arm.Piece) := by
  have hk := hF.k
  obtain ⟨w1a, w1b, w1c⟩ := hF.w1
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show encodable (BitVec.ofNat 32 oCT) = true by decide)
    (show encodable (BitVec.ofNat 32 p.ctildeLen) = true by rcases hF.ct with e | e | e <;> rw [e] <;> decide)
    (show 0 < p.ctildeLen by rcases hF.ct with e | e | e <;> omega)
    (show oCT + p.ctildeLen < 2 ^ 32 by simp only [oCT]; rcases hF.ct with e | e | e <;> omega)
    (by rcases hF.ct with e | e | e <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl)
    fun _ => show ix Reg.r7 ∈ vWb by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show encodable (BitVec.ofNat 32 0) = true by decide)
      (show encodable (BitVec.ofNat 32 64) = true by decide) (by decide) (by decide)
      (by vsep hF [hashLay, Lay.size]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show encodable (BitVec.ofNat 32 oB) = true by decide) w1c w1b (by simp only [oB]; omega)
      (by rcases hF.w1l with e | ⟨e, _⟩ <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl) fun h => absurd h (by decide)

theorem B_bytes {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc} {s : State}
    (hk5 : KC5 p STK σ A' cc h R nz nc p.k s) :
    bytesAt s.mem ((vlay p STK σ).A 0 oB) (p.k * w1Len p) = w1Enc p σ A' cc h := by
  rw [Nat.mul_comm, Lay.A, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ oB (w1Len p) p.k]
  exact flatMap_congr_mem' fun r hr => hk5.rows r (List.mem_range.mp hr)

theorem vhash_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R p.ℓ true p.k s) :
    WP isa (hash 136 0x1f [⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] [⟨.r7, oCT, p.ctildeLen⟩]) s (KF p STK σ) := by
  have hk := hF.k
  have hs := hk5.vc.site
  obtain ⟨hin, hq⟩ := vhPieces hF hs
  refine WP.mono (hashS hs kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
    (by simp) hin hq) fun s' ⟨k', o'⟩ => ⟨A', cc, h, R, hk5.keep hF k' ?_, ?_⟩
  · rcases hF.ct with e | e | e <;> k5chk hF
  · have o₃ : bytesAt s'.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s.mem (State.addr ((vlay p STK σ).ptr (ix Reg.r5)) + BitVec.ofNat 64 0) 64 = muOf σ :=
      hk5.vc.mu
    have e2 : bytesAt s.mem (State.addr ((vlay p STK σ).ptr (ix Reg.r7)) + BitVec.ofNat 64 oB) (p.k * w1Len p) =
        w1Enc p σ A' cc h := B_bytes hk5
    rw [e1, e2, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem vhash_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KX p STK p.ℓ true p.k) (KF p STK)
      (hash 136 0x1f [⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] [⟨.r7, oCT, p.ctildeLen⟩]) :=
  ⟨fun _ _ _ ⟨_, _, _, _, h⟩ => vhash_ok hF h,
    rel_of (RelCT.exists_ fun σ => hashS_tr kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide)
      (by simp) (fun s hs => (vhPieces hF (σ := σ) hs).1) (fun s hs => (vhPieces hF hs).2) fun _ _ h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.Arm.Verify
