import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.StepsCT

/-!
# ML-DSA key generation on 32-bit ARM: the seeds leak nothing

Untrusted: everything here is checked by Lean. Two runs of the seeds in the
same layout leak the same (`seeds_two`): the bytes `k` and `ℓ` are public,
and every access is through the pointers of the layout; which gives the
piece of the seeds (`seeds_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params)

/-- Two runs whose entry states have the same layout. -/
def KTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, Two (lay p STK σ) kWb STK x y

theorem kc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : kgPub p σ₁ σ₂) (h₁ : KC p STK σ₁ x)
    (h₂ : KC p STK σ₂ y) : Two (lay p STK σ₁) kWb STK x y :=
  ⟨h₁.site, lay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem kc_two {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : kgPub p σ₁ σ₂) (h₁ : KC p STK σ₁ x)
    (h₂ : KC p STK σ₂ y) : KTwo p STK x y :=
  ⟨σ₁, kc_twoL pub h₁ h₂⟩

/-- A part that leaks the same in two runs in every layout of key generation. -/
theorem ktwo {p : Params} {STK : Nat} {c : Prog isa} (h : ∀ σ, RelCT isa (Two (lay p STK σ) kWb STK) c fun _ _ => True) :
    RelCT isa (KTwo p STK) c fun _ _ => True :=
  RelCT.exists_ h

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem ktrue : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → (fun _ => true) i = true → (fun _ => true) j = true →
    i ∈ kWb ∨ j ∈ kWb := fun i _ j _ hij _ _ _ _ => by
  simp only [kWb, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem seeds_two {p : Params} (hF : PFacts p) {STK : Nat} (σ : State) :
    RelCT isa (Two (lay p STK σ) kWb STK) (seeds p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  have hP : ∀ x y, Two (lay p STK σ) kWb STK x y → Two (lay p STK σ) kWb STK x y := fun _ _ h => h
  unfold seeds
  refine RelCT.seq (RelCT.two hP (taint7 hP (setKL_taint p.k (by omega) p.ℓ (by omega))) fun x hs => ?_) ?_
  · refine WP.block_append (WP.mono (setB_ok hs (q := sc oKL) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) p.k)
      fun s₁ ⟨k₁, _⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oKL + 1)) ⟨sc_ok _, by lsep hF⟩ (by decide)
        (by decide) p.ℓ) fun s₂ ⟨k₂, _⟩ => ⟨_, (k₁.monoL (W' := [tri (sc oKL) 1, tri (sc (oKL + 1)) 1])
          (by simp)).trans (k₂.monoL (by simp))⟩)
  have hin : ∀ s, Site (lay p STK σ) kWb STK s → ∀ pc ∈ ([⟨.r4, 0, 32⟩, ⟨.r7, oKL, 2⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc := fun s hs pc hpc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  have hq : ∀ s, Site (lay p STK σ) kWb STK s →
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.r7, oHX, 128⟩ : Impl.MlKem.Arm.Piece) := fun s hs =>
    pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size]) (.inl rfl)
      fun _ => by decide
  refine RelCT.seq (RelCT.two hP (hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide)
    (by simp) hin hq hP) fun x hs => WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by decide) (by decide) (by simp) (hin x hs) (hq x hs)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (taint7 hP (by taint_decide)) fun x hs =>
    WP.mono (copyS hs (sb := .r7) (so := oHX) (db := .r7) (dO := oSA) (len := 32) ⟨rfl, by lsep hF⟩
      ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (taint7 hP (by taint_decide)) fun x hs =>
    WP.mono (copyS hs (sb := .r7) (so := oHX + 32) (db := .r7) (dO := oSB) (len := 64) ⟨rfl, by lsep hF⟩
      ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  exact taint7 hP (by taint_decide)

theorem seeds_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (fun σ s => KC p STK σ s ∧ s.gpr .r11 = 1) (fun σ s => K1 p STK σ s ∧ s.gpr .r11 = 1) (seeds p) :=
  ⟨fun _ _ _ h => seeds_ok hF h.1 h.2,
    rel_of (ktwo fun σ => seeds_two hF σ) fun _ _ _ _ _ _ pub h₁ h₂ => kc_two pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.Arm.KeyGen
