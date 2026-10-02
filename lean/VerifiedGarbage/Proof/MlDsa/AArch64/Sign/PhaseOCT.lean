import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT

/-!
# ML-DSA signing on AArch64: the signature leaks only the hint

Writing the signature leaks its pointers and the hint (`output_tr`), on which
two runs whose loops leaked the same agree (`OX`); so all but `Â` leaks what
`signLeakT` says (`rest_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem hint_coeffs {x y : State} {k : Nat} {f : Nat → Vector Bool n} (hx : HFam x 5 k f) (hy : HFam y 5 k f) :
    (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x (Impl.MlDsa.AArch64.Sign.hP 0)) i).toNat) =
      (List.range (256 * k)).map (fun i => (coeffAt y.mem (pa y (Impl.MlDsa.AArch64.Sign.hP 0)) i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ s : State, coeffAt s.mem (pa s (Impl.MlDsa.AArch64.Sign.hP 0)) i =
      coeffAt s.mem (pa s (pS (5 + i / 256))) (i % 256) := fun s => by
    rw [pS_hint s (i / 256)]
    simp only [coeffAt]
    rw [BitVec.add_assoc (pa s (Impl.MlDsa.AArch64.Sign.hP 0)) (BitVec.ofNat 64 (1024 * (i / 256))), ← BitVec.ofNat_add,
      show 1024 * (i / 256) + 4 * (i % 256) = 4 * i by omega]
  have hq : i / 256 < k := by omega
  have hj : i % 256 < n := Nat.mod_lt _ (by decide)
  have ex := (hx _ hq).2 0 (by decide) _ hj
  have ey := (hy _ hq).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [e x, e y, ex, ey]

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, IK p D σ s ∧ bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ ∧ Fam s (yBase p) p.ℓ (Zv p σ κ) ∧
    HFam s 5 p.k (Hv p σ κ) ∧ PassV p σ κ ∧ s.gpr .x24 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, OS p D σ κ r s ∧ PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (pa s (yP p r)) ∧ InRange s.mem (pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : PrimsOk P D) (hc : oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => RS p D E (IOi p D) x y ∧ HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  unfold output
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D 0) x y ∧ HJ p x y) (liftQ
    (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (copy_tr (.inr rfl) rfl fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk.d.im.st)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D p.ℓ) x y ∧ HJ p x y) (RelCT.mono (seqR_tr
    (R := fun r x y => RS p D E (IOr p D r) x y ∧ HJ p x y) p.ℓ 0 fun r _ hr => liftQ
      (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (packZ_ok hP hc (by omega) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (bpAt_tr hP hbp hzl (cz r (by omega)).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega), i₂.zr (by omega)⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨hones_ok o₁ a₁, hones_ok o₂ a₂, hint_coeffs hx hy⟩

theorem XS.io {σ x : State} (h : XS p D σ x) (h15 : x.gpr .x24 = 1) : IOi p D σ x := by
  obtain ⟨t, _, _, _, hpass, hct, hz, hh⟩ := h.pass h15
  exact ⟨p.ℓ * t, h.k, hct, hz, hh, hpass, h15⟩

theorem rest_tr {P : Prims} (hP : PrimsOk P D) (h3 : Ok3 p) :
    RelCT isa (RS p D (LeakEq p 0) (IM p D)) (restWith keccak.callee P p) (RS p D (LeakEq p 0) (FS p D)) := by
  refine liftR (fun σ s _ h => rest_ok hP h3 h) ?_
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, -⟩ := hc
  unfold restWith
  refine RelCT.seq (decode_tr hP hd) (RelCT.seq (signLoop_tr hP h3 hc1 hb hks hl) ?_)
  unfold ifOk
  refine ifOkElse_tr (fun x y h => by rw [h.2.1]) (RelCT.mono (output_tr hP ho (E := fun _ _ => True))
    (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, _, s₁, s₂⟩, h15, hj⟩, hne⟩ => ?_)
    fun _ _ h => h) (RelCT.mono nil_tr (fun _ _ h => h) fun _ _ _ => trivial)
  have e₁ := x24_one s₁.r01 hne
  have e₂ : y.gpr .x24 = 1 := h15 ▸ e₁
  obtain ⟨_, f, hx, hy⟩ := hj e₁
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, s₁.io e₁, s₂.io e₂⟩, f, hx, hy⟩

end

end VG.Proof.MlDsa.AArch64.Sign
