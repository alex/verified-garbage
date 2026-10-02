import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay

/-!
# ML-DSA verification on AArch64: the prologue, the hint and `z`

The prologue (`pro_vpiece`); the hint of the signature, with `x24` whether it
is well formed (`hint_vpiece`); then, if it is, `z[i]` (polynomial `k + i`
after `Â`) and `x24` whether each norm so far is small (`zOne_vpiece`). The
results in `x24` are functions of the signature, so they are the same in two
runs.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq polyAt coeffAt Reduced PolyIs HintIs normRq hintBitUnpack bitUnpack)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

/-! ## The inputs -/

/-- `h`, `z[i]`, and whether the norms of `z[0], …, z[j - 1]` are small, of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (vSig p σ)
abbrev zOf (p : Params) (σ : State) (i : Nat) : IPoly := Proof.MlDsa.Verify.vZ p (vSig p σ) i
abbrev normOk (p : Params) (σ : State) (j : Nat) : Prop := ∀ i < j, normRq [toRq (zOf p σ i)] < p.γ₁ - p.β

/-- The result in `x24`. -/
abbrev flag (P : Prop) [Decidable P] : BitVec 64 := if P then 1 else 0

theorem flag_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : flag P = flag Q := by
  by_cases hp : P
  · simp only [flag, hp, h.mp hp, ↓reduceIte]
  · simp only [flag, hp, mt h.mpr hp, ↓reduceIte]

/-- `and24` of a flag and a callee's result. -/
theorem and_flag {P Q : Prop} [Decidable P] [Decidable Q] (r : BitVec 64)
    (hr : r.setWidth 32 = if Q then 1 else 0) :
    ((flag P).setWidth 32 &&& r.setWidth 32).setWidth 64 = flag (P ∧ Q) := by
  rw [hr]
  by_cases hp : P <;> by_cases hq : Q <;> simp only [flag, hp, hq, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

theorem vpa0 (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

theorem VC.slice {p : Params} {σ s : State} (h : VC p σ s) {o len : Nat} (hl : o + len ≤ p.sigLen) :
    bytesAt s.mem (pa s (.x27, o)) len = ((vSig p σ).drop o).take len := by
  rw [← h.sig, vpa0, Proof.MlKem.bytesAt_slice _ _ hl]

theorem VC.pkSlice {p : Params} {σ s : State} (h : VC p σ s) {o len : Nat} (hl : o + len ≤ p.pkLen) :
    bytesAt s.mem (pa s (.x25, o)) len = ((vPk p σ).drop o).take len := by
  rw [← h.pk, vpa0, Proof.MlKem.bytesAt_slice _ _ hl]

theorem sc_ge {p : Params} (hF : VFacts p) : 4096 + 1024 * (p.k * p.ℓ + p.k + p.ℓ + 6) ≤ scrLen p := by
  rw [scr_eq]; have := hF.k; have := hF.l; omega

/-- The block `and24`: only `x24`, and memory kept. -/
theorem and24_post {S : Nat} (s : State) :
    WP isa (.block and24) s fun s' => PPostB S s s' [] ∧ (∀ r, r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧ s'.mem = s.mem :=
  WP.mono (and24_ok s) fun _ ⟨o, e⟩ => ⟨postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _),
    fun r hr => o.get r (by simpa using hr), e, o.mem⟩

theorem and24_nomem : ∀ i ∈ and24, ∀ s, isa.addrs i s = [] := fun i hi _ => by
  simp only [and24, List.mem_singleton] at hi; subst hi; rfl

/-! ## The prologue -/

theorem pro_vpiece {p : Params} (hF : VFacts p) {S : Nat} :
    VPiece p S (fun σ s => s = σ) (fun σ s => VC p σ s ∧ s.gpr .x24 = 1) (.block pro) := by
  refine ⟨fun σ s hp hs => ?_, taintRel [.x0, .x1, .x2, .x3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · subst hs
    have hp' := hp
    unfold vPre at hp'
    sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at hp'
    obtain ⟨_, _, hwr, d03, d13, d23, _, _, _, _, _⟩ := hp'
    have hsc : 4096 + 1024 * (p.k * p.ℓ + p.k + p.ℓ + 6) ≤ Spec.MlDsa.scratchWords p * 8 := sc_ge hF
    have hsm := hF.small
    have hsv : SV + 48 ≤ Spec.MlDsa.scratchWords p * 8 := Nat.le_trans (by decide) (Nat.le_trans (Nat.le_add_right 4096 _) hsc)
    have hin : ∀ k < 6, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk =>
      ⟨⟨s.gpr .x3, Spec.MlDsa.scratchWords p * 8⟩, by rw [hwr]; simp,
        Offset.contains_base _ (by simp only [SV]; omega) (by simp only [SV]; omega)⟩
    refine WP.mono (pro_ok hin) fun s' ⟨ht, h24, hf⟩ => ⟨⟨ht, ?_, ?_, ?_⟩, h24⟩
    · rw [vpa0, ht.x25]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d03.sub_right (Offset.sub_base _ hsv)) (Nat.le_of_lt (Nat.lt_trans hsm.2.1 (by decide)))
    · rw [vpa0, ht.x26]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d13.sub_right (Offset.sub_base _ hsv)) (by decide)
    · rw [vpa0, ht.x27]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d23.sub_right (Offset.sub_base _ hsv)) (Nat.le_of_lt (Nat.lt_trans hsm.2.2 (by decide)))
  · subst h₁ h₂
    obtain ⟨esp, _, _, _, e0, e1, e2, e3⟩ := vPub_eq pub
    refine ⟨esp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-! ## The hint -/

/-- After the hint: `x24` whether it is well formed, and the hint. -/
def V1 (p : Params) (σ s : State) : Prop :=
  VC p σ s ∧ s.gpr .x24 = flag ((hintOf p σ).isSome = true) ∧
    ∀ h, hintOf p σ = some h → HintIs s.mem (pa s (hP p 0)) p.k h

theorem hint_chk {p : Params} (hF : VFacts p) :
    rwChk (vR p) (vW p) (.x27, oHint p) (p.ω + p.k) (hP p 0) (256 * p.k * 4) = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.sig; have := hF.small
  unfold rwChk; vlay

theorem hint_eq (p : Params) (σ : State) :
    hintOf p σ = hintBitUnpack p.ω p.k (((vSig p σ).drop (oHint p)).take (p.ω + p.k)) := rfl

theorem hint_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s => VC p σ s ∧ s.gpr .x24 = 1) (V1 p) (hint P p) := by
  have hc := hint_chk hF
  refine ⟨fun σ s hp h => ?_, ?_⟩
  · have L := h.1.lay hF hp
    unfold hint
    refine WP.seq (WP.mono (huAt_ok hP.s64 hP.hintUnpack L hc hF.hu) fun s₁ ⟨hP₁, x₁, hq⟩ => ?_)
    have h₁ := h.1.step hF hp hP₁ (by
      have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.small
      unfold vcChk; vlay)
    refine WP.mono (and24_post (S := S) s₁) fun s₂ ⟨hP₂, g₂, x₂, hm⟩ => ?_
    have h₂ := h₁.step hF hp hP₂ (by
      have := hF.k; have := hF.l; have := scr_eq p; have := hF.small
      unfold vcChk; vlay)
    rw [h.1.slice (by rw [hF.sig, oHint]; omega), show p.ω + p.k - p.ω = p.k by omega, ← hint_eq] at hq
    refine ⟨h₂, ?_, fun hh e => ?_⟩
    · rw [x₂, x₁, h.2]
      revert hq; cases hintOf p σ with
      | some hh => intro ⟨hr, _⟩; rw [hr]; rfl
      | none => intro hr; rw [hr]; rfl
    · rw [e] at hq
      rw [hP₂.pa (show Reg.x28 ∈ bases by decide), hm, hP₁.pa (show Reg.x28 ∈ bases by decide)]
      exact hq.2
  · refine vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (.x27, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (pa y (.x27, oHint p)) (p.ω + p.k)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
        ⟨vc_two hF p₁ p₂ pub h₁.1 h₂.1, by
          have hl : oHint p + (p.ω + p.k) ≤ p.sigLen := by rw [hF.sig, oHint]; omega
          rw [h₁.1.slice hl, h₂.1.slice hl, (vPub_eq pub).2.2.2.1]⟩
    unfold hint
    exact RelCT.seq (huAt_tr hP.hintUnpack (vOk p) hc hF.hu fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      (block_nomem_tr and24_nomem)

/-! ## `z` -/

/-- After `z[0], …, z[j - 1]`, with the hint well formed. -/
structure VZ (p : Params) (σ : State) (j : Nat) (s : State) : Prop where
  vc : VC p σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem (pa s (hP p 0)) p.k h
  z : ∀ i < j, PolyIs s.mem (pa s (zP p i)) (toRq (zOf p σ i))

/-- A piece that writes `ws` keeps `VZ`. -/
structure VZChk (p : Params) (j : Nat) (ws : List (Ptr × Nat)) : Prop where
  vc : vcChk p ws = true
  hint : keepB (vR p) (vW p) ws (hP p 0) (1024 * p.k) = true
  z : ∀ i < j, keepB (vR p) (vW p) ws (zP p i) 1024 = true

theorem VZ.keep {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ) {j : Nat} {s s' : State}
    (h : VZ p σ j s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VZChk p j ws) : VZ p σ j s' := by
  have L := h.vc.lay hF hp
  obtain ⟨hh, e, hH⟩ := h.hint
  exact ⟨h.vc.step hF hp hP hc.vc, ⟨hh, e, L.keepHint hP hc.hint hH⟩,
    fun i hi => L.keepPoly hP (hc.z i hi) (h.z i hi)⟩

theorem VFacts.scr {p : Params} (_ : VFacts p) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) :=
  scr_eq p

/-- Proves a `VZChk`. -/
syntax "vzchk " term:max : tactic
macro_rules
  | `(tactic| vzchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> vlay))

theorem zl_le {p : Params} {j : Nat} (hj : j < p.ℓ) : lenZ p * j + lenZ p ≤ lenZ p * p.ℓ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj

/-- `x24` whether the norms so far are small, and then `z[j]`, and whether its norm is. -/
abbrev Z0 (p : Params) (j : Nat) (σ s : State) : Prop := VZ p σ j s ∧ s.gpr .x24 = flag (normOk p σ j)
abbrev Z1 (p : Params) (j : Nat) (σ s : State) : Prop :=
  Z0 p j σ s ∧ PolyIs s.mem (pa s (zP p j)) (toRq (zOf p σ j))
abbrev Z2 (p : Params) (j : Nat) (σ s : State) : Prop :=
  Z1 p j σ s ∧ (s.gpr .x0).setWidth 32 = if normRq [toRq (zOf p σ j)] < p.γ₁ - p.β then 1 else 0

theorem zOf_eq (p : Params) (σ : State) (j : Nat) :
    zOf p σ j = bitUnpack (((vSig p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p)) (p.γ₁ - 1) p.γ₁ := rfl

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) {j : Nat} (hj : j < p.ℓ)
include hP hF hj

omit hP in
theorem bu_chk : rwChk (vR p) (vW p) (.x27, p.ctildeLen + lenZ p * j) (lenZ p) (zP p j) 1024 = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.sig; have := hF.small
  have := zl_le hj
  unfold rwChk; vlay

theorem bu_vpiece : VPiece p S (Z0 p j) (Z1 p j)
    (bitUnpackAt P (.x27, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (zP p j)) := by
  have hc := bu_chk hF hj
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := VTwo p S) (buAt_tr hP.bitUnpack (vOk p) hc hF.bp
    fun x y h => ⟨h.lx, h.ly, h.same⟩) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => vc_two hF p₁ p₂ pub h₁.1.vc h₂.1.vc⟩
  have L := h.1.vc.lay hF hp
  refine WP.mono (buAt_ok hP.s64 hP.bitUnpack L hc hF.bp) fun s' ⟨hP', x', hq⟩ => ?_
  have := zl_le hj
  refine ⟨⟨h.1.keep hF hp hP' (by vzchk hF), by rw [x', h.2]⟩, ?_⟩
  rw [h.1.vc.slice (by rw [hF.sig]; omega), ← zOf_eq] at hq
  rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
  exact hq

theorem norm_vpiece : VPiece p S (Z1 p j) (Z2 p j) (normLtAt P (zP p j) (p.γ₁ - p.β)) := by
  have hc : inB (vR p ++ vW p) (zP p j) 1024 = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlay
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧ Reduced x.mem (pa x (zP p j)) ∧
    Reduced y.mem (pa y (zP p j))) (normAt_tr hP.normLt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2,
      h.1.same⟩) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨vc_two hF p₁ p₂ pub h₁.1.1.vc h₂.1.1.vc, h₁.2.1, h₂.2.1⟩⟩
  have L := h.1.1.vc.lay hF hp
  refine WP.mono (normAt_ok hP.s64 hP.normLt L hc hF.g1.2.2 h.2.1) fun s' ⟨hP', x', hq⟩ => ?_
  have hz := L.keepPoly hP' (by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlay) h.2
  refine ⟨⟨⟨h.1.1.keep hF hp hP' (by vzchk hF), by rw [x', h.1.2]⟩, hz⟩, ?_⟩
  rw [hq, h.2.2]

omit hP in
theorem and_vpiece : VPiece p S (Z2 p j) (Z0 p (j + 1)) (.block and24) := by
  refine ⟨fun σ s hp h => ?_, block_nomem_tr and24_nomem⟩
  refine WP.mono (and24_post (S := S) s) fun s' ⟨hP', _, x', _⟩ => ?_
  have L := h.1.1.1.vc.lay hF hp
  have hz := L.keepPoly hP' (by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlay) h.1.2
  obtain ⟨⟨⟨hv, hn⟩, _⟩, hr⟩ := h
  have hv' := hv.keep hF hp hP' (by vzchk hF)
  refine ⟨⟨hv'.vc, hv'.hint, fun i hi => ?_⟩, ?_⟩
  · rcases (by omega : i < j ∨ i = j) with hi | rfl
    · exact hv'.z i hi
    · exact hz
  · rw [x', hn, and_flag _ hr]
    exact flag_congr ⟨fun ⟨h1, h2⟩ i hi => by
      rcases (by omega : i < j ∨ i = j) with hi | rfl
      exacts [h1 i hi, h2], fun h1 => ⟨fun i hi => h1 i (by omega), h1 j (by omega)⟩⟩

theorem zOne_vpiece : VPiece p S (Z0 p j) (Z0 p (j + 1)) (zOne P p j) :=
  (bu_vpiece hP hF hj).seq ((norm_vpiece hP hF hj).seq (and_vpiece hF hj))

end

end VG.Proof.MlDsa.AArch64.Verify
