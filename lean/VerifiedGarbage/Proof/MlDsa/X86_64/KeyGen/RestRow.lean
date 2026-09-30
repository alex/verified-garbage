import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestPack

/-!
# ML-DSA key generation on x86-64: the rows of `t`

Untrusted: everything here is checked by Lean. Row `i` of `t`: the sum of
the products `Â[i, j] ŝ₁[j]` in `t` (`mul_ok`, `mulAdd_ok`), `NTT⁻¹` of it
plus `s₂[i]` (`inv_ok`, `addS2_ok`), then `Power2Round` (`p2r_ok`) and
`t₁[i]` packed to `pk` and `t₀[i]` to `sk` (`sbp_ok`, `bp_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs
  NatPolyIs bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- In row `i`, with `f` holding what the row computed so far. -/
def KRow (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

/-- The `t` so far. -/
abbrev tIs (p : Params) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (A : Nat → Poly) (S : Nat → IPoly) (s : State) :
    Prop := PolyIs s.mem (pa s (tP p)) (g A S)

theorem KR.polyA {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (aP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (sP p j)) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem tP_ok {p : Params} (hF : PFacts p) : PtrOk (tP p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega)

theorem tP1_ok {p : Params} (hF : PFacts p) : PtrOk (t1P p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega)

theorem tP0_ok {p : Params} (hF : PFacts p) : PtrOk (t0P p) :=
  sc_ok _ (by have := hF.kl; have := hF.l; have := hF.k; simp only [oP]; omega)

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem packIn_t0 {m : Mem} {q : Addr} {t : Poly} (h : PolyIs m q (t.map fun c => ofInt (power2Round c).2)) :
    PackIn m q 4095 4096 := by
  refine ⟨h.1, fun j hj => ?_⟩
  rw [coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  omega

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {i : Nat}
  (hi : i < p.k)
include hP hF hp hi


/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem mul_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State} (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P.mul (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => dotK p A S i 1) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega)
  rw [Nat.add_zero] at hx0
  have S₀ := h.kc.site hF hp
  have hA := h.polyA hi (j := 0) (by omega)
  rw [Nat.add_zero] at hA
  have hS := h.polyS (j := 0) (by omega)
  refine WP.mono (mulAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega)) (sc_ok _ (by simp only [oP]; omega))
    (by lay) (by lay) (by lay) hP.mul S₀ hA.1 hS.1) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem mulAdd_ok {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => dotK p A S i j) A S s) :
    WP isa (mulAddAt P.mulAdd (tP p) (aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => dotK p A S i (j + 1)) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have hx0 := idx_lt hi hj
  have S₀ := h.kc.site hF hp
  have hA := h.polyA hi hj
  have hS := h.polyS hj
  refine WP.mono (mulAddAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega)) (sc_ok _ (by simp only [oP]; omega))
    (by lay) (by lay) (by lay) hP.mulAdd S₀ ht.1 hA.1 hS.1) fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hS.2, ← ht.2]
  exact hb

/-- `t = NTT⁻¹(t)`. -/
theorem inv_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => dotK p A S i p.ℓ) A S s) :
    WP isa (invNttAt P.invNtt (tP p)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  unfold invNttAt
  refine WP.mono (ipAt_ok (t := nttInv) (f := tP p) (tP_ok hF) (by lay) (by lay) (by lay) hP.invNtt S₀ ht.1)
    fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases, ← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (addAt P.add (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => tK p A S i) A S s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  have hS := h.s2 i hi
  refine WP.mono (addAt_ok (tP_ok hF) (sc_ok _ (by simp only [oP]; omega)) (by lay) (by lay) hP.add S₀ ht.1 hS.1)
    fun s' ⟨hP', hx, hb⟩ => ?_
  have hP'' : PPostB s s' [(tP p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF), ?_⟩
  rw [tIs, hP''.pa (p := tP p) rbx_bases, Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => tK p A S i) A S s) :
    WP isa (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  dsimp only [tIs] at ht
  have S₀ := h.kc.site hF hp
  refine WP.mono (p2rAt_ok (tP_ok hF) (tP1_ok hF) (tP0_ok hF) (by lay) (by lay) (by lay) (by lay) (by lay)
    hP.power2Round S₀ ht.1) fun s' ⟨hP', hx, h1, h0⟩ => ?_
  have hP'' : PPostB s s' [(t1P p, 1024), (t0P p, 1024)] := hP'.b
  refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF), ?_, ?_⟩
  · rw [hP''.pa (p := t1P p) rbx_bases, Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP''.pa (p := t0P p) rbx_bases, ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)) :
    WP isa (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  refine WP.mono (sbpAt_ok (by decide) (by decide) (tP1_ok hF)
    ⟨by omega, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk]) (by lay [hF.pk]) hP.simpleBitPack S₀
    fun j hj => ?_) fun s' ⟨hP', hx, hb⟩ => ?_
  · rw [show (coeffAt s.mem (pa s (t1P p)) j).toNat = (t1K p A S i)[j]'hj from by
      rw [← h1]; simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn]]
    simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
    omega
  · have hP'' : PPostB s s' [((.r12, 32 + 320 * i), 320)] := hP'.b
    refine ⟨h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF),
      polyIs_frame' L hP'' (by lay [hF.pk]) h0, ?_⟩
    rw [hP''.pa (p := (.r12, 32 + 320 * i)) (show Reg.r12 ∈ bases by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023) :
    WP isa (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) s
      (KR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have S₀ := h.kc.site hF hp
  have L := S₀.lay
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  refine WP.mono (bpAt_ok (by decide) (by decide) (tP0_ok hF)
    ⟨by simp only [oT0, hlen]; omega, show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk, hF.sk, hlen])
    (by lay [hF.pk, hF.sk, hlen]) hP.bitPack S₀ (packIn_t0 h0)) fun s' ⟨hP', hx, hb⟩ => ?_ <;>
  · have hP'' : PPostB s s' [((.r13, oT0 p + 416 * i), 416)] := hP'.b
    have hk' := h.keep hF hp hP'' hx (hP'.cs .r15 (by decide)) (by krchk hF)
    refine ⟨hk'.kc, hk'.r15, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
      fun i' hi' => ?_⟩
    rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
    · exact hk'.rows i' hi'
    · refine ⟨by rw [L.keepBytes hP'' (by lay [hF.pk, hF.sk, hlen])]; exact h1, ?_⟩
      rw [hP''.pa (p := (.r13, oT0 p + 416 * i')) (show Reg.r13 ∈ bases by decide), hb, h0.2, modPm_t0]
      rfl

end

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [Spec.MlDsa.natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega

/-! ## The pieces of a row -/

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_piece : Piece p (KRx p (p.ℓ + p.k) p.ℓ i) (RowI p i (tIs p fun A S => dotK p A S i 1))
    (mulAt P.mul (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (mul_ok hP hF hp hi h) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (Reduced x.mem (pa x (aP (p.ℓ * i))) ∧ Reduced x.mem (pa x (sP p 0))) ∧
    (Reduced y.mem (pa y (aP (p.ℓ * i))) ∧ Reduced y.mem (pa y (sP p 0)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => by
      have a₁ := h₁.polyA hi (j := 0) (by omega); have a₂ := h₂.polyA hi (j := 0) (by omega)
      rw [Nat.add_zero] at a₁ a₂
      exact ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨a₁.1, (h₁.polyS (j := 0) (by omega)).1⟩,
        ⟨a₂.1, (h₂.polyS (j := 0) (by omega)).1⟩⟩
  exact mulAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega)) (sc_ok _ (by simp only [oP]; omega)) (by lay) (by lay)
    (by lay) hP.mul (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.rbx ∈ kgRegs by decide)

theorem mulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    Piece p (RowI p i (tIs p fun A S => dotK p A S i j)) (RowI p i (tIs p fun A S => dotK p A S i (j + 1)))
      (mulAddAt P.mulAdd (tP p) (aP (p.ℓ * i + j)) (sP p j)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (mulAdd_ok hP hF hp hi hj h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (aP (p.ℓ * i + j))) ∧
    Reduced x.mem (pa x (sP p j))) ∧ (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (aP (p.ℓ * i + j))) ∧
    Reduced y.mem (pa y (sP p j)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩,
        ⟨t₂.1, (h₂.polyA hi hj).1, (h₂.polyS hj).1⟩⟩
  exact mulAddAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega)) (sc_ok _ (by simp only [oP]; omega)) (by lay)
    (by lay) (by lay) hP.mulAdd (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.rbx ∈ kgRegs by decide)

theorem inv_piece : Piece p (RowI p i (tIs p fun A S => dotK p A S i p.ℓ))
    (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ))) (invNttAt P.invNtt (tP p)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (inv_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  unfold invNttAt
  exact ipAt_tr (tP_ok hF) (by lay) (by lay) (by lay) hP.invNtt (show Reg.rbx ∈ kgRegs by decide)

theorem addS2_piece : Piece p (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (addAt P.add (tP p) (sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  exact addAt_tr (tP_ok hF) (sc_ok _ (by simp only [oP]; omega)) (by lay) (by lay) hP.add
    (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p (RowI p i (tIs p fun A S => Proof.MlDsa.KeyGen.tK p A S i)) (RowI p i (p2rIs p i))
    (power2RoundAt P.power2Round (tP p) (t1P p) (t0P p)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr (tP_ok hF) (tP1_ok hF) (tP0_ok hF) (by lay) (by lay) (by lay) (by lay) (by lay) hP.power2Round
    (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide)

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((Proof.MlDsa.KeyGen.tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.r12, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (simpleBitPackAt P.simpleBitPack (t1P p) 1023 (.r12, 32 + 320 * i) 320) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  exact sbpAt_tr (by decide) (by decide) (tP1_ok hF) ⟨by omega, show Reg.r12 ∉ MlKem.X86_64.argRegs by decide⟩
    (by lay [hF.pk]) (by lay [hF.pk]) hP.simpleBitPack (show Reg.rbx ∈ kgRegs by decide)
    (show Reg.r12 ∈ kgRegs by decide)

theorem bp_piece : Piece p (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (bitPackAt P.bitPack (t0P p) 4095 4096 (.r13, oT0 p + 416 * i) 416) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p x y ∧ PackIn x.mem (pa x (t0P p)) 4095 4096 ∧
    PackIn y.mem (pa y (t0P p)) 4095 4096) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, packIn_t0 t₁.1, packIn_t0 t₂.1⟩
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact bpAt_tr (by decide) (by decide) (tP0_ok hF)
    ⟨by simp only [oT0, hlen]; omega, show Reg.r13 ∉ MlKem.X86_64.argRegs by decide⟩ (by lay [hF.pk, hF.sk, hlen])
    (by lay [hF.pk, hF.sk, hlen]) hP.bitPack (show Reg.rbx ∈ kgRegs by decide) (show Reg.r13 ∈ kgRegs by decide)

end

end VG.Proof.MlDsa.X86_64.KeyGen
