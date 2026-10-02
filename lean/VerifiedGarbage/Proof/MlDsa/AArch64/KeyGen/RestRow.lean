import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack

/-!
# ML-DSA key generation on AArch64: the rows of `t`

Row `i` of `t`: the sum of the products `Â[i, j] ŝ₁[j]` in `t` (`mul_ok`,
`mulAdd_ok`), `NTT⁻¹` of it plus `s₂[i]` (`inv_ok`, `addS2_ok`), then
`Power2Round` (`p2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`sbp_ok`, `bp_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs
  NatPolyIs bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega

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

theorem range_t0 {m : Mem} {q : Addr} {t : Poly} (h : PolyIs m q (t.map fun c => ofInt (power2Round c).2)) :
    BpRange m q 4095 4096 := fun j hj => by
  rw [coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  omega

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega

/-! ## The checks of the calls -/

section
variable {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hF hi

theorem mul_chk {j : Nat} (hj : j < p.ℓ) : mulChk kgR (kgW p) (tP p) (aP (p.ℓ * i + j)) (sP p j) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have := idx_lt hi hj
  unfold mulChk; lay

theorem inv_chk : ipChk kgR (kgW p) (tP p) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold ipChk; lay

theorem add_chk : accChk kgR (kgW p) (tP p) (sP p (p.ℓ + i)) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold accChk; lay

theorem p2r_chk : p2rChk kgR (kgW p) (tP p) (t1P p) (t0P p) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold p2rChk; lay

theorem sbp_chk : rwChk kgR (kgW p) (t1P p) 1024 (.x26, 32 + 320 * i) 320 = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold rwChk; lay [hF.pk]

theorem bp_chk : rwChk kgR (kgW p) (t0P p) 1024 (.x27, oT0 p + 416 * i) 416 = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> (unfold rwChk; lay [hF.pk, hF.sk, hlen])

end

theorem sbpOk_t1 : SbpOk 1023 320 := ⟨by decide, by decide, by decide⟩

theorem bpOk_t0 : BpOk 4095 4096 416 := ⟨by decide, by decide, by decide⟩

/-! ## The calls -/

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State} (hp : kgPre p S' σ)
  {i : Nat} (hi : i < p.k)
include hP hF hp hi

/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem mul_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State} (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => dotK p A S i 1) A S s' := by
  have hl := hF.l
  have L := h.kc.lay hF hp
  have hA := h.polyA hi (j := 0) (by omega)
  have hc := mul_chk hF hi (j := 0) (by omega)
  rw [Nat.add_zero] at hA hc
  have hS := h.polyS (j := 0) (by omega)
  refine WP.mono (mulAt_ok hP.s64 hP.mul L hc hA.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (by krchk hF), ?_⟩
  rw [tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem mulAdd_ok {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => dotK p A S i j) A S s) :
    WP isa (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => dotK p A S i (j + 1)) A S s' := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  have hA := h.polyA hi hj
  have hS := h.polyS hj
  refine WP.mono (mulAddAt_ok hP.s64 hP.mulAdd L (mul_chk hF hi hj) ht.1 hA.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (by krchk hF), ?_⟩
  rw [tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hS.2, ← ht.2]
  exact hb

/-- `t = NTT⁻¹(t)`. -/
theorem inv_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => dotK p A S i p.ℓ) A S s) :
    WP isa (invNttAt P (sc oSS) (tP p)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s' := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  unfold invNttAt
  refine WP.mono (ipAt_ok (t := nttInv) hP.s64 hP.invNtt L (inv_chk hF hi) ht.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (by krchk hF), ?_⟩
  rw [tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), ← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => tK p A S i) A S s' := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  have hS := h.s2 i hi
  unfold addAt
  refine WP.mono (accAt_ok (op := add) hP.s64 hP.add L (add_chk hF hi) ht.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (by krchk hF), ?_⟩
  rw [tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => tK p A S i) A S s) :
    WP isa (power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  refine WP.mono (p2rAt_ok hP.s64 hP.power2Round L (p2r_chk hF hi) ht.1) fun s' ⟨hP', x', h1, h0⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (by krchk hF), ?_, ?_⟩
  · rw [hP'.pa (p := t1P p) (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP'.pa (p := t0P p) (show Reg.x28 ∈ keptRegs by decide), ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)) :
    WP isa (simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) s fun s' =>
      KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (sbpAt_ok hP.s64 hP.simpleBitPack L (sbp_chk hF hi) sbpOk_t1 (t1_bound h1))
    fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (by krchk hF), L.keepPoly hP' (by lay [hF.pk]) h0, ?_⟩
  rw [hP'.pa (show Reg.x26 ∈ keptRegs by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023) :
    WP isa (bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) s
      (KR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (bp_chk hF hi) bpOk_t0 h0.1 (range_t0 h0))
    fun s' ⟨hP', x', hb⟩ => ?_
  have hk' := h.keep hF hp hP' x' (by krchk hF)
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by
      rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
      · rw [L.keepBytes hP' (by lay [hF.pk, hF.sk, hlen])]; exact h1, ?_⟩
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, h0.2, modPm_t0]
    rfl

end

/-! ## The pieces of a row -/

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_piece : Piece p S' (KRx p (p.ℓ + p.k) p.ℓ i) (RowI p i (tIs p fun A S => dotK p A S i 1))
    (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hl := hF.l
  have hc := mul_chk hF hi (j := 0) (by omega)
  rw [Nat.add_zero] at hc
  refine ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (mul_ok hP hF hp hi h) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (aP (p.ℓ * i))) ∧ Reduced x.mem (pa x (sP p 0))) ∧
    (Reduced y.mem (pa y (aP (p.ℓ * i))) ∧ Reduced y.mem (pa y (sP p 0)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => by
      have a₁ := h₁.polyA hi (j := 0) (by omega); have a₂ := h₂.polyA hi (j := 0) (by omega)
      rw [Nat.add_zero] at a₁ a₂
      exact ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨a₁.1, (h₁.polyS (j := 0) (by omega)).1⟩,
        ⟨a₂.1, (h₂.polyS (j := 0) (by omega)).1⟩⟩
  exact mulAt_tr hP.mul (kgOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem mulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    Piece p S' (RowI p i (tIs p fun A S => dotK p A S i j)) (RowI p i (tIs p fun A S => dotK p A S i (j + 1)))
      (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (mulAdd_ok hP hF hp hi hj h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (aP (p.ℓ * i + j))) ∧ Reduced x.mem (pa x (sP p j))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (aP (p.ℓ * i + j))) ∧ Reduced y.mem (pa y (sP p j)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩,
        ⟨t₂.1, (h₂.polyA hi hj).1, (h₂.polyS hj).1⟩⟩
  exact mulAddAt_tr hP.mulAdd (kgOk p) (mul_chk hF hi hj) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem inv_piece : Piece p S' (RowI p i (tIs p fun A S => dotK p A S i p.ℓ))
    (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ))) (invNttAt P (sc oSS) (tP p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (inv_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  unfold invNttAt
  exact ipAt_tr (t := nttInv) hP.invNtt (kgOk p) (inv_chk hF hi) fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem addS2_piece : Piece p S' (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => tK p A S i)) (addAt P (tP p) (sP p (p.ℓ + i))) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  unfold addAt
  exact accAt_tr (op := add) hP.add (kgOk p) (add_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p S' (RowI p i (tIs p fun A S => tK p A S i)) (RowI p i (p2rIs p i))
    (power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr hP.power2Round (kgOk p) (p2r_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p S' (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  exact sbpAt_tr hP.simpleBitPack (kgOk p) (sbp_chk hF hi) sbpOk_t1 fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem bp_piece : Piece p S' (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (t0P p)) ∧ BpRange x.mem (pa x (t0P p)) 4095 4096) ∧
    (Reduced y.mem (pa y (t0P p)) ∧ BpRange y.mem (pa y (t0P p)) 4095 4096)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1.1, range_t0 t₁.1⟩, ⟨t₂.1.1, range_t0 t₂.1⟩⟩
  exact bpAt_tr hP.bitPack (kgOk p) (bp_chk hF hi) bpOk_t0 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

end

end VG.Proof.MlDsa.AArch64.KeyGen
