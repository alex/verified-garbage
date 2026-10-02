import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.Sign.Iter

/-!
# ML-DSA signing on AArch64: the commitment of an iteration

At the head of iteration `t` of the loop (`IL`): what decoding left, `κ = ℓt`
at `KAP`, `814 - t` at `CNT`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`
(`maskR_ok`), `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])` (`rowW_ok`),
`w1Encode(HighBits(w[i]))` at `W1` (`w1R_ok`), and `c̃ = H(μ ‖ w1Encode(w₁),
λ/4)` at `CT` (`commit_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) i j

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : Poly := toRq (yF p (rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : Poly := yhF p (rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : Poly := wF p (Am p σ) (rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (Am p σ) (muOf σ) (rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) maxBounds 0 t

end

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : aVal p σ (p.ℓ * i + j) = Am p σ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [aVal, e1, e2]

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  kap : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * t)
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  t_lt : t < 814
  rej : RejT p σ t

/-- A piece that writes `ws` keeps what decoding left (but `KAP` and `CNT`). -/
def ikChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  idChk p ws p.ℓ p.k p.k && keepB (sgR p) (sgW p) ws (sc oMS) 64

/-- A piece that writes `ws` keeps `IL`. -/
def ilChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && keepB (sgR p) (sgW p) ws (sc oKAP) 8 && keepB (sgR p) (sgW p) ws (sc oCNT) 8

theorem IK.step {p : Params} {D : Nat} {σ s s' : State} (h : IK p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : ikChk p ws = true) : IK p D σ s' := by
  simp only [ikChk, Bool.and_eq_true] at hc
  exact ⟨h.d.step hP hc.1, (h.d.im.st.lay.keepBytes hP hc.2).trans h.rpp⟩

theorem IL.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : IL p D σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : ilChk p ws = true) : IL p D σ t s' := by
  simp only [ilChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP h1, (L.keepW hP h2).trans h.kap, (L.keepW hP h3).trans h.cnt, h.t_lt, h.rej⟩

theorem IL.st {p : Params} {D : Nat} {σ s : State} {t : Nat} (h : IL p D σ t s) : St p D σ s := h.k.d.im.st

/-! ## `κ + r` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 64 x).setWidth 8, (BitVec.ofNat 64 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [integerToBytes_two]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega

theorem add_one_ne (a : Addr) : a ≠ a + 1 := by
  intro h
  have := congrArg BitVec.toNat h
  have ha := a.isLt
  rw [BitVec.toNat_add] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  omega

theorem bytes2_write (m : Mem) (a : Addr) (v w : Byte) :
    bytesAt ((m.writeW a v).writeW (a + 1) w) a 2 = [v, w] := by
  show [((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 0),
    ((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 1)] = _
  have e0 : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
  have e1 : a + BitVec.ofNat 64 1 = a + 1 := rfl
  rw [e0, e1, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlKem.writeW8_apply, ifn (add_one_ne a), ifp rfl,
    VG.Proof.MlKem.writeW8_apply, ifp rfl]

/-- `κ + r` to `MS + 64`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKappa_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r x : Nat}
    (hr : r < 4096) (hx : x + r < 2 ^ 16) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : inB wbs (sc (oMS + 64)) 2 = true) (hk : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKappa r)) s fun s' => PPostB D s s' [(sc (oMS + 64), 2)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s (sc (oMS + 64))) 2 = integerToBytes (x + r) 2 := by
  have e65 : pa s (sc (oMS + 65)) = pa s (sc (oMS + 64)) + 1 := (pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 64))) 1 := by
    have := Offset.contains_base (pa s (sc (oMS + 64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMS + 64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (setKappa_run r hr s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s (sc (oMS + 64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨postB_of_keep k (by decide) hf, k.get .x24, ?_⟩
  rw [hm, e65, bytes2_write, hk, ofNat64_add, kappa_bytes hx]

/-! ## `y` and `ŷ` -/

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure ICm (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  l : IL p D σ t s
  y : Fam s (yBase p) r (Yv p σ (p.ℓ * t))
  yh : Fam s (yhBase p) r (YHv p σ (p.ℓ * t))

def icmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  ilChk p ws && famChk (sgR p) (sgW p) ws (yBase p) r && famChk (sgR p) (sgW p) ws (yhBase p) r

theorem ICm.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : ICm p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : icmChk p ws r = true) : ICm p D σ t r s' := by
  simp only [icmChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `y[r]` and `ŷ[r]` need of the layout. -/
def mChk (p : Params) (r : Nat) : Bool :=
  let y := pS (yBase p + r)
  let yh := pS (yhBase p + r)
  let w1 : List (Ptr × Nat) := [(sc (oMS + 64), 2)]
  let w2 : List (Ptr × Nat) := [(y, 1024), (sc oPS, 2048)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  icmChk p w1 r && inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMS + 64)) 2 && maskChkS (sgR p) (sgW p) y &&
    icmChk p w2 r && copyChk (sgR p) (sgW p) yh y 1024 && icmChk p w3 r && famChk (sgR p) (sgW p) w3 (yBase p) (r + 1) &&
    ipChkS (sgR p) (sgW p) yh && icmChk p w4 r && famChk (sgR p) (sgW p) w4 (yBase p) (r + 1) &&
    decide (p.ℓ * 813 + r < 2 ^ 16) && decide (r < 4096) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem maskR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : mChk p r = true) {s : State} (h : ICm p D σ t r s) : WP isa (maskR P p r) s (ICm p D σ t (r + 1)) := by
  simp only [mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, k1⟩, w1⟩, cm⟩, c2⟩, cc⟩, c3⟩, f3⟩, ci⟩, c4⟩, f4⟩, hx⟩, hr⟩, hγ⟩ := hc
  have ht := h.l.t_lt
  unfold maskR
  have hx' : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega); omega
  refine WP.seq (WP.mono (setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.step hP1 c1
  have hms : bytesAt s1.mem (pa s1 (sc oMS)) 66 = rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, I1.l.k.rpp, pa_sc_add, hP1.pa (by decide), hb1]
  refine WP.seq (WP.mono (maskAt_ok hP I1.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_)
  rw [hms] at hq2
  have I2 := I1.step hP2 c2
  have hy2 : Fam s2 (yBase p) (r + 1) (Yv p σ (p.ℓ * t)) :=
    Fam.snoc I2.y (by
      show PolyIs s2.mem (pa s2 (pS (yBase p + r))) _
      rw [hP2.pa (pS_bases _)]; exact hq2)
  refine WP.seq (WP.mono (copy_ok I2.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := I2.step hP3 c3
  have hyh3 : Pl s3 (yhBase p + r) (Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (pS_bases _)]
    exact polyIs_of_bytes hb3 (hy2 r (by omega))
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, Fam.keep I3.l.st.lay hP4 f4 (Fam.keep I2.l.st.lay hP3 f3 hy2), Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (pS_bases _), hyh3.2] at *
  exact hq4

/-! ## `w` -/

/-- Iteration `t`, with `y`, `ŷ`, and the first `i` polynomials of `w`. -/
structure ICw (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  l : IL p D σ t s
  y : Fam s (yBase p) p.ℓ (Yv p σ (p.ℓ * t))
  yh : Fam s (yhBase p) p.ℓ (YHv p σ (p.ℓ * t))
  w : Fam s (wBase p) i (Wv p σ (p.ℓ * t))

def icwChk (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  icmChk p ws p.ℓ && famChk (sgR p) (sgW p) ws (wBase p) i

theorem ICw.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : ICw p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : icwChk p ws i = true) : ICw p D σ t i s' := by
  simp only [icwChk, Bool.and_eq_true] at hc
  have I : ICm p D σ t p.ℓ s' := (ICm.mk h.l h.y h.yh).step hP hc.1
  exact ⟨I.l, I.y, I.yh, Fam.keep h.l.st.lay hP hc.2 h.w⟩

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (σ : State) (κ i m : Nat) : Poly :=
  ((List.range m).map fun j => multiplyNTT (Am p σ i j) (YHv p σ κ j)).foldl add zero

theorem add_zero_left (x : Poly) : add zero x = x := by
  apply Vector.ext
  intro j hj
  simp [add, zero]

theorem wAcc_one (p : Params) (σ : State) (κ i : Nat) :
    wAcc p σ κ i 1 = multiplyNTT (Am p σ i 0) (YHv p σ κ 0) := by
  simp only [wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, add_zero_left]

theorem wAcc_succ (p : Params) (σ : State) (κ i m : Nat) :
    wAcc p σ κ i (m + 1) = add (wAcc p σ κ i m) (multiplyNTT (Am p σ i m) (YHv p σ κ m)) := by
  simp only [wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem aP_ij (p : Params) (i j : Nat) : aP p i j = pS (aBase p + (p.ℓ * i + j)) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j) = _
  rw [Nat.add_assoc (5 + 4 * p.k + 3 * p.ℓ)]

/-- What `w[i]` needs of the layout. -/
def wChk (p : Params) (i : Nat) : Bool :=
  let w := pS (wBase p + i)
  (List.range p.ℓ).all (fun j => mulChk (sgR p) (sgW p) w (aP p i j) (yhP p j)) && ipChkS (sgR p) (sgW p) w &&
    icwChk p [(w, 1024)] i && icwChk p [(w, 1024), (sc oPS, 1024)] i && decide (0 < p.ℓ)

theorem rowW_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : wChk p i = true) (hi : i < p.k) {s : State} (h : ICw p D σ t i s) :
    WP isa (rowW P p i) s (ICw p D σ t (i + 1)) := by
  simp only [wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, c2⟩, hl⟩ := hc
  have hA : ∀ {s : State} (I : ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (pa s (aP p i j)) (Am p σ i j) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [aVal_ij hj] at this
      rw [aP_ij]; exact this
  have hY : ∀ {s : State} (I : ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (pa s (yhP p j)) (YHv p σ (p.ℓ * t) j) :=
    fun I j hj => I.yh j hj
  unfold rowW
  refine WP.seq (WP.mono (mulAt_ok hP.mul h.l.st.lay (cm 0 hl) (hA h 0 hl).1 (hY h 0 hl).1)
    fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 c1
  rw [(hA h 0 hl).2, (hY h 0 hl).2, ← wAcc_one] at hq1
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => ICw p D σ t i s ∧ Pl s (wBase p + i) (wAcc p σ (p.ℓ * t) i j))
    (p.ℓ - 1) 1 (fun j hj1 hj s ⟨I, hw⟩ => ?_) s1 ⟨I1, by show PolyIs _ _ _; rw [hP1.pa (pS_bases _)]; exact hq1⟩)
    fun s2 ⟨I2, hw2⟩ => ?_)
  · refine WP.mono (mulAddAt_ok hP.mulAdd I.l.st.lay (cm j (by omega)) hw.1 (hA I j (by omega)).1
      (hY I j (by omega)).1) fun s' ⟨hP', _, hq'⟩ => ⟨I.step hP' c1, ?_⟩
    rw [hw.2, (hA I j (by omega)).2, (hY I j (by omega)).2, ← wAcc_succ] at hq'
    show PolyIs _ _ _
    rw [hP'.pa (pS_bases _)]; exact hq'
  rw [show 1 + (p.ℓ - 1) = p.ℓ by omega] at hw2
  refine WP.mono (ipAt_ok (t := nttInv) hP.invNtt I2.l.st.lay ci hw2.1) fun s3 ⟨hP3, _, hq3⟩ => ?_
  have I3 := I2.step hP3 c2
  refine ⟨I3.l, I3.y, I3.yh, Fam.snoc I3.w ?_⟩
  show PolyIs _ _ _
  rw [hP3.pa (pS_bases _)]
  rw [hw2.2] at hq3
  exact hq3

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (σ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => simpleBitPack (w1F p (Am p σ) (rppOf p σ) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `ŷ`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure ICh (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  c : ICw p D σ t p.k s
  w1 : bytesAt s.mem (pa s (sc oW1)) (w1Len p * i) = w1Enc p σ (p.ℓ * t) i

/-- What `w1Encode(w₁[i])` needs of the layout. -/
def hChk (p : Params) (i : Nat) : Bool :=
  let w := pS (wBase p + i)
  let o := sc (oW1 + w1Len p * i)
  rwChk (sgR p) (sgW p) w 1024 t1P 1024 && rwChk (sgR p) (sgW p) t1P 1024 o (w1Len p) &&
    icwChk p [(t1P, 1024)] p.k && icwChk p [(o, w1Len p)] p.k && keepB (sgR p) (sgW p) [(t1P, 1024)] (sc oW1) (w1Len p * i) &&
    keepB (sgR p) (sgW p) [(o, w1Len p)] (sc oW1) (w1Len p * i) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (p.γ₂ ∈ gamma2s)

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

theorem w1R_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : hChk p i = true) (hi : i < p.k) {s : State} (h : ICh p D σ t i s) :
    WP isa (w1R P p i) s (ICh p D σ t (i + 1)) := by
  simp only [hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, k1⟩, k2⟩, e1⟩, e2⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine WP.seq (WP.mono (highBitsAt_ok hP h.c.l.st.lay hγ c1 (h.c.w i hi).1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.c.step hP1 k1
  rw [(h.c.w i hi).2] at hq1
  refine WP.mono (sbpAt_ok hP I1.l.st.lay hb rfl c2 fun j hj => ?_) fun s2 ⟨hP2, _, hq2⟩ => ?_
  · rw [hP1.pa (by decide), natPolyIs_coeff hq1 hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _
  have I2 := I1.step hP2 k2
  refine ⟨I2, ?_⟩
  have b1 : bytesAt s2.mem (pa s2 (sc oW1)) (w1Len p * i) = w1Enc p σ (p.ℓ * t) i := by
    rw [I1.l.st.lay.keepBytes hP2 e2, h.c.l.st.lay.keepBytes hP1 e1, h.w1]
  have b2 : bytesAt s2.mem (pa s2 (sc (oW1 + w1Len p * i))) (w1Len p) =
      simpleBitPack (w1F p (Am p σ) (rppOf p σ) (p.ℓ * t) i) (w1Max p) := by
    rw [hP2.pa (sc_bases _), hq2, hP1.pa (by decide), show natPolyAt s1.mem (pa s t1P) = _ from hq1]
    rfl
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, pa_sc_add, b1, b2, w1Enc, w1Enc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton]

/-- The commitment of iteration `t`: `y`, `ŷ`, `w`, and `c̃` at `CT`. -/
structure IC (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICw p D σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  (List.range p.ℓ).all (mChk p) && (List.range p.k).all (wChk p) && (List.range p.k).all (hChk p) &&
    hashChk (sgR p) (sgW p) [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩ &&
    icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : Ok3 p) : cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem commit_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : IL p D σ t s) : WP isa (commitWith keccak.callee P p) s (IC p D σ t) := by
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, hk⟩ := hc
  unfold commitWith
  refine WP.seq (WP.mono (seqR_ok (I := fun r => ICm p D σ t r) p.ℓ 0
    (fun r _ hr s hs => maskR_ok hP (hm r (by omega)) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ICw p D σ t i) p.k 0
    (fun i _ hi s hs => rowW_ok hP (hw i (by omega)) (by omega) hs) s1
    ⟨hs1.l, hs1.y, hs1.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ICh p D σ t i) p.k 0
    (fun i _ hi s hs => w1R_ok hP (hh i (by omega)) (by omega) hs) s2
    ⟨hs2, by simp [w1Enc]; rfl⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  refine WP.mono (shake_ok hP.s16 hP.s64 hs3.c.l.st.lay (by simp) hs) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs3.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  show H (bytesAt s3.mem (pa s3 (.x26, 0)) 64 ++ bytesAt s3.mem (pa s3 (sc oW1)) (p.k * w1Len p)) (cLen p) = _
  rw [Nat.mul_comm p.k, hs3.w1, hs3.c.l.st.mu]
  simp only [CTv, ctF, w1Encode, List.flatMap_map]

end VG.Proof.MlDsa.AArch64.Sign
