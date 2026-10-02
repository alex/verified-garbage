import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.SeedsCT
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Mask

/-!
# ML-DSA key generation on 32-bit ARM: the samplers

The primitives key generation calls, verified with at most `S` bytes of stack
(`PrimsOk`); and the entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂`
(`expS_piece`): after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`
(`KSamp`), each polynomial is reduced (and those of `s₁ ‖ s₂` small), and
`r11` is what `Good` says.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly toRq polyAt coeffAt Reduced
  PolyIs Outcome)
open VG.Proof.MlDsa.KeyGen (seedA seedS Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract Arm.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract Arm.abi stk) S
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract Arm.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract Arm.abi stk) S
  add : Callee P.add (fun stk => Spec.MlDsa.addContract Arm.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract Arm.abi stk) S
  rejBounded : Callee P.rejBounded (fun stk => Spec.MlDsa.rejBoundedContract Arm.abi stk) S
  power2Round : Callee P.power2Round (fun stk => Spec.MlDsa.power2RoundContract Arm.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract Arm.abi stk) S
  bitPack : Callee P.bitPack (fun stk => Spec.MlDsa.bitPackContract Arm.abi stk) S

/-! ## `r11` -/

theorem and11_ok (s : State) :
    WP isa (.block and11) s (· = s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)) := by
  apply WP.of_runBlock
  simp only [and11, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
    Option.some.injEq, exists_eq_left']

theorem Site.setReg {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {r : Reg}
    (hr : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7) (v : BitVec 32) : Site L Wb STK (s.setReg r v) :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, h.p1, h.s8, h.spk,
    by rw [gpr_setReg_of_ne _ _ hr.2.2.2.symm]; exact h.r7, by rw [gpr_setReg_of_ne _ _ hr.1.symm]; exact h.r4,
    by rw [gpr_setReg_of_ne _ _ hr.2.1.symm]; exact h.r5, by rw [gpr_setReg_of_ne _ _ hr.2.2.1.symm]; exact h.r6,
    h.cw, h.cr⟩

theorem K1.r11 {p : Params} {STK : Nat} {σ s : State} (h : K1 p STK σ s) (v : BitVec 32) :
    K1 p STK σ (s.setReg .r11 v) :=
  ⟨⟨h.kc.site.setReg (by decide) v, h.kc.rd, h.kc.wr, h.kc.sp, h.kc.sav, h.kc.lr, h.kc.xi⟩, h.hx, h.sa, h.sb, h.z⟩

/-! ## What the samplers leave -/

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (STK : Nat) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : K1 p STK σ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem ((lay p STK σ).A 0 (oP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r'))) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p (xiOf σ) e r A S (s.gpr .r11)

/-- A part that keeps `K1`, the polynomials sampled so far and `r11` keeps `KSamp`. -/
theorem KSamp.keep {p : Params} {STK : Nat} {σ : State} {e r : Nat} {s s' : State} (h : KSamp p STK σ e r s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((lay p STK σ).RL W) s s') (hc : k1Chk p STK W = true)
    (ha : ∀ e' < e, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e', 1024) W = true)
    (hs : ∀ r' < r, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + r'), 1024) W = true)
    (h11 : s'.gpr .r11 = s.gpr .r11) : KSamp p STK σ e r s' := by
  have hL := h.k1.kc.site.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.keep hk hc, A, S, fun e' he' => ?_, fun r' hr' => ?_, by rw [h11]; exact hG⟩
  · exact polyIs_keepW hL hk.frame (ha e' he') (by decide) rfl (hA e' he')
  · exact ⟨polyIs_keepW hL hk.frame (hs r' hr') (by decide) rfl (hS r' hr').1, (hS r' hr').2⟩

theorem KSamp.zero {p : Params} {STK : Nat} {σ s : State} (h : K1 p STK σ s) (h11 : s.gpr .r11 = 1) :
    KSamp p STK σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h11]; exact Proof.MlDsa.KeyGen.good_zero _ _ _ _⟩

/-! ## A sampled polynomial, masked -/

/-- `and11` and `mask`, after a sampler whose result `r0` is 0 or 1. -/
theorem andMask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (hw : ix a.1 ∈ Wb) (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) :
    WP isa (.seq (.block and11) (mask a)) s fun s' =>
      Kept (L.RL [tri a 1024]) (s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)) s' ∧
      s'.gpr .r11 = s.gpr .r11 &&& s.gpr .r0 ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t = if s.gpr .r0 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  refine WP.seq (WP.mono (and11_ok s) fun s₁ e₁ => ?_)
  subst e₁
  have h0 : (s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)).gpr .r0 = s.gpr .r0 := gpr_setReg_of_ne _ _ (by decide)
  refine WP.mono (mask_ok (hs.setReg (by decide) _) pa hw (by rw [h0]; exact hr)) fun s' ⟨k, co⟩ =>
    ⟨k, ?_, fun t ht => by rw [co t ht, h0]; rfl⟩
  rw [k.cs .r11 (by decide) (by decide)]
  exact gpr_setReg_self _ _ _

/-- What a sampler and its mask leave in entry `j` of the polynomials, from
the facts the sampler's contract gives. -/
theorem masked_poly {m m' : Mem} {q : Addr} {r : BitVec 32} (hred : r = 1 → Reduced m q)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (polyAt m' q) ∧ (r = 1 → polyAt m' q = polyAt m q) ∧
      (r ≠ 1 → PolyIs m' q (toRq (Vector.replicate 256 0))) := by
  by_cases h1 : r = 1
  · have := Proof.MlDsa.KeyGen.masked_one h1 h
    exact ⟨⟨this.2 (hred h1), rfl⟩, fun _ => this.1, fun h => absurd h1 h⟩
  · have := Proof.MlDsa.KeyGen.masked_zero h1 h
    exact ⟨⟨this.1, rfl⟩, fun h => absurd h h1, fun _ => this⟩

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) : seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-- The seed and the call of `RejNTTPoly`. -/
theorem rnA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (hs : Site (lay p STK σ) kWb STK s) {Q : State → Prop}
    (hQ : ∀ s', Kept ((lay p STK σ).RL [tri (aP e) 1024, tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem ((lay p STK σ).A 0 (oP e))) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem ((lay p STK σ).A 0 oSA) 34)) (s'.gpr .r0)
        (polyAt s'.mem ((lay p STK σ).A 0 (oP e))) → Q s') :
    WP isa (rejNttAt P (sc oSA) (aP e)) s Q := by
  have := hF.kl
  exact rn_ok hP.rejNtt hs (by omega) (sd := sc oSA) (a := aP e) (w := sc oSS)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide, show ix Reg.r7 ∈ kWb by decide, by lsep hF,
      by lsep hF, by lsep hF⟩ hQ

theorem expA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : KSamp p STK σ e 0 s) :
    WP isa (expA P p e) s (KSamp p STK σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  have hs := h.k1.kc.site
  unfold expA sampled
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (setB_ok hs (q := sc (oSA + 32)) ⟨sc_ok _, by lsep hF⟩ (by decide)
    (by decide) (e % p.ℓ)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSA + 33))
      ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) (e / p.ℓ)) fun s₂ ⟨k₂, b₂⟩ => ?_))
  have h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₁.cs .r11 (by decide) (by decide))
  have h₂ := h₁.keep k₂ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₂.cs .r11 (by decide) (by decide))
  have hs₂ := h₂.k1.kc.site
  have hseed : bytesAt s₂.mem ((lay p STK σ).A 0 oSA) 34 = seedA (rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    have b₁' := bytes_keepW hs.ok k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₂.k1.sa,
      add_ofNat_add, add_ofNat_add, seedA_eq, List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32 + 1)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
    rw [e1, e2]; rfl
  -- the call
  refine WP.seq (rnA_ok hP hF hS he hs₂ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have hs₃ := hs₂.kept k₃
  -- the result and the mask
  refine WP.mono (andMask_ok hs₃ (a := aP e) ⟨sc_ok _, by lsep hF⟩ (show ix Reg.r7 ∈ kWb by decide) hr01) fun s₄ ⟨k₄, r₄, co⟩ => ?_
  have h₃ := h₂.keep k₃ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₃.cs .r11 (by decide) (by decide))
  obtain ⟨A, S', hA, _, hG⟩ := h₃.ex
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have hL := hs.ok
  refine ⟨(h₃.k1.r11 _).keep k₄ (by lsep hF [k1Chk, kcChk]),
    fun e' => if e' = e then polyAt s₄.mem ((lay p STK σ).A 0 (oP e)) else A e', S', fun e' he' => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]; exact polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hA e' he')
    · rw [ifp rfl]; exact pi
  · rw [r₄]; exact Proof.MlDsa.KeyGen.good_A he hG hout p1

/-! ## An entry of `s₁ ‖ s₂` -/

omit hP hF hS in
theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) : seedS ρ' r = ρ' ++ [BitVec.ofNat 8 r, 0] := by
  simp only [seedS, Proof.MlDsa.KeyGen.integerToBytes_two hr]

omit hP hS in
theorem eta_of : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

/-- The call of `RejBoundedPoly`. -/
theorem rbS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (hs : Site (lay p STK σ) kWb STK s)
    {Q : State → Prop}
    (hQ : ∀ s', Kept ((lay p STK σ).RL [tri (sP p r) 1024, tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) →
      Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (bytesAt s.mem ((lay p STK σ).A 0 oSB) 66)).map toRq)
        (s'.gpr .r0) (polyAt s'.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) → Q s') :
    WP isa (rejBoundedAt P (sc oSB) p.η (sP p r)) s Q := by
  have := hF.kl
  exact rb_ok hP.rejBounded hs (by omega) (sd := sc oSB) (a := sP p r) (w := sc oSS)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
      show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩ (eta_of hF) hQ

theorem expS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (h : KSamp p STK σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (KSamp p STK σ (p.k * p.ℓ) (r + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold expS sampled
  refine WP.seq (WP.mono (setB_ok hs (q := sc (oSB + 64)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) r)
    fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
    (k₁.cs .r11 (by decide) (by decide))
  have hs₁ := h₁.k1.kc.site
  have hseed : bytesAt s₁.mem ((lay p STK σ).A 0 oSB) 66 = seedS (rho'Of p σ) r := by
    rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₁.k1.sb,
      add_ofNat_add, add_ofNat_add, seedS_eq _ (by omega), List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₁.mem ((lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
    have e2 : bytesAt s₁.mem ((lay p STK σ).A 0 (oSB + 64 + 1)) 1 = [0] := h₁.k1.z
    rw [e1, e2]; rfl
  refine WP.seq (rbS_ok hP hF hS hr hs₁ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have hs₃ := hs₁.kept k₃
  refine WP.mono (andMask_ok hs₃ (a := sP p r) ⟨sc_ok _, by lsep hF⟩ (show ix Reg.r7 ∈ kWb by decide) hr01)
    fun s₄ ⟨k₄, r₄, co⟩ => ?_
  have h₃ := h₁.keep k₃ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
    (k₃.cs .r11 (by decide) (by decide))
  obtain ⟨A, S', hA, hS', hG⟩ := h₃.ex
  obtain ⟨pi, p1, p0⟩ := masked_poly hred co
  obtain ⟨z, hz, hz1, hz0, hG'⟩ := Proof.MlDsa.KeyGen.good_S hr hG hout
  have hL := hs.ok
  refine ⟨(h₃.k1.r11 _).keep k₄ (by lsep hF [k1Chk, kcChk]), A, fun r' => if r' = r then z else S' r',
    fun e' he' => polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hA e' he'), fun r' hr' => ?_,
    by rw [r₄]; exact hG'⟩
  dsimp only
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · rw [ifn (by omega)]
    exact ⟨polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hS' r' hr').1, (hS' r' hr').2⟩
  · rw [ifp rfl]
    refine ⟨?_, hz⟩
    show PolyIs s₄.mem (lpa (lay p STK σ) (sP p r')) (toRq z)
    by_cases h1 : s₃.gpr .r0 = 1
    · rw [hz1 h1, ← p1 h1]; exact pi
    · rw [hz0 h1]; exact p0 h1

/-! ## Constant time -/

omit hP hF hS in
theorem rho_pub {σ₁ σ₂ : State} (pub : kgPub p σ₁ σ₂) : rhoOf p σ₁ = rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).1

omit hP hF hS in
theorem rej_pub {σ₁ σ₂ : State} (pub : kgPub p σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).2 r hr

omit hP hF hS in
theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
theorem setS_taint : ∀ v < 16, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block (setB (sc (oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem andMask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP j))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem expA_two {e : Nat} (he : e < p.k * p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32) (expA P p e)
      fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((lay p STK σ).A 0 oSA) 34 = bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 ++
      [BitVec.ofNat 8 (e % p.ℓ), BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, Site (lay p STK σ) kWb STK x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x hs =>
    WP.block_append (WP.mono (setB_ok hs (q := sc (oSA + 32)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide)
      (e % p.ℓ)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSA + 33)) ⟨sc_ok _, by lsep hF⟩
        (by decide) (by decide) (e / p.ℓ)) fun s₂ ⟨k₂, b₂⟩ => ⟨⟨_, (k₁.monoL (W' := [tri (sc (oSA + 32)) 1,
          tri (sc (oSA + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩, by
        have hL := hs.ok
        have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
        have b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)).trans
          (bytes_keepW hL k₁.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32 + 1)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32)
    (taint7 (fun _ _ h => h.1) (setIJ_taint _ (by omega) _ (by omega))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (lay p STK σ) kWb STK x y ∧
        bytesAt x.mem ((lay p STK σ).A 0 oSA) 34 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  have ok := fun x (hs : Site (lay p STK σ) kWb STK x) =>
    rnA_ok hP hF hS he hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (rn_tr hP.rejNtt (by omega) (sd := sc oSA) (a := aP e) (w := sc oSS)
      ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
        show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint7 (fun _ _ h => h) (andMask_taint _ (by omega))

theorem expA_tr {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (Rel2 (Pre p STK) (kgPub p) fun σ s => KSamp p STK σ e 0 s) (expA P p e) fun _ _ => True :=
  rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32)
    (RelCT.exists_ fun σ => expA_two hP hF hS he σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
      ⟨σ₁, kc_twoL pub h₁.k1.kc h₂.k1.kc, by
        rw [h₁.k1.sa, lay_pub pub, h₂.k1.sa, rho_pub pub]⟩

theorem expS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧ bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      bytesAt y.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((lay p STK σ).A 0 oSB) 64) r)) (expS P p r)
      fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold expS sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    (bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] →
      bytesAt x'.mem ((lay p STK σ).A 0 oSB) 66 = seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r)
  have hF1 : ∀ x, Site (lay p STK σ) kWb STK x → WP isa (.block (setB (sc (oSB + 64)) r)) x (F x) := fun x hs =>
    WP.mono (setB_ok hs (q := sc (oSB + 64)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) r) fun x' ⟨k₁, b₁⟩ =>
      ⟨⟨_, k₁⟩, fun hz => by
        have hL := hs.ok
        have b₀ := bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)
        have b₂ := bytes_keepW hL k₁.frame (i := 0) (o := oSB + 64 + 1) (l := 1) (by lsep hF) (by decide) (by decide)
        rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, seedS_eq _ (by omega), List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt x'.mem ((lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
        have e2 : bytesAt x.mem ((lay p STK σ).A 0 (oSB + 64 + 1)) 1 = [0] := hz
        rw [e1, b₂, e2]; rfl⟩
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧ bytesAt y.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((lay p STK σ).A 0 oSB) 64) r))
    (taint7 (fun _ _ h => h.1) (setS_taint _ (by omega))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (lay p STK σ) kWb STK x y ∧
        Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem ((lay p STK σ).A 0 oSB) 66) =
          Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem ((lay p STK σ).A 0 oSB) 66))
      fun x' y' ⟨_, x, y, ⟨T, zx, zy, hl⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx zx, by' zy, hl]⟩) ?_
  have ok := fun x (hs : Site (lay p STK σ) kWb STK x) =>
    rbS_ok hP hF hS hr hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (rb_tr hP.rejBounded (by omega) (sd := sc oSB) (a := sP p r)
      (w := sc oSS) ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩,
        show ix Reg.r7 ∈ kWb by decide, show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      (eta_of hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint7 (fun _ _ h => h) (andMask_taint _ (by omega))

theorem expS_tr {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (Rel2 (Pre p STK) (kgPub p) fun σ s => KSamp p STK σ (p.k * p.ℓ) r s) (expS P p r)
      fun _ _ => True :=
  rel_of (RelCT.exists_ fun σ => expS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, kc_twoL pub h₁.k1.kc h₂.k1.kc, h₁.k1.z, by rw [lay_pub pub]; exact h₂.k1.z, by
      rw [h₁.k1.sb, lay_pub pub, h₂.k1.sb]; exact rej_pub pub hr⟩

/-! ## The pieces -/

theorem expA_piece {e : Nat} (he : e < p.k * p.ℓ) :
    KPiece p STK (fun σ s => KSamp p STK σ e 0 s) (fun σ s => KSamp p STK σ (e + 1) 0 s) (expA P p e) :=
  ⟨fun _ _ _ h => expA_ok hP hF hS he h, expA_tr hP hF hS he⟩

theorem expS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) r s) (fun σ s => KSamp p STK σ (p.k * p.ℓ) (r + 1) s)
      (expS P p r) :=
  ⟨fun _ _ _ h => expS_ok hP hF hS hr h, expS_tr hP hF hS hr⟩

/-- The entries of `Â`. -/
theorem sampA_piece :
    KPiece p STK (fun σ s => K1 p STK σ s ∧ s.gpr .r11 = 1) (fun σ s => KSamp p STK σ (p.k * p.ℓ) 0 s)
      (seqR (expA P p) 0 (p.k * p.ℓ)) := by
  refine Piece.mono (Piece.seqR (I := fun e σ s => KSamp p STK σ e 0 s) (p.k * p.ℓ) 0
    fun e _ he => expA_piece hP hF hS (by omega)) (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
  simpa using h

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) 0 s) (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => KSamp p STK σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => expS_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.Arm.KeyGen
