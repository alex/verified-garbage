import VerifiedGarbage.Proof.MlKem.X86_64.KgA

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, the keys

Untrusted: everything here is checked by Lean. When every entry of `Â` was
sampled (`allOk`): `ŝ` and `ê` (`se_ok`), `t̂` encoded to `ek` (`row_ok`),
`ŝ` encoded to `dk` (`encS_ok`), and `ρ`, `ek`, `H(ek)` and `z` to the keys
(`fin_ok`). Between the steps, `KRest n r e`: the first `n` of `ŝ ‖ ê`, `r`
rows of `ek` and `e` of `dk` are done.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `ρ` of `σ`. -/
abbrev rhoK (σ : State) : List Byte := kgRho (kgD σ)

/-- `PRF₂(σ, N)`, in the outputs of `prfs`. -/
abbrev prfO (N : Nat) : Ptr := sc (oPR + 128 * N)

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure KRest0 (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK σ
  sig : bytesAt s.mem (pa s sigP) 32 = kgSigma (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ i < 3, ∀ j < 3, PolyIs s.mem (pa s (aS i j)) (aHat (rhoK σ) i j)

/-- The steps done after the outputs of `PRF₂`. -/
structure KRest (n r e : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK σ
  sig : bytesAt s.mem (pa s sigP) 32 = kgSigma (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ i < 3, ∀ j < 3, PolyIs s.mem (pa s (aS i j)) (aHat (rhoK σ) i j)
  prf : ∀ N < 6, bytesAt s.mem (pa s (prfO N)) 128 = prf 2 (kgSigma (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ k < n, PolyIs s.mem (pa s (pS k)) (ntt (cbd (kgSigma (kgD σ)) k))
  ek : ∀ i < r, bytesAt s.mem (pa s (.r12, 384 * i)) 384 = encode12 (kgT (aHat (rhoK σ)) (kgD σ) i)
  dk : ∀ j < e, bytesAt s.mem (pa s (.r13, 384 * j)) 384 = encode12 (kgS (kgD σ) j)

/-- A piece that writes `ws` keeps `KRest n r e`. -/
def restChk (n r e : Nat) (ws : List (Ptr × Nat)) : Bool :=
  kcChk ws && keepB kgB ws (sc oG) 32 && keepB kgB ws sigP 32 &&
    (List.range 9).all (fun e => keepB kgB ws (aS (e / 3) (e % 3)) 1024) &&
    (List.range 6).all (fun N => keepB kgB ws (prfO N) 128) &&
    (List.range n).all (fun k => keepB kgB ws (pS k) 1024) &&
    (List.range r).all (fun i => keepB kgB ws (.r12, 384 * i) 384) &&
    (List.range e).all (fun j => keepB kgB ws (.r13, 384 * j) 384)

theorem KRest.keep {σ : State} (hp : keyGenK.pre σ) {n r e : Nat} {s s' : State} (h : KRest n r e σ s)
    {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : restChk n r e ws = true) : KRest n r e σ s' := by
  simp only [restChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kA⟩, kR⟩, kP⟩, kE⟩, kD⟩ := hc
  have L := h.kc.lay hp
  refine ⟨h.kc.step hp hP.b hkc, by rw [L.keepBytes hP.b kG]; exact h.rho, by rw [L.keepBytes hP.b kS]; exact h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun i hi j hj => ?_,
    fun N hN => by rw [L.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L.keepPoly hP.b (kP k hk) (h.se k hk),
    fun i hi => by rw [L.keepBytes hP.b (kE i hi)]; exact h.ek i hi,
    fun j hj => by rw [L.keepBytes hP.b (kD j hj)]; exact h.dk j hj⟩
  have := kA (3 * i + j) (by omega)
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
  exact L.keepPoly hP.b this (h.mat i hi j hj)

/-- After the matrix, when every `SampleNTT` succeeded. -/
theorem KRest0.start {σ : State} {s : State} (h : KB 9 σ s) (ho : allOk (rhoK σ) 9) : KRest0 σ s := by
  refine ⟨h.a.kc, h.a.rho, h.a.sig, by rw [h.r15, ifp ho], fun i hi j hj => ?_⟩
  have := h.mat (3 * i + j) (by omega) (aHat (rhoK σ) i j)
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
  exact this (aHat_eq ho hi hj)

/-! ## The outputs of `PRF₂` -/

def prfsKChk : Bool :=
  prfsChk kgB kgW 6 oPR lPW && kcChk (prfsW 6 oPR lPW) && keepB kgB (prfsW 6 oPR lPW) (sc oG) 32 &&
    keepB kgB (prfsW 6 oPR lPW) sigP 32 &&
    (List.range 9).all (fun e => keepB kgB (prfsW 6 oPR lPW) (aS (e / 3) (e % 3)) 1024)

theorem prfsKChk_true : prfsKChk = true := by decide

theorem prfs_okK (v : Sample4Impl) {σ : State} (hp : keyGenK.pre σ) {s : State} (h : KRest0 σ s) :
    WP isa (v.callee.prfs 0 6 oPR lPW) s (KRest 0 0 0 σ) := by
  have hc := prfsKChk_true
  simp only [prfsKChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hpc, hkc⟩, kG⟩, kS⟩, kA⟩ := hc
  have L := h.kc.lay hp
  refine WP.mono (v.prfs_ok L kgB_bases (by decide) hpc) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L.keepBytes hP.b kS
  refine ⟨h.kc.step hp hP.b hkc, by rw [L.keepBytes hP.b kG]; exact h.rho, hσ.trans h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun i hi j hj => ?_, fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · have := kA (3 * i + j) (by omega)
    rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
    exact L.keepPoly hP.b this (h.mat i hi j hj)
  · rw [prfO, hP.pa rbx_cs, hb N hN, h.sig, Nat.zero_add]

/-! ## `ŝ` and `ê` -/

/-- What `se N` writes. -/
abbrev seW (N : Nat) : List (Ptr × Nat) := [(pS N, 1024)] ++ [(pS N, 1024), (sc oSS, 1024)]

def seChk (N : Nat) : Bool :=
  twoChk kgB kgW (prfO N) 128 (pS N) 1024 && ipChk kgB kgW (pS N) && restChk N 0 0 (seW N)

theorem seChk_all : ∀ N < 6, seChk N = true := by decide

theorem se_ok {A : Arith} (hA : ArithOk A) {σ : State} (hp : keyGenK.pre σ) {N : Nat} (hN : N < 6) {s : State} (h : KRest N 0 0 σ s) :
    WP isa (se A N) s (KRest (N + 1) 0 0 σ) := by
  have hc := seChk_all N hN
  simp only [seChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, hrc⟩ := hc
  have L := h.kc.lay hp
  unfold se
  refine WP.seq (WP.mono (cbd2At_okL L rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b kgB_bases
  rw [h.prf N hN, ← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hk := h.keep hp (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hrc
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.se k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂; exact hp₂

theorem r12_na : Reg.r12 ∉ argRegs := by decide
theorem r13_na : Reg.r13 ∉ argRegs := by decide
theorem r12_cs : Reg.r12 ∈ calleeSaved := by decide
theorem r13_cs : Reg.r13 ∈ calleeSaved := by decide

/-! ## `t̂`, encoded to `ek` -/

/-- What a sum of products writes. -/
abbrev dotW : List (Ptr × Nat) := [(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024), (sc oSS, 1024)] ++
  [(pS 15, 1024)] ++ [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)]

/-- What `row i` writes. -/
abbrev rowW (i : Nat) : List (Ptr × Nat) := dotW ++ [(pS 15, 1024)] ++ [((.r12, 384 * i), 384)]

def rowChk (i : Nat) : Bool :=
  dotChk kgB kgW (fun j => aS i j) pS && accChk kgB kgW (pS 15) (pS (3 + i)) && keepB kgB dotW (pS (3 + i)) 1024 &&
    twoChk kgB kgW (pS 15) 1024 (.r12, 384 * i) 384 && restChk 6 i 0 (rowW i)

theorem rowChk_all : ∀ i < 3, rowChk i = true := by decide

theorem row_ok {A : Arith} (hA : ArithOk A) {σ : State} (hp : keyGenK.pre σ) {i : Nat} (hi : i < 3) {s : State} (h : KRest 6 i 0 σ s) :
    WP isa (row A i) s (KRest 6 (i + 1) 0 σ) := by
  have hc := rowChk_all i hi
  simp only [rowChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hdc, hac⟩, hk3⟩, htw⟩, hrc⟩ := hc
  have L := h.kc.lay hp
  unfold row
  refine WP.seq (WP.mono (dotAt_ok hA L kgB_bases hdc (a := fun j => aHat (rhoK σ) i j) (b := kgS (kgD σ))
    (fun k hk => h.mat i hi k hk) (fun k hk => h.se k (by omega))) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b kgB_bases
  rw [← hP₁.pa rbx_cs] at hp₁
  have he₁ := L.keepPoly hP₁.b hk3 (h.se (3 + i) (by omega))
  refine WP.seq (WP.mono (addAt_ok L₁ rbx_na hac hp₁.1 he₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b kgB_bases
  rw [hp₁.2, he₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.mono (enc12At_okL L₂ r12_na htw hp₂.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have hk := h.keep hp (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by simp [calleeSaved])) hrc
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, hk.se, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.ek i' hi'
  · rw [hP₃.pa r12_cs, hb₃, hp₂.2]; rfl

/-! ## `ŝ`, encoded to `dk` -/

def encSChk (j : Nat) : Bool :=
  twoChk kgB kgW (pS j) 1024 (.r13, 384 * j) 384 && restChk 6 3 j [((.r13, 384 * j), 384)]

theorem encSChk_all : ∀ j < 3, encSChk j = true := by decide

theorem encS_ok {σ : State} (hp : keyGenK.pre σ) {j : Nat} (hj : j < 3) {s : State} (h : KRest 6 3 j σ s) :
    WP isa (encS j) s (KRest 6 3 (j + 1) σ) := by
  have hc := encSChk_all j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  have L := h.kc.lay hp
  have hs := h.se j (by omega)
  refine WP.mono (enc12At_okL L r13_na hc.1 hs.1) fun s' ⟨hP, hb⟩ => ?_
  have hk := h.keep hp hP hc.2
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, hk.se, hk.ek, fun j' hj' => ?_⟩
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
  · exact hk.dk j' hj'
  · rw [hP.pa r13_cs, hb, hs.2]; rfl

/-! ## The rest of the keys -/

theorem bytesAt_split (m : Mem) (s : State) (r : Reg) (o a b : Nat) :
    bytesAt m (pa s (r, o)) (a + b) = bytesAt m (pa s (r, o)) a ++ bytesAt m (pa s (r, o + a)) b := by
  rw [bytesAt_add, pa, pa, off_add]

/-- The keys. -/
structure KFin (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = 1
  ek : bytesAt s.mem (pa s (.r12, 0)) 1184 = ekPKE768 (aHat (rhoK σ)) (kgD σ)
  dk : bytesAt s.mem (pa s (.r13, 0)) 2400 = dkPKE768 (kgD σ) ++ ekPKE768 (aHat (rhoK σ)) (kgD σ) ++
    H (ekPKE768 (aHat (rhoK σ)) (kgD σ)) ++ kgZ σ

theorem fin_ok {σ : State} (hp : keyGenK.pre σ) {s : State} (h : KRest 6 3 3 σ s) :
    WP isa fin s (KFin σ) := by
  have L := h.kc.lay hp
  unfold fin
  -- `ρ` to `ek`.
  refine WP.seq (WP.mono (copy_okL L (dst := (.r12, 1152)) (src := sc oG) (n := 32) (by decide) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.kc.step hp hP₁.b (by decide)
  have L₁ := k₁.lay hp
  have hek : bytesAt s₁.mem (pa s₁ (.r12, 0)) 1184 = ekPKE768 (aHat (rhoK σ)) (kgD σ) := by
    rw [show (1184 : Nat) = 384 + (384 + (384 + 32)) from rfl, bytesAt_split, bytesAt_split, bytesAt_split,
      L.keepBytes hP₁.b (p := (.r12, 0)) (by decide), L.keepBytes hP₁.b (p := (.r12, 0 + 384)) (by decide),
      L.keepBytes hP₁.b (p := (.r12, 0 + 384 + 384)) (by decide), hP₁.pa (p := (.r12, 0 + 384 + 384 + 384)) (by decide),
      show 0 + 384 + 384 + 384 = 1152 from rfl, hb₁, h.rho]
    have e0 := h.ek 0 (by decide); have e1 := h.ek 1 (by decide); have e2 := h.ek 2 (by decide)
    simp only [Nat.reduceMul] at e0 e1 e2
    rw [e0, e1, e2]
    simp only [ekPKE768, List.append_assoc]
  -- `ek` to `dk`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := (.r13, 1152)) (src := (.r12, 0)) (n := 1184) (by decide) (by decide))
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step hp hP₂.b (by decide)
  have L₂ := k₂.lay hp
  rw [hek] at hb₂
  have hek₂ : bytesAt s₂.mem (pa s₂ (.r12, 0)) 1184 = ekPKE768 (aHat (rhoK σ)) (kgD σ) := by
    rw [L₁.keepBytes hP₂.b (by decide)]; exact hek
  -- `H(ek)`.
  refine WP.seq (WP.mono (hash_ok kgB_bases (ps := [((.r12, 0), 1184)]) (rate := 136) (out := (.r13, 2336))
    (len := 32) (by decide) (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_)
  have k₃ := k₂.step hp hP₃.b (by decide)
  have L₃ := k₃.lay hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hek₂, sha3Suffix6] at hb₃
  rw [← H_eq] at hb₃
  -- `z`.
  refine WP.mono (copy_okL L₃ (dst := (.r13, 2368)) (src := (.rbp, 32)) (n := 32) (by decide) (by decide))
    fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have k₄ := k₃.step hp hP₄.b (by decide)
  rw [k₃.z] at hb₄
  refine ⟨k₄, ?_, ?_, ?_⟩
  · rw [hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]
  · rw [L₃.keepBytes hP₄.b (by decide), L₂.keepBytes hP₃.b (by decide)]; exact hek₂
  · rw [show (2400 : Nat) = 384 + (384 + (384 + (1184 + (32 + 32)))) from rfl, bytesAt_split, bytesAt_split,
      bytesAt_split, bytesAt_split, bytesAt_split]
    simp only [Nat.reduceAdd]
    have d0 := h.dk 0 (by decide); have d1 := h.dk 1 (by decide); have d2 := h.dk 2 (by decide)
    simp only [Nat.reduceMul] at d0 d1 d2
    rw [L₃.keepBytes hP₄.b (p := (.r13, 0)) (by decide), L₂.keepBytes hP₃.b (p := (.r13, 0)) (by decide),
      L₁.keepBytes hP₂.b (p := (.r13, 0)) (by decide), L.keepBytes hP₁.b (p := (.r13, 0)) (by decide), d0,
      L₃.keepBytes hP₄.b (p := (.r13, 384)) (by decide), L₂.keepBytes hP₃.b (p := (.r13, 384)) (by decide),
      L₁.keepBytes hP₂.b (p := (.r13, 384)) (by decide), L.keepBytes hP₁.b (p := (.r13, 384)) (by decide), d1,
      L₃.keepBytes hP₄.b (p := (.r13, 768)) (by decide), L₂.keepBytes hP₃.b (p := (.r13, 768)) (by decide),
      L₁.keepBytes hP₂.b (p := (.r13, 768)) (by decide), L.keepBytes hP₁.b (p := (.r13, 768)) (by decide), d2,
      L₃.keepBytes hP₄.b (p := (.r13, 1152)) (by decide), L₂.keepBytes hP₃.b (p := (.r13, 1152)) (by decide),
      hP₂.pa (p := (.r13, 1152)) (by decide), hb₂,
      L₃.keepBytes hP₄.b (p := (.r13, 2336)) (by decide), hP₃.pa (p := (.r13, 2336)) (by decide), hb₃,
      hP₄.pa (p := (.r13, 2368)) (by decide), hb₄]
    simp only [dkPKE768, List.append_assoc]

end KeyGen

end VG.Proof.MlKem.X86_64
