import VerifiedGarbage.Proof.MlKem.X86_64.KgA

/-!
# ML-KEM on x86-64: key generation, the keys

When every entry of `Â` was sampled (`allOk`): `ŝ` and `ê` (`se_ok`), `t̂`
encoded to `ek` (`row_ok`), `ŝ` encoded to `dk` (`encS_ok`), and `ρ`, `ek`,
`H(ek)` and `z` to the keys (`fin_ok`). Between the steps, `KRest n r e`: the
first `n` of `ŝ ‖ ê`, `r` rows of `ek` and `e` of `dk` are done.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem bytesAt_split (m : Mem) (s : State) (r : Reg) (o a b : Nat) :
    bytesAt m (pa s (r, o)) (a + b) = bytesAt m (pa s (r, o)) a ++ bytesAt m (pa s (r, o + a)) b := by
  rw [bytesAt_add, pa, pa, off_add]

/-- `k` consecutive pieces of `c` bytes. -/
theorem bytesAt_catK (m : Mem) (s : State) (r : Reg) (o c : Nat) (f : Nat → List Byte) :
    ∀ k, (∀ i < k, bytesAt m (pa s (r, o + c * i)) c = f i) → bytesAt m (pa s (r, o)) (c * k) = KPke.catK f k
  | 0, _ => rfl
  | k + 1, h => by
    rw [KPke.catK, KPke.foldK_succ List.nil_append, ← KPke.catK, Nat.mul_succ, bytesAt_split,
      bytesAt_catK m s r o c f k fun i hi => h i (by omega), h k (by omega)]

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `ρ` of `σ`. -/
abbrev rhoK (L : Kem) (σ : State) : List Byte := KPke.kgRho L.p (kgD σ)

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure KRest0 (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoK L σ) (e / L.k) (e % L.k))

/-- The steps done after the outputs of `PRF₂`. -/
structure KRest (L : Kem) (n r e : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoK L σ) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k, bytesAt s.mem (pa s (prfO L N)) 128 = prf 2 (KPke.kgSigma L.p (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ k < n, PolyIs s.mem (pa s (pS k)) (ntt (cbd (KPke.kgSigma L.p (kgD σ)) k))
  ek : ∀ i < r, bytesAt s.mem (pa s (.r12, 384 * i)) 384 = encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) i)
  dk : ∀ j < e, bytesAt s.mem (pa s (.r13, 384 * j)) 384 = encode12 (KPke.kgS L.p (kgD σ) j)

theorem KRest.keep {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {n r e : Nat} {s s' : State}
    (h : KRest L n r e σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : restChk L n r e ws = true) :
    KRest L n r e σ s' := by
  simp only [restChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kA⟩, kR⟩, kP⟩, kE⟩, kD⟩ := hc
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, by rw [L₀.keepBytes hP.b kS]; exact h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kP k hk) (h.se k hk),
    fun i hi => by rw [L₀.keepBytes hP.b (kE i hi)]; exact h.ek i hi,
    fun j hj => by rw [L₀.keepBytes hP.b (kD j hj)]; exact h.dk j hj⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
theorem KRest0.start {L : Kem} {σ : State} {s : State} (h : KB L (L.k * L.k) σ s) (ho : allOk L.k (rhoK L σ) (L.k * L.k)) :
    KRest0 L σ s :=
  ⟨h.a.kc, h.a.rho, h.a.sig, by rw [h.m.r15, ifp ho], fun e he =>
    h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

/-- `Â[i, j]`, from the entries. -/
theorem KRest.matIJ {L : Kem} {n r e : Nat} {σ s : State} (h : KRest L n r e σ s) {i j : Nat} (hi : i < L.k)
    (hj : j < L.k) : PolyIs s.mem (pa s (L.aS i j)) (aHat (rhoK L σ) i j) := by
  have := h.mat (L.k * i + j) (ij_lt hi hj)
  rwa [(divmod_ij hj).1, (divmod_ij hj).2, ← aS_ij] at this

/-! ## The outputs of `PRF₂` -/

theorem prfs_okK (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KRest0 L σ s) : WP isa (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW) s (KRest L 0 0 0 σ) := by
  have hc := W.prfs
  simp only [prfsKChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hpc, hkc⟩, kG⟩, kS⟩, kA⟩ := hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (v.prfs_ok L₀ (kgB_bases L) (by have := W.k; omega) hpc) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b kS
  refine ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, hσ.trans h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [prfO, hP.pa rbx_cs, hb N hN, h.sig, Nat.zero_add]

/-! ## `ŝ` and `ê` -/

theorem se_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {N : Nat}
    (hN : N < 2 * L.k) {s : State} (h : KRest L N 0 0 σ s) : WP isa (se L A N) s (KRest L (N + 1) 0 0 σ) := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, hrc⟩ := hc
  have L₀ := h.kc.lay W hp
  unfold se
  refine WP.seq (WP.mono (cbd2At_okL L₀ rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b (kgB_bases L)
  rw [h.prf N hN, ← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hk := h.keep W hp (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hrc
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

theorem row_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {i : Nat}
    (hi : i < L.k) {s : State} (h : KRest L (2 * L.k) i 0 σ s) : WP isa (row L A i) s (KRest L (2 * L.k) (i + 1) 0 σ) := by
  have hc := W.row i hi
  simp only [rowChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hdc, hac⟩, hk3⟩, htw⟩, hrc⟩ := hc
  have L₀ := h.kc.lay W hp
  unfold row
  refine WP.seq (WP.mono (dotN_ok hA (kgB_bases L) W.k.1 (dotChk_spec hdc) L₀ (a := fun j => aHat (rhoK L σ) i j)
    (b := KPke.kgS L.p (kgD σ)) (fun k hk => h.matIJ hi hk) (fun k hk => h.se k (by omega))) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b (kgB_bases L)
  rw [← hP₁.pa rbx_cs] at hp₁
  have he₁ := L₀.keepPoly hP₁.b hk3 (h.se (L.k + i) (by omega))
  refine WP.seq (WP.mono (addAt_ok L₁ rbx_na hac hp₁.1 he₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (kgB_bases L)
  rw [hp₁.2, he₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.mono (enc12At_okL L₂ r12_na htw hp₂.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have hk := h.keep W hp (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by simp [calleeSaved])) hrc
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, hk.se, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.ek i' hi'
  · rw [hP₃.pa r12_cs, hb₃, hp₂.2]; rfl

/-! ## `ŝ`, encoded to `dk` -/

theorem encS_ok {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {j : Nat} (hj : j < L.k) {s : State}
    (h : KRest L (2 * L.k) L.k j σ s) : WP isa (encS j) s (KRest L (2 * L.k) L.k (j + 1) σ) := by
  have hc := W.encS j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  have L₀ := h.kc.lay W hp
  have hs := h.se j (by omega)
  refine WP.mono (enc12At_okL L₀ r13_na hc.1 hs.1) fun s' ⟨hP, hb⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, hk.se, hk.ek, fun j' hj' => ?_⟩
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
  · exact hk.dk j' hj'
  · rw [hP.pa r13_cs, hb, hs.2]; rfl

/-! ## The rest of the keys -/

/-- `ek` and `dk_PKE`. -/
abbrev ekK (L : Kem) (σ : State) : List Byte := KPke.ekPKE L.p (aHat (rhoK L σ)) (kgD σ)
abbrev dkK (L : Kem) (σ : State) : List Byte := KPke.dkPKE L.p (kgD σ)

/-- The keys. -/
structure KFin (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = 1
  ek : bytesAt s.mem (pa s (.r12, 0)) L.ekLen = ekK L σ
  dk : bytesAt s.mem (pa s (.r13, 0)) L.dkLen = dkK L σ ++ ekK L σ ++ H (ekK L σ) ++ kgZ σ

theorem fin_ok {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State} (h : KRest L (2 * L.k) L.k L.k σ s) :
    WP isa (fin L) s (KFin L σ) := by
  have L₀ := h.kc.lay W hp
  unfold fin
  -- `ρ` to `ek`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.kc.step W hp hP₁.b W.f₁K
  have L₁ := k₁.lay W hp
  have hek : bytesAt s₁.mem (pa s₁ (.r12, 0)) L.ekLen = ekK L σ := by
    rw [Kem.ekLen, Params.ekLen, bytesAt_split, show 0 + 384 * L.p.k = 384 * L.k from Nat.zero_add _,
      hP₁.pa (p := (.r12, 384 * L.k)) r12_cs, hb₁, h.rho, ekK, KPke.ekPKE]
    refine congrArg (· ++ _) (bytesAt_catK _ _ _ _ _ _ L.k fun i hi => ?_)
    rw [Nat.zero_add, L₀.keepBytes hP₁.b (W.f₁E i hi)]
    exact h.ek i hi
  -- `ek` to `dk`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step W hp hP₂.b W.f₂K
  have L₂ := k₂.lay W hp
  rw [hek] at hb₂
  have hek₂ : bytesAt s₂.mem (pa s₂ (.r12, 0)) L.ekLen = ekK L σ := by
    rw [L₁.keepBytes hP₂.b W.f₂E]; exact hek
  -- `H(ek)`.
  refine WP.seq (WP.mono (hash_ok (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
    (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_)
  have k₃ := k₂.step W hp hP₃.b W.f₃K
  have L₃ := k₃.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hek₂, sha3Suffix6] at hb₃
  rw [← H_eq] at hb₃
  -- `z`.
  refine WP.mono (copy_okL L₃ (dst := (.r13, 384 * L.k + L.ekLen + 32)) (src := (.rbp, 32)) (n := 32) (by decide) W.f₄)
    fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have k₄ := k₃.step W hp hP₄.b W.f₄K
  rw [k₃.z] at hb₄
  refine ⟨k₄, ?_, ?_, ?_⟩
  · rw [hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]
  · rw [L₃.keepBytes hP₄.b W.f₄E, L₂.keepBytes hP₃.b W.f₃E]; exact hek₂
  · have hP := PPost.app (PPost.app (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hP₃ (by simp [calleeSaved])) hP₄
      (by simp [calleeSaved])
    have hP' := PPost.app hP₃ hP₄ (by simp [calleeSaved])
    rw [show L.dkLen = 384 * L.k + L.ekLen + 32 + 32 by
        simp only [Kem.k, Kem.dkLen, Kem.ekLen, Params.dkLen, Params.ekLen]; omega,
      bytesAt_split, bytesAt_split, bytesAt_split, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    rw [hP₄.pa (p := (.r13, 384 * L.k + L.ekLen + 32)) r13_cs, hb₄,
      L₃.keepBytes hP₄.b W.dkH, hP₃.pa (p := (.r13, 384 * L.k + L.ekLen)) r13_cs, hb₃,
      L₂.keepBytes hP'.b W.dkE, hP₂.pa (p := (.r13, 384 * L.k)) r13_cs, hb₂, dkK, KPke.dkPKE]
    refine congrArg (· ++ _ ++ _ ++ _) (bytesAt_catK _ _ _ _ _ _ L.k fun j hj => ?_)
    rw [Nat.zero_add, L₀.keepBytes hP.b (W.dkS j hj)]
    exact h.dk j hj

end KeyGen

end VG.Proof.MlKem.X86_64
