import VerifiedGarbage.Proof.MlKem.X86_64.DcDec

/-!
# ML-KEM on x86-64: decapsulation

After K-PKE.Decrypt (`DcDec.lean`): `G(m' ‖ h)` and `J(z ‖ c)` (`hashes_ok`),
K-PKE.Encrypt in the context `dcX` (which keeps `K'` and `K̄`), and the choice
of the key (`select_okD`). The function returns 1 with
`ML-KEM.Decaps_internal(dk, c)` in `key` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`kemDecaps_correct`); it leaks
only the pointers and `ρ` (`kemDecaps_ct`). Each parameter set's file moves
this to its shared contract.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

/-- `m'`, `(K', r') = G(m' ‖ h)`, `K̄ = J(z ‖ c)` and the encryption key of `σ`. -/
abbrev dcM' (L : Kem) (σ : State) : List Byte := KPke.decM L.p (dcDk L σ) (dcC L σ)
abbrev dcG (L : Kem) (σ : State) : List Byte × List Byte := G (dcM' L σ ++ KPke.dkH L.p (dcDk L σ))
abbrev dcKb (L : Kem) (σ : State) : List Byte := J (KPke.dkZ L.p (dcDk L σ) ++ dcC L σ)
abbrev dcEk (L : Kem) (σ : State) : List Byte := KPke.dkEk L.p (dcDk L σ)

/-- What `K-PKE.Encrypt` keeps: `DC`, `K'` at `G` and `K̄` at `KB`. -/
structure DCK (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcG L σ).1
  kb : bytesAt s.mem (pa s (sc oKB)) 32 = dcKb L σ

theorem DCK.step (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) {s s' : State} (h : DCK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : dckChk L ws = true) : DCK L σ s' := by
  simp only [dckChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.k, by rw [L₀.keepBytes hP hc.2]; exact h.kb⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def dcX (W : DcWf L) (σ : State) : Ctx (dcR L) (dcW L) where
  Out s := (decapsK L).pre σ ∧ DCK L σ s
  chk := dckChk L
  bs := dcB_bases L
  lay h := h.2.dc.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def dcXA (W : DcWf L) : Ctx (dcR L) (dcW L) where
  Out s := ∃ σ, (decapsK L).pre σ ∧ DCK L σ s
  chk := dckChk L
  bs := dcB_bases L
  lay := fun ⟨_, hp, h⟩ => h.dc.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

/-! ## `G(m' ‖ h)` and `J(z ‖ c)` -/

theorem shakeSuffix31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI (W : DcWf L) (σ s : State) : Prop :=
  Enc.EIn L (dcX W σ) (.rbp, 384 * L.k) (dcEk L σ) (dcM' L σ) (dcG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) {s : State} (h : DM L σ s) :
    WP isa (hashes L) s (EncI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * L.k + 96 = L.dkLen := rfl
  unfold hashes
  -- `G(m' ‖ h)`.
  refine WP.seq (WP.mono (hash_ok (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    slice_of h.dc.dk (show 768 * L.k + 32 + 32 ≤ L.dkLen by omega), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  -- `J(z ‖ c)`.
  refine WP.mono (hash_ok (dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136)
    (out := sc oKB) (len := 32) W.h₂ (show 0x1f < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.h₂K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.c,
    slice_of k₁.dk (show 768 * L.k + 64 + 32 ≤ L.dkLen by omega), shakeSuffix31] at hb₂
  rw [← J_eq, ← hP₂.pa rbx_cs] at hb₂
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (dcM' L σ ++ KPke.dkH L.p (dcDk L σ)) := by
    rw [L₁.keepBytes hP₂.b W.h₂G]; exact hb₁
  have hK : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = (dcG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hr : bytesAt s₂.mem (pa s₂ sigP) 32 = (dcG L σ).2 := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨⟨hp, k₂, hK, hb₂⟩, slice_of k₂.dk (show 384 * L.k + (384 * L.k + 32) ≤ L.dkLen by omega), ?_, hr⟩, ?_⟩
  · rw [L₁.keepBytes hP₂.b W.h₂M, L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]

/-! ## The key -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (W : DcWf L) (σ s : State) : Prop :=
  Enc.EOut L (dcX W σ) (.rbp, 384 * L.k) (dcEk L σ) (dcM' L σ) (dcG L σ).2 s

/-- At the end: `r15` as `allOk`, and the key if it is 1. -/
structure DEnd (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) then 1 else 0
  key : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) → bytesAt s.mem (pa s (.r12, 0)) 32 =
    if dcC L σ = KPke.ct L.p (aHat (Enc.rhoE L (dcEk L σ))) (dcEk L σ) (dcM' L σ) (dcG L σ).2 then (dcG L σ).1
    else dcKb L σ

theorem select_okD (W : DcWf L) {σ : State} {s : State} (h : EncO W σ s) : WP isa (select L) s (DEnd L σ) := by
  have hp := h.out.1
  have k := h.out.2
  have L₀ := k.dc.lay W hp
  have cR : ∀ {p : Ptr} {l : Nat}, inB (dcB L) p l = true → InRegions (s.rd ++ s.wr) (pa s p) l := fun hi =>
    L₀.cR hi _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  obtain ⟨i1, i2, i3, i4, i5, s1, s2⟩ := W.sel
  refine WP.mono (select_ok W.ct.1 W.ct.2.1 W.ct.2.2 (cR i1) (cR i2) (cR i3) (cR i4)
    (L₀.cW i5 _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩) (L₀.disj s1) (L₀.disj s2))
    fun s' ⟨hP, hb⟩ => ?_
  refine ⟨k.dc.step W hp hP.b W.selK, by rw [hP.cs .r15 (by decide)]; exact h.r15, fun ho => ?_⟩
  rw [hP.pa KeyGen.r12_cs, hb]
  exact ite_congr (propext (by rw [k.dc.c, h.ct ho])) (fun _ => k.k) (fun _ => k.kb)

theorem DEnd.hin (W : DcWf L) {σ s : State} (hp : (decapsK L).pre σ) (h : DEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.dc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the key. -/
theorem post_of (W : DcWf L) {σ s : State} (h : DEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (decapsK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.dc.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := aHat (Enc.rhoE L (dcEk L σ)))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, h.key ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

theorem decrypt_ok {A : Arith} (hA : ArithOk A) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {σ : State}
    (hp : (decapsK L).pre σ) {s : State} (h : DC L σ s) (h15 : s.gpr .r15 = 1) : WP isa (decrypt L A) s (DM L σ) := by
  unfold decrypt
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR L k 0 σ) L.k 0 (fun k _ hk s hs => u_ok hA W K hp (by omega) hs) s
    (DR.zero h h15)) fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR L L.k k σ) L.k 0 (fun k _ hk s hs => s_ok W hp (by omega) hs) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  exact tail_ok hA W K hp h₂

end Decaps

open Decaps in
theorem kemDecaps_correct (v : Sample4Impl) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd)
    (hctl : ctlOk (kemDecaps L v.callee) = true) (σ : State) (hp : (decapsK L).pre σ) :
    ∃ t s', Exec isa (kemDecaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (decapsK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (decrypt_ok v.arith W K hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashes_ok W hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc.encrypt_ok v K W.k (C := dcX W σ) W.enc h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (select_okD W h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.dc.top (h₅.hin W hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (decapsK L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

theorem rho_pub {σ₁ σ₂ : State} (pub : (decapsK L).pub σ₁ σ₂) : Enc.rhoE L (dcEk L σ₁) = Enc.rhoE L (dcEk L σ₂) := by
  rw [Enc.rhoE, Enc.rhoE, KPke.ekRho_dkEk, KPke.ekRho_dkEk]; exact pub.2.2.2.2.2

theorem decrypt_tr {A : Arith} (hA : ArithOk A) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L fun σ s => DC L σ s ∧ s.gpr .r15 = 1) (decrypt L A) fun _ _ => True := by
  unfold decrypt
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun k => R L (DR L k 0)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => u_ok hA W K hp (by omega) hs) (u_tr hA W K (by omega)))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, DR.zero h₁.1 h₁.2, DR.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => R L (DR L L.k k)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => s_ok W hp (by omega) hs) (s_tr W (by omega))) ?_
  rw [Nat.zero_add]
  exact tail_tr hA W K

theorem hashes_trL (W : DcWf L) : RelCT isa (LRel (dcR L) (dcW L)) (hashes L) fun _ _ => True := by
  unfold hashes
  exact RelCT.seq (LRel.step (dcB_bases L) (hash_tr (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)])
      (rate := 72) (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72) (out := sc oG)
        (len := 64) W.h₁ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr (dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136) (out := sc oKB)
      (len := 32) W.h₂ (show 0x1f < 256 by decide))

theorem hashes_tr (W : DcWf L) : RelCT isa (R L (DM L)) (hashes L) fun _ _ => True :=
  rel2_of (hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

theorem EIn.any {W : DcWf L} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State}
    (h : Enc.EIn L (dcX W σ) E ek m r s) : Enc.EIn L (dcXA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (EncI W)) (encrypt L v.callee (.rbp, 384 * L.k)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR L) (dcW L) x y ∧
      Enc.EIρ L (dcXA W) (.rbp, 384 * L.k) ρ x ∧ Enc.EIρ L (dcXA W) (.rbp, 384 * L.k) ρ y) (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := dcXA W) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (dcXA W) (.rbp, 384 * L.k) (Enc.rhoE L (dcEk L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (dcXA W) (.rbp, 384 * L.k) (Enc.rhoE L (dcEk L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (dcEk L σ₁), dc_lrel W p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc, i₁, i₂⟩

theorem select_tr (W : DcWf L) : RelCT isa (R L (EncO W)) (select L) fun _ _ => True := by
  obtain ⟨_, selT⟩ := W.selT
  exact rel2_of (Q := LRel (dcR L) (dcW L)) (taintRel [.rbx, .r12, .r14] (fun _ _ h =>
    fa3 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1)
      (h.eq (p := (.r14, 0)) (l := 1) W.inBs.2.2)) selT)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.out.2.dc h₂.out.2.dc

theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

theorem epi_tr : RelCT isa (R L (DEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.dc.top.regs (.rbx, .rcx) (by decide), h₂.dc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end Decaps

open Decaps in
theorem kemDecaps_ct (v : Sample4Impl) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    ConstantTime isa (decapsK L).pre (decapsK L).pub (kemDecaps L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecaps
  refine RelCT.seq (relInv (I' := fun σ s => DC L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM L) (fun σ s hp hs => decrypt_ok v.arith W K hp hs.1 hs.2)
    (decrypt_tr v.arith W K)) ?_
  refine RelCT.seq (relInv (I' := EncI W) (fun σ s hp hs => hashes_ok W hp hs) (hashes_tr W)) ?_
  refine RelCT.seq (relInv (I' := EncO W) (fun σ s _ hs => Enc.encrypt_ok v K W.k (C := dcX W σ) W.enc hs.1 hs.2)
    (encrypt_tr v W K)) ?_
  refine RelCT.seq (relInv (I' := DEnd L) (fun σ s _ hs => select_okD W hs) (select_tr W)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
