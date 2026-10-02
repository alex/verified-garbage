import VerifiedGarbage.Proof.MlKem1024.X86_64.DcDec

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps`

After K-PKE.Decrypt (`DcDec.lean`): `G(m' ‖ h)` and `J(z ‖ c)` (`hashes_ok`),
K-PKE.Encrypt in the context `dcX` (which keeps `K'` and `K̄`), and the choice
of the key (`select_okD`). The function returns 1 with
`ML-KEM.Decaps_internal(dk, c)` in `key` if every `SampleNTT` succeeded within
280 iterations (`allOk4`), and 0 otherwise (`decaps1024_correct`); it leaks
only the pointers and `ρ` (`decaps1024_ct`); so it meets the shared contract
(`decaps1024_verified`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps4

open VG.Impl.MlKem1024.X86_64.Decaps1024

/-- `m'`, `(K', r') = G(m' ‖ h)`, `K̄ = J(z ‖ c)` and the encryption key of `σ`. -/
abbrev dcM' (σ : State) : List Byte := decM1024 (dcDk σ) (dcC σ)
abbrev dcG (σ : State) : List Byte × List Byte := G (dcM' σ ++ dkH1024 (dcDk σ))
abbrev dcKb (σ : State) : List Byte := J (dkZ1024 (dcDk σ) ++ dcC σ)
abbrev dcEk (σ : State) : List Byte := dkEk1024 (dcDk σ)

/-- What `K-PKE.Encrypt` keeps: `DC`, `K'` at `G` and `K̄` at `KB`. -/
structure DCK (σ s : State) : Prop where
  dc : DC σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcG σ).1
  kb : bytesAt s.mem (pa s (sc oKB)) 32 = dcKb σ

def dckChk (ws : List (Ptr × Nat)) : Bool := dcChk ws && keepB dcB ws (sc oG) 32 && keepB dcB ws (sc oKB) 32

theorem DCK.step {σ : State} (hp : decaps1024K.pre σ) {s s' : State} (h : DCK σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : dckChk ws = true) : DCK σ s' := by
  simp only [dckChk, Bool.and_eq_true] at hc
  have L := h.dc.lay hp
  exact ⟨h.dc.step hp hP hc.1.1, by rw [L.keepBytes hP hc.1.2]; exact h.k, by rw [L.keepBytes hP hc.2]; exact h.kb⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def dcX (σ : State) : Ctx dcR dcW where
  Out s := decaps1024K.pre σ ∧ DCK σ s
  chk := dckChk
  bs := dcB_bases
  lay h := h.2.dc.lay h.1
  step h hP hc := ⟨h.1, h.2.step h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def dcXA : Ctx dcR dcW where
  Out s := ∃ σ, decaps1024K.pre σ ∧ DCK σ s
  chk := dckChk
  bs := dcB_bases
  lay := fun ⟨_, hp, h⟩ => h.dc.lay hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step hp hP hc⟩

theorem dcEncChk : Enc4.encChk (dcR ++ dcW) dcW dckChk (.rbp, 1536) = true := by decide

/-! ## `G(m' ‖ h)` and `J(z ‖ c)` -/

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI (σ s : State) : Prop := Enc4.EIn (dcX σ) (.rbp, 1536) (dcEk σ) (dcM' σ) (dcG σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {σ : State} (hp : decaps1024K.pre σ) {s : State} (h : DM σ s) : WP isa hashes s (EncI σ) := by
  have L := h.dc.lay hp
  unfold hashes
  -- `G(m' ‖ h)`.
  refine WP.seq (WP.mono (hash_ok dcB_bases (ps := [(sc oM, 32), ((.rbp, 3104), 32)]) (rate := 72) (out := sc oG)
    (len := 64) (by decide) (show 6 < 256 by decide) L) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.dc.step hp hP₁.b (by decide)
  have L₁ := k₁.lay hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    Decaps.slice_of h.dc.dk (show 3104 + 32 ≤ 3168 by decide), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  -- `J(z ‖ c)`.
  refine WP.mono (hash_ok dcB_bases (ps := [((.rbp, 3136), 32), ((.r14, 0), 1568)]) (rate := 136) (out := sc oKB)
    (len := 32) (by decide) (show 0x1f < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step hp hP₂.b (by decide)
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.c,
    Decaps.slice_of k₁.dk (show 3136 + 32 ≤ 3168 by decide), Decaps.shakeSuffix31] at hb₂
  rw [← J_eq, ← hP₂.pa rbx_cs] at hb₂
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (dcM' σ ++ dkH1024 (dcDk σ)) := by
    rw [L₁.keepBytes hP₂.b (by decide)]; exact hb₁
  have hK : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = (dcG σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hr : bytesAt s₂.mem (pa s₂ sigP) 32 = (dcG σ).2 := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨⟨hp, k₂, hK, hb₂⟩, Decaps.slice_of k₂.dk (show 1536 + 1568 ≤ 3168 by decide), ?_, hr⟩, ?_⟩
  · rw [L₁.keepBytes hP₂.b (by decide), L.keepBytes hP₁.b (by decide)]; exact h.m
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]

/-! ## The key -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := Enc4.EOut (dcX σ) (.rbp, 1536) (dcEk σ) (dcM' σ) (dcG σ).2 s

/-- At the end: `r15` as `allOk4`, and the key if it is 1. -/
structure DEnd (σ s : State) : Prop where
  dc : DC σ s
  r15 : s.gpr .r15 = if allOk4 (Enc4.rhoE (dcEk σ)) 16 then 1 else 0
  key : allOk4 (Enc4.rhoE (dcEk σ)) 16 → bytesAt s.mem (pa s (.r12, 0)) 32 =
    if dcC σ = ct1024 (aHat (Enc4.rhoE (dcEk σ))) (dcEk σ) (dcM' σ) (dcG σ).2 then (dcG σ).1 else dcKb σ

theorem select_okD {σ : State} {s : State} (h : EncO σ s) : WP isa Decaps1024.select s (DEnd σ) := by
  have hp := h.out.1
  have k := h.out.2
  have L := k.dc.lay hp
  have cR : ∀ {p : Ptr} {l : Nat}, inB dcB p l = true → InRegions (s.rd ++ s.wr) (pa s p) l := fun hi =>
    L.cR hi _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (select4_ok (cR (p := (.r14, 0)) (l := 1568) (by decide)) (cR (p := sc oCT4) (l := 1568) (by decide))
    (cR (p := sc oG) (l := 32) (by decide)) (cR (p := sc oKB) (l := 32) (by decide))
    (L.cW (show inB dcW (.r12, 0) 32 = true by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (L.disj (show sepB dcB (sc oG) 32 (.r12, 0) 32 = true by decide))
    (L.disj (show sepB dcB (sc oKB) 32 (.r12, 0) 32 = true by decide))) fun s' ⟨hP, hb⟩ => ?_
  refine ⟨k.dc.step hp hP.b (by decide), by rw [hP.cs .r15 (by decide)]; exact h.r15, fun ho => ?_⟩
  rw [hP.pa KeyGen.r12_cs, hb]
  exact ite_congr (propext (by rw [k.dc.c, h.ct ho])) (fun _ => k.k) (fun _ => k.kb)

theorem DEnd.hin {σ s : State} (hp : decaps1024K.pre σ) (h : DEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk => by
  have hk' : ∀ k < 6, inB dcB (sc (oSV + 8 * k)) 8 = true := by decide
  exact (h.dc.lay hp).cR (hk' k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the key. -/
theorem post_of {σ s : State} (h : DEnd σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : decaps1024K.post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.dc.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk4 (Enc4.rhoE (dcEk σ)) 16
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show decapsInternal mlKem1024 minIterations _ _ = _
    rw [decapsInternal1024, kpkeEncrypt1024_some (a := aHat (Enc4.rhoE (dcEk σ))) fun i hi j hj => aHat4_eq ho hi hj,
      Option.map_some, hm, ← e12, h.key ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk4 ho
    show decapsInternal mlKem1024 minIterations _ _ = _
    rw [decapsInternal1024, kpkeEncrypt1024_none hi hj hn]
    rfl

theorem decrypt_ok {A : Arith} (hA : ArithOk A) {σ : State} (hp : decaps1024K.pre σ) {s : State} (h : DC σ s) (h15 : s.gpr .r15 = 1) :
    WP isa (decrypt A) s (DM σ) := by
  unfold decrypt
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR k 0 σ) 4 0 (fun k _ hk s hs => u_ok hA hp (by omega) hs) s
    (DR.zero h h15)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR 4 k σ) 4 0 (fun k _ hk s hs => s_ok hp (by omega) hs) s₁ h₁)
    fun s₂ h₂ => ?_)
  exact tail_ok hA hp h₂

end Decaps4

open Decaps4 in
theorem decaps1024_correct (v : Sample4Impl) (σ : State) (hp : decaps1024K.pre σ) :
    ∃ t s', Exec isa (decaps1024 v.callee) σ t s' ∧ abiPreserved σ s' ∧ decaps1024K.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (decrypt_ok v.arith hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashes_ok hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc4.encrypt_ok v (C := dcX σ) dcEncChk h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (select_okD h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.dc.top (h₅.hin hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of h₅ hr hm⟩ : gprPreserved σ s₆ ∧ decaps1024K.post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl (by s4_ctl v) he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Decaps4

open VG.Impl.MlKem1024.X86_64.Decaps1024

theorem rho_pub {σ₁ σ₂ : State} (pub : decaps1024K.pub σ₁ σ₂) : Enc4.rhoE (dcEk σ₁) = Enc4.rhoE (dcEk σ₂) := by
  rw [Enc4.rhoE, Enc4.rhoE, KPke.ekRho_dkEk, KPke.ekRho_dkEk]; exact pub.2.2.2.2.2

theorem decrypt_tr {A : Arith} (hA : ArithOk A) : RelCT isa (R fun σ s => DC σ s ∧ s.gpr .r15 = 1) (decrypt A) fun _ _ => True := by
  unfold decrypt
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun k => R (DR k 0)) 4 0
    fun k _ hk => relInv (fun σ s hp hs => u_ok hA hp (by omega) hs) (u_tr hA (by omega)))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, DR.zero h₁.1 h₁.2, DR.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (seqR_tr (R := fun k => R (DR 4 k)) 4 0
    fun k _ hk => relInv (fun σ s hp hs => s_ok hp (by omega) hs) (s_tr (by omega))) ?_
  exact tail_tr hA

theorem hashes_trL : RelCT isa (LRel dcR dcW) hashes fun _ _ => True := by
  unfold hashes
  exact RelCT.seq (LRel.step dcB_bases (hash_tr dcB_bases (ps := [(sc oM, 32), ((.rbp, 3104), 32)]) (rate := 72)
      (out := sc oG) (len := 64) (by decide) (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok dcB_bases (ps := [(sc oM, 32), ((.rbp, 3104), 32)]) (rate := 72) (out := sc oG) (len := 64)
        (by decide) (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr dcB_bases (ps := [((.rbp, 3136), 32), ((.r14, 0), 1568)]) (rate := 136) (out := sc oKB) (len := 32)
      (by decide) (show 0x1f < 256 by decide))

theorem hashes_tr : RelCT isa (R DM) hashes fun _ _ => True :=
  rel2_of hashes_trL fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel p₁ p₂ pub h₁.dc h₂.dc

theorem EIn.any {σ : State} {E : Ptr} {ek m r : List Byte} {s : State} (h : Enc4.EIn (dcX σ) E ek m r s) :
    Enc4.EIn dcXA E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem copyRho_taint : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 1536 + 1536) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 1536 + 1536) 32))).isSome = true := by
  taint_decide

theorem encrypt_tr (v : Sample4Impl) : RelCT isa (R EncI) (encrypt1024 v.callee (.rbp, 1536)) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel dcR dcW x y ∧ Enc4.EIρ dcXA (.rbp, 1536) ρ x ∧
      Enc4.EIρ dcXA (.rbp, 1536) ρ y) (Q := fun _ _ => True) fun ρ =>
      RelCT.mono (Enc4.encrypt_tr v (C := dcXA) dcEncChk copyRho_taint (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc4.EIρ dcXA (.rbp, 1536) (Enc4.rhoE (dcEk σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc4.EIρ dcXA (.rbp, 1536) (Enc4.rhoE (dcEk σ₁)) y := ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc4.rhoE (dcEk σ₁), dc_lrel p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc, i₁, i₂⟩

theorem select_tr : RelCT isa (R EncO) Decaps1024.select fun _ _ => True :=
  rel2_of (Q := LRel dcR dcW) (taintRel [.rbx, .r12, .r14] (fun x y h =>
    fa3 (h.eq (p := sc 0) (l := 1) (by decide)) (h.eq (p := (.r12, 0)) (l := 1) (by decide))
      (h.eq (p := (.r14, 0)) (l := 1) (by decide))) (by taint_decide))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel p₁ p₂ pub h₁.out.2.dc h₂.out.2.dc

theorem pro_tr : RelCT isa (R fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

theorem epi_tr : RelCT isa (R DEnd) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.dc.top.regs (.rbx, .rcx) (by decide), h₂.dc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end Decaps4

open Decaps4 in
theorem decaps1024_ct (v : Sample4Impl) :
    ConstantTime isa decaps1024K.pre decaps1024K.pub (decaps1024 v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold decaps1024
  refine RelCT.seq (relInv (I' := fun σ s => DC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM) (fun σ s hp hs => decrypt_ok v.arith hp hs.1 hs.2) (decrypt_tr v.arith)) ?_
  refine RelCT.seq (relInv (I' := EncI) (fun σ s hp hs => hashes_ok hp hs) hashes_tr) ?_
  refine RelCT.seq (relInv (I' := EncO) (fun σ s _ hs => Enc4.encrypt_ok v (C := dcX σ) dcEncChk hs.1 hs.2)
    (encrypt_tr v)) ?_
  refine RelCT.seq (relInv (I' := DEnd) (fun σ s _ hs => select_okD hs) select_tr) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

/-- A state satisfying `decapsContract`'s precondition. -/
def decaps1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 3168⟩, ⟨0x2000, 1568⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 49152⟩]

theorem decaps1024_verified (v : Sample4Impl) :
    Verified X86_64.target (decaps1024 v.callee) (Spec.MlKem1024.decapsContract X86_64.abi 32) :=
  Verified.of_correct (decaps1024_correct v) (decaps1024_ct v)
    { pre := by sig_implies_pre [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decaps1024K, X86_64.abi,
        VG.X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decaps1024K, X86_64.abi,
        VG.X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decaps1024K, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem1024.decapsContract, Spec.MlKem1024.decapsSig, decaps1024K, X86_64.abi,
        VG.X86_64.argRegs] [decaps1024Sat] using decaps1024Sat }

end VG.Proof.MlKem1024.X86_64
