import VerifiedGarbage.Proof.MlKem1024.X86_64.DcBase

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps`, K-PKE.Decrypt

Untrusted: everything here is checked by Lean. `NTT(u'[i])` (`u_ok`),
`ŝ[i]` (`s_ok`), and `m' = ByteEncode₁(Compress₁(v' - NTT⁻¹(ŝ ∘ û)))` to
`M` (`tail_ok`): `m' = K-PKE.Decrypt(dk_PKE, c)`. Between the steps,
`DR nu ns`: the first `nu` of `û` and `ns` of `ŝ` are done. Each with its
constant time.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps4

open VG.Impl.MlKem1024.X86_64.Decaps1024

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 decaps1024K.pre decaps1024K.pub I

theorem dc_lrel {σ₁ σ₂ x y : State} (p₁ : decaps1024K.pre σ₁) (p₂ : decaps1024K.pre σ₂) (pub : decaps1024K.pub σ₁ σ₂)
    (h₁ : DC σ₁ x) (h₂ : DC σ₂ y) : LRel dcR dcW x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay p₁, h₂.lay p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r14, .rsi) (by decide), h₂.top.regs (.r14, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]

/-- The steps of K-PKE.Decrypt. -/
structure DR (nu ns : Nat) (σ s : State) : Prop where
  dc : DC σ s
  r15 : s.gpr .r15 = 1
  u : ∀ i < nu, PolyIs s.mem (pa s (pS i)) (ntt (dcU1024 (dcC σ) i))
  sh : ∀ i < ns, PolyIs s.mem (pa s (pS (4 + i))) (dcS (dkPke1024 (dcDk σ)) i)

/-- A piece that writes `ws` keeps `DR nu ns`. -/
def drChk (nu ns : Nat) (ws : List (Ptr × Nat)) : Bool :=
  dcChk ws && (List.range nu).all (fun i => keepB dcB ws (pS i) 1024) &&
    (List.range ns).all (fun i => keepB dcB ws (pS (4 + i)) 1024)

theorem DR.keep {σ : State} (hp : decaps1024K.pre σ) {nu ns : Nat} {s s' : State} (h : DR nu ns σ s)
    {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : drChk nu ns ws = true) : DR nu ns σ s' := by
  simp only [drChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hdc, kU⟩, kS⟩ := hc
  have L := h.dc.lay hp
  exact ⟨h.dc.step hp hP.b hdc, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun i hi => L.keepPoly hP.b (kU i hi) (h.u i hi), fun i hi => L.keepPoly hP.b (kS i hi) (h.sh i hi)⟩

theorem DR.zero {σ s : State} (h : DC σ s) (h15 : s.gpr .r15 = 1) : DR 0 0 σ s :=
  ⟨h, h15, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-! ## `û` -/

def uChk (i : Nat) : Bool :=
  twoChk dcB dcW (.r14, 352 * i) (32 * 11) (pS i) 1024 && ipChk dcB dcW (pS i) && drChk i 0 (Decaps.uW i)

theorem uChk_all : ∀ i < 4, uChk i = true := by decide +kernel

theorem u_ok {σ : State} (hp : decaps1024K.pre σ) {i : Nat} (hi : i < 4) {s : State} (h : DR i 0 σ s) :
    WP isa (uHat i) s (DR (i + 1) 0 σ) := by
  have hc := uChk_all i hi
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hdd, hic⟩, hrc⟩ := hc
  have L := h.dc.lay hp
  unfold uHat
  refine WP.seq (WP.mono (dd4At_okL L (d := 11) rbx_na hdd (by decide)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b dcB_bases
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hk := h.keep hp (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hrc
  refine ⟨hk.dc, hk.r15, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.u k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs, Decaps.slice_of h.dc.c (show 352 * k + 32 * 11 ≤ 1568 by omega)] at hp₂
    exact hp₂

theorem u_tr {i : Nat} (hi : i < 4) : RelCT isa (R (DR i 0)) (uHat i) fun _ _ => True := by
  have hc := uChk_all i hi
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hdd, hic⟩, _⟩ := hc
  unfold uHat
  exact rel2_of (Q := fun x y => LRel dcR dcW x y ∧ True ∧ True) (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS i)))
    dcB_bases (RelCT.mono (dd4At_trL (d := 11) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
    (fun x Lx _ => WP.mono (dd4At_okL Lx (d := 11) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
      ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hic))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨dc_lrel p₁ p₂ pub h₁.dc h₂.dc, trivial, trivial⟩

/-! ## `ŝ` -/

def sChk (i : Nat) : Bool :=
  twoChk dcB dcW (.rbp, 384 * i) 384 (pS (4 + i)) 1024 && drChk 4 i [(pS (4 + i), 1024)]

theorem sChk_all : ∀ i < 4, sChk i = true := by decide +kernel

theorem s_ok {σ : State} (hp : decaps1024K.pre σ) {i : Nat} (hi : i < 4) {s : State} (h : DR 4 i σ s) :
    WP isa (sHat i) s (DR 4 (i + 1) σ) := by
  have hc := sChk_all i hi
  simp only [sChk, Bool.and_eq_true] at hc
  have L := h.dc.lay hp
  refine WP.mono (dec12At_okL L rbx_na hc.1) fun s' ⟨hP, hq⟩ => ?_
  have hk := h.keep hp hP hc.2
  refine ⟨hk.dc, hk.r15, hk.u, fun k hk' => ?_⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.sh k hk'
  · rw [hP.pa rbx_cs]
    rw [Decaps.slice_of h.dc.dk (show 384 * k + 384 ≤ 3168 by omega)] at hq
    rw [dcS, dkPke1024, slice_take _ (show 384 * k + 384 ≤ 1536 by omega)]
    exact hq

theorem s_tr {i : Nat} (hi : i < 4) : RelCT isa (R (DR 4 i)) (sHat i) fun _ _ => True := by
  have hc := sChk_all i hi
  simp only [sChk, Bool.and_eq_true] at hc
  exact rel2_of (dec12At_trL rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel p₁ p₂ pub h₁.dc h₂.dc

/-! ## `m'` -/

/-- After K-PKE.Decrypt: `m'` at `M`. -/
structure DM (σ s : State) : Prop where
  dc : DC σ s
  r15 : s.gpr .r15 = 1
  m : bytesAt s.mem (pa s (sc oM)) 32 = decM1024 (dcDk σ) (dcC σ)

abbrev tailW : List (Ptr × Nat) := dot4W ++ [(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024)] ++
  [(pS 16, 1024)] ++ [(sc oM, 32 * 1)]

def tailChk : Bool :=
  dot4Chk dcB dcW (fun j => pS (4 + j)) pS && ipChk dcB dcW (pS 15) &&
    twoChk dcB dcW (.r14, 1408) (32 * 5) (pS 16) 1024 && keepB dcB [(pS 16, 1024)] (pS 15) 1024 &&
    accChk dcB dcW (pS 16) (pS 15) && twoChk dcB dcW (pS 16) 1024 (sc oM) (32 * 1) && dcChk tailW

theorem tailChk_true : tailChk = true := by decide +kernel

/-- The rest of `decrypt`. -/
abbrev tail : Prog isa :=
  .seq (dot4At (fun j => pS (4 + j)) pS) (.seq (nttInvAt (pS 15)) (.seq (dd4At (.r14, 1408) 5 (pS 16))
    (.seq (subAt (pS 16) (pS 15)) (ceAt (pS 16) 1 (sc oM)))))

theorem tail_ok {σ : State} (hp : decaps1024K.pre σ) {s : State} (h : DR 4 4 σ s) : WP isa tail s (DM σ) := by
  have hc := tailChk_true
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdc, hic⟩, hdd⟩, hk15⟩, hac⟩, htw⟩, hkc⟩ := hc
  have L := h.dc.lay hp
  refine WP.seq (WP.mono (dot4At_ok L dcB_bases hdc (a := dcS (dkPke1024 (dcDk σ))) (b := fun i => ntt (dcU1024 (dcC σ) i))
    (fun k hk => h.sh k hk) (fun k hk => h.u k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b dcB_bases
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b dcB_bases
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (dd4At_okL L₂ (d := 5) rbx_na hdd (by decide)) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b dcB_bases
  have hc₃ : bytesAt s₂.mem (pa s₂ (.r14, 1408)) (32 * 5) = ((dcC σ).drop 1408).take (32 * 5) := by
    have k₂ := h.dc.step hp (PPost.app hP₁ hP₂ (by decide)).b
      (show dcChk (dot4W ++ [(pS 15, 1024), (sc oSS, 1024)]) = true by decide +kernel)
    exact Decaps.slice_of k₂.c (show 1408 + 32 * 5 ≤ 1568 by decide)
  rw [hc₃, ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (subAt_ok L₃ rbx_na hac hp₃.1 hq₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b dcB_bases
  rw [hp₃.2, hq₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceAt_okL L₄ (d := 1) rbx_na htw (by decide) hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅
    (by decide)
  refine ⟨h.dc.step hp hP.b hkc, ?_, ?_⟩
  · rw [hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h.r15]
  · rw [hP₅.pa rbx_cs, hb₅, hp₄.2, decM1024, kpkeDecrypt1024]
    rfl

theorem tail_tr : RelCT isa (R (DR 4 4)) tail fun _ _ => True := by
  have hc := tailChk_true
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdc, hic⟩, hdd⟩, hk15⟩, hac⟩, htw⟩, _⟩ := hc
  refine rel2_of (Q := fun x y => LRel dcR dcW x y ∧ DotIn4 (fun j => pS (4 + j)) pS x ∧
      DotIn4 (fun j => pS (4 + j)) pS y) (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) dcB_bases
    (RelCT.mono (dot4At_tr dcB_bases hdc) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dot4At_ok Lx dcB_bases hdc (a := fun k => polyAt x.mem (pa x (pS (4 + k))))
      (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) dcB_bases (nttInvAt_tr hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16)) ∧ Reduced x.mem (pa x (pS 15))) dcB_bases
      (RelCT.mono (dd4At_trL (d := 5) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (dd4At_okL Lx (d := 5) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk15 hx⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16))) dcB_bases (subAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (subAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceAt_trL (d := 1) rbx_na htw (by decide))))))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨dc_lrel p₁ p₂ pub h₁.dc h₂.dc,
      fun k hk => ⟨(h₁.sh k hk).1, (h₁.u k hk).1⟩, fun k hk => ⟨(h₂.sh k hk).1, (h₂.u k hk).1⟩⟩

end Decaps4

end VG.Proof.MlKem1024.X86_64
