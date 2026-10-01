import VerifiedGarbage.Proof.MlKem.X86_64.DcBase

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_decaps`, K-PKE.Decrypt

Untrusted: everything here is checked by Lean. `NTT(u'[i])` (`u_ok`),
`ŝ[i]` (`s_ok`), and `m' = ByteEncode₁(Compress₁(v' - NTT⁻¹(ŝ ∘ û)))` to
`M` (`tail_ok`): `m' = K-PKE.Decrypt(dk_PKE, c)`. Between the steps,
`DR nu ns`: the first `nu` of `û` and `ns` of `ŝ` are done. Each with its
constant time. The functions that decrypt (`vg_mlkem768_decaps` and
`vg_mlkem768_decaps_expanded`) do so in the layout `dcR`/`dcW`, each keeping
what it holds of its state (`DCtx`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

abbrev uW (i : Nat) : List (Ptr × Nat) := [(pS i, 1024)] ++ [(pS i, 1024), (sc oSS, 1024)]

abbrev tailW : List (Ptr × Nat) := KeyGen.dotW ++ [(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024)] ++
  [(pS 16, 1024)] ++ [(sc oM, 32 * 1)]

/-- What the pieces of `decrypt` write. -/
abbrev decWs : List (List (Ptr × Nat)) :=
  [uW 0, uW 1, uW 2, [(pS 3, 1024)], [(pS 4, 1024)], [(pS 5, 1024)],
    KeyGen.dotW ++ [(pS 15, 1024), (sc oSS, 1024)], tailW]

/-- What a function holds of its state while it decrypts, in a run from `σ`
(`Out σ`, kept by the pieces whose writes pass `chk`, which those of
`decrypt` do), in the layout `dcR`/`dcW`: `dk σ` and `c σ` at `rbp` and
`r14`. `Pre` and `Pub` are its contract's precondition and public data, in
two runs of which the pointers are the same (`lrel`). -/
structure DCtx where
  Pre : State → Prop
  Pub : State → State → Prop
  Out : State → State → Prop
  chk : List (Ptr × Nat) → Bool
  dk : State → List Byte
  c : State → List Byte
  lay : ∀ {σ s : State}, Pre σ → Out σ s → Lay dcR dcW s
  step : ∀ {σ s s' : State} {ws : List (Ptr × Nat)}, Pre σ → Out σ s → PPostB s s' ws → chk ws = true → Out σ s'
  dkAt : ∀ {σ s : State}, Out σ s → bytesAt s.mem (pa s (.rbp, 0)) 2400 = dk σ
  cAt : ∀ {σ s : State}, Out σ s → bytesAt s.mem (pa s (.r14, 0)) 1088 = c σ
  lrel : ∀ {σ₁ σ₂ x y : State}, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → Out σ₁ x → Out σ₂ y → LRel dcR dcW x y
  chks : decWs.all chk = true

variable (D : DCtx)

theorem DCtx.ok {w : List (Ptr × Nat)} (hw : w ∈ decWs) : D.chk w = true := List.all_eq_true.mp D.chks w hw

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 D.Pre D.Pub I

/-- The steps of K-PKE.Decrypt. -/
structure DR (nu ns : Nat) (σ s : State) : Prop where
  out : D.Out σ s
  r15 : s.gpr .r15 = 1
  u : ∀ i < nu, PolyIs s.mem (pa s (pS i)) (ntt (dcU (D.c σ) i))
  sh : ∀ i < ns, PolyIs s.mem (pa s (pS (3 + i))) (dcS (dkPke (D.dk σ)) i)

/-- A piece that writes `ws` keeps the polynomials of `DR nu ns`. -/
def drKeep (nu ns : Nat) (ws : List (Ptr × Nat)) : Bool :=
  (List.range nu).all (fun i => keepB dcB ws (pS i) 1024) &&
    (List.range ns).all (fun i => keepB dcB ws (pS (3 + i)) 1024)

variable {D}

theorem DR.keep {σ : State} (hp : D.Pre σ) {nu ns : Nat} {s s' : State} (h : DR D nu ns σ s)
    {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : D.chk ws = true) (hk : drKeep nu ns ws = true) :
    DR D nu ns σ s' := by
  simp only [drKeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  obtain ⟨kU, kS⟩ := hk
  have L := D.lay hp h.out
  exact ⟨D.step hp h.out hP.b hc, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun i hi => L.keepPoly hP.b (kU i hi) (h.u i hi), fun i hi => L.keepPoly hP.b (kS i hi) (h.sh i hi)⟩

theorem DR.zero {σ s : State} (h : D.Out σ s) (h15 : s.gpr .r15 = 1) : DR D 0 0 σ s :=
  ⟨h, h15, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-! ## `û` -/

def uChk (i : Nat) : Bool :=
  twoChk dcB dcW (.r14, 320 * i) (32 * 10) (pS i) 1024 && ipChk dcB dcW (pS i) && drKeep i 0 (uW i)

theorem uChk_all : ∀ i < 3, uChk i = true := by decide

theorem uW_mem {i : Nat} (hi : i < 3) : uW i ∈ decWs := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide

theorem u_ok {σ : State} (hp : D.Pre σ) {i : Nat} (hi : i < 3) {s : State} (h : DR D i 0 σ s) :
    WP isa (uHat i) s (DR D (i + 1) 0 σ) := by
  have hc := uChk_all i hi
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hdd, hic⟩, hrc⟩ := hc
  have L := D.lay hp h.out
  unfold uHat
  refine WP.seq (WP.mono (ddAt_okL L (d := 10) rbx_na hdd (by decide)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b dcB_bases
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hk := h.keep hp (PPost.app hP₁ hP₂ (by simp [calleeSaved])) (D.ok (uW_mem hi)) hrc
  refine ⟨hk.out, hk.r15, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.u k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs, slice_of (D.cAt h.out) (show 320 * k + 32 * 10 ≤ 1088 by omega)] at hp₂
    exact hp₂

theorem u_tr {i : Nat} (hi : i < 3) : RelCT isa (R D (DR D i 0)) (uHat i) fun _ _ => True := by
  have hc := uChk_all i hi
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hdd, hic⟩, _⟩ := hc
  unfold uHat
  exact rel2_of (Q := fun x y => LRel dcR dcW x y ∧ True ∧ True) (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS i)))
    dcB_bases (RelCT.mono (ddAt_trL (d := 10) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
    (fun x Lx _ => WP.mono (ddAt_okL Lx (d := 10) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
      ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hic))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨D.lrel p₁ p₂ pub h₁.out h₂.out, trivial, trivial⟩

/-! ## `ŝ` -/

def sChk (i : Nat) : Bool :=
  twoChk dcB dcW (.rbp, 384 * i) 384 (pS (3 + i)) 1024 && drKeep 3 i [(pS (3 + i), 1024)]

theorem sChk_all : ∀ i < 3, sChk i = true := by decide

theorem sW_mem {i : Nat} (hi : i < 3) : [(pS (3 + i), 1024)] ∈ decWs := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide

theorem s_ok {σ : State} (hp : D.Pre σ) {i : Nat} (hi : i < 3) {s : State} (h : DR D 3 i σ s) :
    WP isa (sHat i) s (DR D 3 (i + 1) σ) := by
  have hc := sChk_all i hi
  simp only [sChk, Bool.and_eq_true] at hc
  have L := D.lay hp h.out
  refine WP.mono (dec12At_okL L rbx_na hc.1) fun s' ⟨hP, hq⟩ => ?_
  have hk := h.keep hp hP (D.ok (sW_mem hi)) hc.2
  refine ⟨hk.out, hk.r15, hk.u, fun k hk' => ?_⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.sh k hk'
  · rw [hP.pa rbx_cs]
    rw [slice_of (D.dkAt h.out) (show 384 * k + 384 ≤ 2400 by omega)] at hq
    rw [dcS, dkPke, slice_take _ (show 384 * k + 384 ≤ 1152 by omega)]
    exact hq

theorem s_tr {i : Nat} (hi : i < 3) : RelCT isa (R D (DR D 3 i)) (sHat i) fun _ _ => True := by
  have hc := sChk_all i hi
  simp only [sChk, Bool.and_eq_true] at hc
  exact rel2_of (dec12At_trL rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => D.lrel p₁ p₂ pub h₁.out h₂.out

/-! ## `m'` -/

/-- After K-PKE.Decrypt: `m'` at `M`. -/
structure DM (D : DCtx) (σ s : State) : Prop where
  out : D.Out σ s
  r15 : s.gpr .r15 = 1
  m : bytesAt s.mem (pa s (sc oM)) 32 = decM (D.dk σ) (D.c σ)

def tailChk : Bool :=
  dotChk dcB dcW (fun j => pS (3 + j)) pS && ipChk dcB dcW (pS 15) &&
    twoChk dcB dcW (.r14, 960) (32 * 4) (pS 16) 1024 && keepB dcB [(pS 16, 1024)] (pS 15) 1024 &&
    accChk dcB dcW (pS 16) (pS 15) && twoChk dcB dcW (pS 16) 1024 (sc oM) (32 * 1)

theorem tailChk_true : tailChk = true := by decide

/-- The rest of `decrypt`. -/
abbrev tail : Prog isa :=
  .seq (dotAt (fun j => pS (3 + j)) pS) (.seq (nttInvAt (pS 15)) (.seq (ddAt (.r14, 960) 4 (pS 16))
    (.seq (subAt (pS 16) (pS 15)) (ceAt (pS 16) 1 (sc oM)))))

theorem tail_ok {σ : State} (hp : D.Pre σ) {s : State} (h : DR D 3 3 σ s) : WP isa tail s (DM D σ) := by
  have hc := tailChk_true
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hdc, hic⟩, hdd⟩, hk15⟩, hac⟩, htw⟩ := hc
  have L := D.lay hp h.out
  refine WP.seq (WP.mono (dotAt_ok L dcB_bases hdc (a := dcS (dkPke (D.dk σ))) (b := fun i => ntt (dcU (D.c σ) i))
    (fun k hk => h.sh k hk) (fun k hk => h.u k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b dcB_bases
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b dcB_bases
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (ddAt_okL L₂ (d := 4) rbx_na hdd (by decide)) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b dcB_bases
  have hc₃ : bytesAt s₂.mem (pa s₂ (.r14, 960)) (32 * 4) = ((D.c σ).drop 960).take (32 * 4) := by
    have k₂ := D.step hp h.out (PPost.app hP₁ hP₂ (by decide)).b (D.ok (by decide))
    exact slice_of (D.cAt k₂) (show 960 + 32 * 4 ≤ 1088 by decide)
  rw [hc₃, ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (subAt_ok L₃ rbx_na hac hp₃.1 hq₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b dcB_bases
  rw [hp₃.2, hq₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceAt_okL L₄ (d := 1) rbx_na htw (by decide) hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅
    (by decide)
  refine ⟨D.step hp h.out hP.b (D.ok (by decide)), ?_, ?_⟩
  · rw [hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h.r15]
  · rw [hP₅.pa rbx_cs, hb₅, hp₄.2, decM, kpkeDecrypt768]
    rfl

theorem tail_tr : RelCT isa (R D (DR D 3 3)) tail fun _ _ => True := by
  have hc := tailChk_true
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hdc, hic⟩, hdd⟩, hk15⟩, hac⟩, htw⟩ := hc
  refine rel2_of (Q := fun x y => LRel dcR dcW x y ∧ DotIn (fun j => pS (3 + j)) pS x ∧
      DotIn (fun j => pS (3 + j)) pS y) (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) dcB_bases
    (RelCT.mono (dotAt_tr dcB_bases hdc) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotAt_ok Lx dcB_bases hdc (a := fun k => polyAt x.mem (pa x (pS (3 + k))))
      (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) dcB_bases (nttInvAt_tr hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16)) ∧ Reduced x.mem (pa x (pS 15))) dcB_bases
      (RelCT.mono (ddAt_trL (d := 4) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddAt_okL Lx (d := 4) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk15 hx⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16))) dcB_bases (subAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (subAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceAt_trL (d := 1) rbx_na htw (by decide))))))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨D.lrel p₁ p₂ pub h₁.out h₂.out,
      fun k hk => ⟨(h₁.sh k hk).1, (h₁.u k hk).1⟩, fun k hk => ⟨(h₂.sh k hk).1, (h₂.u k hk).1⟩⟩

end Decaps

end VG.Proof.MlKem.X86_64
