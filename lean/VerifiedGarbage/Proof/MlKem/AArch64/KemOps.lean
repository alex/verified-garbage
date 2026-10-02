import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon

/-!
# ML-KEM on AArch64: the building blocks of `encaps` and `decaps`

Each building block (`prfCbdWith keccak.callee`, `nttAt`, `nttInvAt`, `mulAt`,
`addAt`, `subAt`, `ceAt`, `ddAt`, `dec12At`, and `ceLAt` and `ddLAt` at the
widths `d_u` and `d_v`): what it needs, what it computes, what it keeps (`KB`,
`x24`), and the only memory it changes (`Frame`), so that the facts
established before it survive it. The functions at the widths `d_u` and `d_v`
are a parameter set's own (`KemLay.Calls`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay} {L : Layout}

/-- The functions of `P` at the widths `d_u` and `d_v` meet their contracts. -/
structure Calls (P : KemLay) : Prop where
  ce : ∀ {s : State} {f o : Addr} {d : Nat}, s.gpr .x0 = f → ((s.gpr .x1).setWidth 32).toNat = d →
    s.gpr .x2 = o → (s.gpr .x3).toNat = 32 * d → (d = P.du ∨ d = P.dv) →
    Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩ → Reduced s.mem f → Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr) →
    Covers [⟨o, 32 * d⟩] s.wr → ∀ {Q : State → Prop},
    (∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) → Q s') →
    WP isa (.call P.ceName P.ce) s Q
  dd : ∀ {s : State} {b f : Addr} {d : Nat}, s.gpr .x0 = b → (s.gpr .x1).toNat = 32 * d →
    ((s.gpr .x2).setWidth 32).toNat = d → s.gpr .x3 = f → (d = P.du ∨ d = P.dv) →
    Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩ → Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
    Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
    (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') →
    WP isa (.call P.ddName P.dd) s Q

/-- Buffer `o` of `scratch`. -/
abbrev sA (L : Layout) (s₀ : State) (o : Nat) : Addr := kA s₀ L.sc + BitVec.ofNat 64 o

/-- A polynomial buffer in `scratch`, past the NTT's working space and below the saved registers. -/
def PO (P : KemLay) (off : Nat) : Prop := AH ≤ off ∧ off + 1024 ≤ SV P

theorem PO.le {off : Nat} (h : PO P off) : off + 1024 ≤ SV P + 48 := by
  obtain ⟨-, h⟩ := h; omega

theorem PO.safe {s₀ : State} (hp : Pre P L s₀) {off : Nat} (h : PO P off) :
    Safe P L s₀ (R (kA s₀) L.sc off 1024) :=
  safe_scr hp h.2

theorem PO.ns {s₀ : State} (hp : Pre P L s₀) {off : Nat} (h : PO P off) :
    (R (kA s₀) L.sc off 1024).Disjoint (R (kA s₀) L.sc NS 1024) :=
  sdisj hp h.le (by kom) (.inr (by obtain ⟨h, -⟩ := h; kom))

theorem e28 {s₀ s : State} (hk : KB P L s₀ s) (o : Nat) :
    s.gpr .x28 + BitVec.ofNat 64 o = sA L s₀ o := by rw [hk.x28]

/-- What `(prfCbdWith keccak.callee)` writes. -/
abbrev pcW (L : Layout) (s₀ : State) (off : Nat) : List Region :=
  [R (kA s₀) L.sc ST 200, R (kA s₀) L.sc WK 640, below s₀.sp 16, R (kA s₀) L.sc (RB + 32) 1,
    R (kA s₀) L.sc PB 128, R (kA s₀) L.sc off 1024]

/-- `SamplePolyCBD₂(PRF₂(r, N))`, with `r` at `RB`. -/
theorem prfCbd_ok {s₀ : State} (hp : Pre P L s₀) {N off : Nat} (hN : N < 256) (ho : PO P off) {s : State}
    (hk : KB P L s₀ s) {rv : List Byte} (hr : bytesAt s.mem (sA L s₀ RB) 32 = rv) :
    WP isa ((prfCbdWith keccak.callee) N off) s fun s' => KB P L s₀ s' ∧ Frame (pcW L s₀ off) s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off) (cbd rv N) ∧ s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hsl : ∀ {o l : Nat}, o + l ≤ SV P + 48 → o + l ≤ L.len L.sc := hp.fs
  -- `N` after `r`
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_strb (a := sA L s₀ (RB + 32)) (by decide)
    (by rw [h₁.get .x28, e28 hk]) (by
      rw [h₁.wr]; exact in_R (cov_s hp hk (o := RB + 32) (l := 1) (by kom)) (k := 0) (by decide)
        (by decide)) fun s₂ h₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem.writeW (sA L s₀ (RB + 32)) ((s₁.gpr .x9).setWidth 8) := by
    rw [h₂.mem, h₁.mem]
  have f₂ : Frame [R (kA s₀) L.sc (RB + 32) 1] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (R.contains (k := 0) (by decide)
      (by decide))
  have kb₂ : KB P L s₀ s₂ := hk.frame (h₁.keep.trans h₂.keep) f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by kom)
  have msg : bytesAt s₂.mem (sA L s₀ RB) 33 = rv ++ [BitVec.ofNat 8 N] := by
    rw [show 33 = 32 + 1 from rfl, bytesAt_add, bytesAt_frame (p := sA L s₀ RB) (len := 32)
      f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact sdisj hp (by kom) (by kom) (by decide)) (by decide), hr]
    refine congrArg (rv ++ ·) (bytesAt_eq rfl fun k hk' => ?_)
    have : k = 0 := by omega
    subst this
    rw [ptr_zero, ptr_add, m₂, writeW8_apply, ite_eq_left rfl, e₁]
    exact sfx8 hN
  -- `PRF₂(r, N)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x28, RB, 33⟩]) (outs := [⟨.x28, PB, 128⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₂ (by decide) (hsl (by kom)) (.inr (by decide)) (by decide)
        (fun _ => hp.scw))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₂ (by decide) (hsl (by kom)) (.inr (by decide)) (by decide)
        (fun _ => hp.scw))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ : KB P L s₀ s₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, PB, 128, rfl, by decide, hp.scw, hsl (by kom), .inr (.inr (by kom))⟩
  have prf₃ : bytesAt s₃.mem (sA L s₀ PB) 128 = prf 2 rv (BitVec.ofNat 8 N) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂] at o
    rw [msg] at o
    rw [o, prf_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  -- `SamplePolyCBD₂`
  refine WP.seq (wp_ptrTo (by decide) (by decide) fun s₄ h₄ e₄ => wp_ptrTo' (by decide)
    (by obtain ⟨-, h⟩ := ho; kom) fun s₅ h₅ e₅ => ?_)
  have kb₅ := kb₃.block (h₄.trans h₅).keep (by rw [h₅.mem, h₄.mem]) (by decide)
  refine cbd2_call (b := sA L s₀ PB) (f := sA L s₀ off)
    (by rw [h₅.get .x0, e₄, e28 kb₃]) (by rw [e₅, h₄.get .x28, e28 kb₃])
    (sdisj hp (by kom) fo (.inl (by obtain ⟨h, -⟩ := ho; kom)))
    (covers_cons (cov_sr hp kb₅ (o := PB) (l := 128) (by kom)) (cov_sr hp kb₅ fo))
    (cov_s hp kb₅ fo) fun s₆ k₆ p₆ => ?_
  have kb₆ := kb₅.call k₆ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp
  rw [show s₅.mem = s₃.mem by rw [h₅.mem, h₄.mem], prf₃] at p₆
  have m₅ : s₅.mem = s₃.mem := by rw [h₅.mem, h₄.mem]
  have F₁ : Frame (pcW L s₀ off) s.mem s₂.mem := f₂.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₂ : Frame (pcW L s₀ off) s₂.mem s₃.mem := k₃'.frame.mono fun r hr => by
    rcases mem4 hr with rfl | rfl | rfl | rfl <;> simp
  have F₃ : Frame (pcW L s₀ off) s₅.mem s₆.mem := k₆.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  rw [m₅] at F₃
  refine ⟨kb₆, F₁.trans (F₂.trans F₃), p₆, ?_⟩
  rw [k₆.cs _ (by decide) (by decide), h₅.get .x24, h₄.get .x24, k₃.cs _ (by decide) (by decide), h₂.gpr,
    h₁.get .x24]

/-- The NTT, or its inverse, of the polynomial at `off`. -/
theorem inPlace_ok {s₀ : State} (hp : Pre P L s₀) {t : Poly → Poly} {c : Prog isa} {name : String}
    (hc : ∀ {s : State} {f w : Addr}, s.gpr .x0 = f → s.gpr .x1 = w → Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩ →
      Reduced s.mem f → Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (t (polyAt s.mem f)) → Q s') →
      WP isa (.call name c) s Q)
    {off : Nat} (ho : PO P off) {s : State} (hk : KB P L s₀ s) (hr : Reduced s.mem (sA L s₀ off)) :
    WP isa (.seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 NS)) (.call name c)) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024, R (kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off) (t (polyAt s.mem (sA L s₀ off))) ∧ s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  refine WP.seq (wp_ptrTo (by decide) (by obtain ⟨-, h⟩ := ho; kom) fun s₁ h₁ e₁ => wp_ptrTo'
    (by decide) (by decide) fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine hc (f := sA L s₀ off) (w := sA L s₀ NS) (by rw [h₂.get .x0, e₁, e28 hk])
    (by rw [e₂, h₁.get .x28, e28 hk]) (ho.ns hp) (by rw [m₂]; exact hr)
    (covers_cons (cov_s hp kb₂ fo) (cov_s hp kb₂ (o := NS) (l := 1024) (by kom))) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact ho.safe hp
      · exact safe_scr hp (by kom),
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem ntt_ok {s₀ : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off) {s : State} (hk : KB P L s₀ s)
    (hr : Reduced s.mem (sA L s₀ off)) :
    WP isa (nttAt off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024, R (kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off) (ntt (polyAt s.mem (sA L s₀ off))) ∧ s'.gpr .x24 = s.gpr .x24 :=
  inPlace_ok hp (fun h0 h1 hd hr hw => ntt_call h0 h1 hd hr hw) ho hk hr

theorem nttInv_ok {s₀ : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off) {s : State} (hk : KB P L s₀ s)
    (hr : Reduced s.mem (sA L s₀ off)) :
    WP isa (nttInvAt off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024, R (kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off) (nttInv (polyAt s.mem (sA L s₀ off))) ∧ s'.gpr .x24 = s.gpr .x24 :=
  inPlace_ok hp (fun h0 h1 hd hr hw => nttInv_call h0 h1 hd hr hw) ho hk hr

/-- `h ← f ×_T g`, for polynomials in `scratch`. -/
theorem mul_ok {s₀ : State} (hp : Pre P L s₀) {h f g : Nat} (hh : PO P h) (hf : PO P f) (hg : PO P g)
    (d₁ : h + 1024 ≤ f ∨ f + 1024 ≤ h) (d₂ : h + 1024 ≤ g ∨ g + 1024 ≤ h) {s : State} (hk : KB P L s₀ s)
    (rf : Reduced s.mem (sA L s₀ f)) (rg : Reduced s.mem (sA L s₀ g)) :
    WP isa (mulAt h f g) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc h 1024, R (kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ h) (multiplyNTTs (polyAt s.mem (sA L s₀ f)) (polyAt s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fh := hh.le
  have ff := hf.le
  have fg := hg.le
  rw [mulAt, List.append_assoc, List.append_assoc]
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo (by decide) (by kom)
    fun s₂ h₂ e₂ => wp_ptrTo (by decide) (by kom) fun s₃ h₃ e₃ => wp_ptrTo' (by decide) (by decide)
    fun s₄ h₄ e₄ => ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine mul_call (h := sA L s₀ h) (f := sA L s₀ f) (g := sA L s₀ g) (w := sA L s₀ NS)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, e28 hk])
    (by rw [h₄.get .x1, h₃.get .x1, e₂, h₁.get .x28, e28 hk])
    (by rw [h₄.get .x2, e₃, h₂.get .x28, h₁.get .x28, e28 hk])
    (by rw [e₄, h₃.get .x28, h₂.get .x28, h₁.get .x28, e28 hk])
    (sdisj hp fh ff d₁) (sdisj hp fh fg d₂) (hh.ns hp) (hf.ns hp) (hg.ns hp)
    (by rw [m₄]; exact rf) (by rw [m₄]; exact rg)
    (covers_cons (cov_sr hp kb₄ ff) (covers_cons (cov_sr hp kb₄ fg)
      (covers_cons (cov_sr hp kb₄ fh) (cov_sr hp kb₄ (o := NS) (l := 1024) (by kom)))))
    (covers_cons (cov_s hp kb₄ fh) (cov_s hp kb₄ (o := NS) (l := 1024) (by kom)))
    fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact hh.safe hp
      · exact safe_scr hp (by kom),
    by rw [← m₄]; exact k₅.frame, by rw [← m₄]; exact p₅,
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

/-- `f ← f + g` or `f ← f - g`, for polynomials in `scratch`. -/
theorem acc_ok {s₀ : State} (hp : Pre P L s₀) {op : Poly → Poly → Poly} {c : Prog isa} {name : String}
    (hc : ∀ {s : State} {f g : Addr}, s.gpr .x0 = f → s.gpr .x1 = g → Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩ →
      Reduced s.mem f → Reduced s.mem g → Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
      Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (op (polyAt s.mem f) (polyAt s.mem g)) → Q s') →
      WP isa (.call name c) s Q)
    {f g : Nat} (hf : PO P f) (hg : PO P g) (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : Reduced s.mem (sA L s₀ f)) (rg : Reduced s.mem (sA L s₀ g)) :
    WP isa (.seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call name c)) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ f) (op (polyAt s.mem (sA L s₀ f)) (polyAt s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg := hg.le
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine hc (f := sA L s₀ f) (g := sA L s₀ g) (by rw [h₂.get .x0, e₁, e28 hk]) (by rw [e₂, h₁.get .x28, e28 hk])
    (sdisj hp ff fg d) (by rw [m₂]; exact rf) (by rw [m₂]; exact rg)
    (covers_cons (cov_sr hp kb₂ fg) (cov_sr hp kb₂ ff)) (cov_s hp kb₂ ff) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by rw [List.mem_singleton.mp hr]; exact hf.safe hp,
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem add_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : Reduced s.mem (sA L s₀ f)) (rg : Reduced s.mem (sA L s₀ g)) :
    WP isa (addAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ f) (add (polyAt s.mem (sA L s₀ f)) (polyAt s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  acc_ok hp (fun h0 h1 hd rf rg hc hw => add_call h0 h1 hd rf rg hc hw) hf hg d hk rf rg

theorem sub_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : Reduced s.mem (sA L s₀ f)) (rg : Reduced s.mem (sA L s₀ g)) :
    WP isa (subAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ f) (sub (polyAt s.mem (sA L s₀ f)) (polyAt s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  acc_ok hp (fun h0 h1 hd rf rg hc hw => sub_call h0 h1 hd rf rg hc hw) hf hg d hk rf rg

theorem width_imm : ∀ d < 12, (((BitVec.ofNat 16 d).setWidth 64).setWidth 32).toNat = d ∧ 32 * d < 65536 := by
  decide

theorem slot_ne {k : Nat} (hk : k < 4) (r : Reg) (hr : r ∈ [Reg.x0, .x1, .x2, .x3]) : r ≠ slotReg k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases mem4 hr with rfl | rfl | rfl | rfl <;> decide

theorem slot_off {s₀ : State} (hp : Pre P L s₀) {k o l : Nat} (hk : k < 4) (f : o + l ≤ L.len (L.slot k)) :
    o < 65536 := by
  have := hp.args.len _ (hp.lt hk); omega

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `off` into bytes
`[o, o + 32d)` of the buffer in `slotReg k`, by a function meeting the
contract of compression and encoding at the widths `W`. -/
theorem ceWith_ok {s₀ : State} (hp : Pre P L s₀) {name : String} {code : Prog isa} {W : Nat → Prop}
    (hW : ∀ {d}, W d → d < 12)
    (hc : ∀ {s : State} {f o : Addr} {d : Nat}, s.gpr .x0 = f → ((s.gpr .x1).setWidth 32).toNat = d →
      s.gpr .x2 = o → (s.gpr .x3).toNat = 32 * d → W d →
      Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩ → Reduced s.mem f → Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr) →
      Covers [⟨o, 32 * d⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) → Q s') →
      WP isa (.call name code) s Q)
    {off d k o : Nat} (ho : PO P off) (hd : W d)
    (hk4 : k < 4) (hw : L.nrd ≤ L.slot k) (f : o + 32 * d ≤ L.len (L.slot k))
    (hs : L.slot k ≠ L.sc ∨ (o + 32 * d ≤ SV P ∧ (o + 32 * d ≤ off ∨ off + 1024 ≤ o))) {s : State}
    (hk : KB P L s₀ s) (hr : Reduced s.mem (sA L s₀ off)) :
    WP isa (ceWith name code off d (slotReg k) o) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) (L.slot k) o (32 * d)] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d) =
        compressEncode d (polyAt s.mem (sA L s₀ off)) ∧ s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  have ⟨wd, wd'⟩ := width_imm d (hW hd)
  rw [ceWith, List.append_assoc, List.cons_append]
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ =>
    wp_ptrTo (slot_ne hk4 .x2 (by decide)) (slot_off hp hk4 f) fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ =>
    wp_nil ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g : ∀ {r : Reg}, r ∈ [Reg.x0, .x1, .x2, .x3] → slotReg k ∉ [r] := fun hr h =>
    slot_ne hk4 _ hr (List.mem_singleton.mp h).symm
  refine hc (f := sA L s₀ off) (o := kA s₀ (L.slot k) + BitVec.ofNat 64 o) (d := d)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, e28 hk])
    (by rw [h₄.get .x1, h₃.get .x1, e₂]; exact wd)
    (by rw [h₄.get .x2, e₃, h₂.get _ (g (by decide)), h₁.get _ (g (by decide)), hk.ptr k hk4])
    (by rw [e₄]; exact imm16 wd') hd
    (hp.args.rdisj hp.scb hb (hp.fs fo) f (.inr (.inl hp.scw)) (by
      rcases hs with hs | ⟨-, hs⟩
      · exact .inl (Ne.symm hs)
      · exact .inr hs.symm))
    (by rw [m₄]; exact hr)
    (covers_cons (cov_sr hp kb₄ fo) (cov_r hp kb₄ hb f)) (cov_w hp kb₄ ⟨hw, hb⟩ f) fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact safe_R hp ⟨hw, hb⟩ f (by
        rcases hs with hs | ⟨hs, -⟩
        · exact .inl hs
        · exact .inr (.inr hs)),
    by rw [← m₄]; exact k₅.frame, by rw [p₅, m₄],
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

theorem mem_widths {d : Nat} (hd : d ∈ compressWidths) : d < 12 := by
  simp only [compressWidths, List.mem_cons, List.not_mem_nil, or_false] at hd; omega

/-- `ByteEncode_d(Compress_d(f))` for the widths of ML-KEM-768 (`d = 1`). -/
theorem ce_ok {s₀ : State} (hp : Pre P L s₀) {off d k o : Nat} (ho : PO P off) (hd : d ∈ compressWidths)
    (hk4 : k < 4) (hw : L.nrd ≤ L.slot k) (f : o + 32 * d ≤ L.len (L.slot k))
    (hs : L.slot k ≠ L.sc ∨ (o + 32 * d ≤ SV P ∧ (o + 32 * d ≤ off ∨ off + 1024 ≤ o))) {s : State}
    (hk : KB P L s₀ s) (hr : Reduced s.mem (sA L s₀ off)) :
    WP isa (ceAt off d (slotReg k) o) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) (L.slot k) o (32 * d)] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d) =
        compressEncode d (polyAt s.mem (sA L s₀ off)) ∧ s'.gpr .x24 = s.gpr .x24 :=
  ceWith_ok hp mem_widths (fun h0 h1 h2 h3 hw hd hr hc hw' => compressEncode_call h0 h1 h2 h3 hw hd hr hc hw')
    ho hd hk4 hw f hs hk hr

/-- `ByteEncode_d(Compress_d(f))` at the widths `d_u` and `d_v`. -/
theorem ceL_ok {s₀ : State} (hp : Pre P L s₀) (hc : Calls P) {off d k o : Nat} (ho : PO P off)
    (hd : d = P.du ∨ d = P.dv)
    (hk4 : k < 4) (hw : L.nrd ≤ L.slot k) (f : o + 32 * d ≤ L.len (L.slot k))
    (hs : L.slot k ≠ L.sc ∨ (o + 32 * d ≤ SV P ∧ (o + 32 * d ≤ off ∨ off + 1024 ≤ o))) {s : State}
    (hk : KB P L s₀ s) (hr : Reduced s.mem (sA L s₀ off)) :
    WP isa (P.ceLAt off d (slotReg k) o) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) (L.slot k) o (32 * d)] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d) =
        compressEncode d (polyAt s.mem (sA L s₀ off)) ∧ s'.gpr .x24 = s.gpr .x24 :=
  ceWith_ok hp (fun h => by have := hp.wf.facts; omega) hc.ce ho hd hk4 hw f hs hk hr

/-- `Decompress_d(ByteDecode_d(·))` of bytes `[o, o + 32d)` of the buffer in
`slotReg k`, into the polynomial at `off`, by a function meeting the contract
of decoding and decompression at the widths `W`. -/
theorem ddWith_ok {s₀ : State} (hp : Pre P L s₀) {name : String} {code : Prog isa} {W : Nat → Prop}
    (hW : ∀ {d}, W d → d < 12)
    (hc : ∀ {s : State} {b f : Addr} {d : Nat}, s.gpr .x0 = b → (s.gpr .x1).toNat = 32 * d →
      ((s.gpr .x2).setWidth 32).toNat = d → s.gpr .x3 = f → W d →
      Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩ → Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
      Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') →
      WP isa (.call name code) s Q)
    {k o d off : Nat} (hk4 : k < 4)
    (f : o + 32 * d ≤ L.len (L.slot k)) (hd : W d) (ho : PO P off)
    (hs : L.slot k ≠ L.sc ∨ o + 32 * d ≤ off ∨ off + 1024 ≤ o) {s : State} (hk : KB P L s₀ s) :
    WP isa (ddWith name code (slotReg k) o d off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off)
        (decodeDecompress d (bytesAt s.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  have ⟨wd, wd'⟩ := width_imm d (hW hd)
  rw [ddWith, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine WP.seq (wp_ptrTo (slot_ne hk4 .x0 (by decide)) (slot_off hp hk4 f) fun s₁ h₁ e₁ =>
    wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_ptrTo' (by decide)
    (by obtain ⟨-, h⟩ := ho; kom) fun s₄ h₄ e₄ => ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine hc (b := kA s₀ (L.slot k) + BitVec.ofNat 64 o) (f := sA L s₀ off) (d := d)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, hk.ptr k hk4])
    (by rw [h₄.get .x1, h₃.get .x1, e₂]; exact imm16 wd')
    (by rw [h₄.get .x2, e₃]; exact wd)
    (by rw [e₄, h₃.get .x28, h₂.get .x28, h₁.get .x28, e28 hk]) hd
    (hp.args.rdisj hb hp.scb f (hp.fs fo) (.inr (.inr hp.scw)) hs)
    (covers_cons (cov_r hp kb₄ hb f) (cov_sr hp kb₄ fo)) (cov_s hp kb₄ fo) fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp,
    by rw [← m₄]; exact k₅.frame, by rw [← m₄]; exact p₅,
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

/-- `Decompress_d(ByteDecode_d(·))` for the widths of ML-KEM-768 (`d = 1`). -/
theorem dd_ok {s₀ : State} (hp : Pre P L s₀) {k o d off : Nat} (hk4 : k < 4)
    (f : o + 32 * d ≤ L.len (L.slot k)) (hd : d ∈ compressWidths) (ho : PO P off)
    (hs : L.slot k ≠ L.sc ∨ o + 32 * d ≤ off ∨ off + 1024 ≤ o) {s : State} (hk : KB P L s₀ s) :
    WP isa (ddAt (slotReg k) o d off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off)
        (decodeDecompress d (bytesAt s.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  ddWith_ok hp mem_widths (fun h0 h1 h2 h3 hw hd hc hw' => decodeDecompress_call h0 h1 h2 h3 hw hd hc hw')
    hk4 f hd ho hs hk

/-- `Decompress_d(ByteDecode_d(·))` at the widths `d_u` and `d_v`. -/
theorem ddL_ok {s₀ : State} (hp : Pre P L s₀) (hc : Calls P) {k o d off : Nat} (hk4 : k < 4)
    (f : o + 32 * d ≤ L.len (L.slot k)) (hd : d = P.du ∨ d = P.dv) (ho : PO P off)
    (hs : L.slot k ≠ L.sc ∨ o + 32 * d ≤ off ∨ off + 1024 ≤ o) {s : State} (hk : KB P L s₀ s) :
    WP isa (P.ddLAt (slotReg k) o d off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off)
        (decodeDecompress d (bytesAt s.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  ddWith_ok hp (fun h => by have := hp.wf.facts; omega) hc.dd hk4 f hd ho hs hk

/-- `ByteDecode₁₂` of bytes `[o, o + 384)` of the buffer in `slotReg k`, into
the polynomial at `off`. -/
theorem dec12_ok {s₀ : State} (hp : Pre P L s₀) {k o off : Nat} (hk4 : k < 4)
    (f : o + 384 ≤ L.len (L.slot k)) (ho : PO P off) (hs : L.slot k ≠ L.sc ∨ o + 384 ≤ off ∨ off + 1024 ≤ o)
    {s : State} (hk : KB P L s₀ s) :
    WP isa (dec12At (slotReg k) o off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ off) (decode12 (bytesAt s.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) 384)) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  refine WP.seq (wp_ptrTo (slot_ne hk4 .x0 (by decide)) (slot_off hp hk4 f) fun s₁ h₁ e₁ =>
    wp_ptrTo' (by decide) (by obtain ⟨-, h⟩ := ho; kom) fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine decode12_call (b := kA s₀ (L.slot k) + BitVec.ofNat 64 o) (f := sA L s₀ off)
    (by rw [h₂.get .x0, e₁, hk.ptr k hk4]) (by rw [e₂, h₁.get .x28, e28 hk])
    (hp.args.rdisj hb hp.scb f (hp.fs fo) (.inr (.inr hp.scw)) hs)
    (covers_cons (cov_r hp kb₂ hb f) (cov_sr hp kb₂ fo)) (cov_s hp kb₂ fo) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp,
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.Kem
