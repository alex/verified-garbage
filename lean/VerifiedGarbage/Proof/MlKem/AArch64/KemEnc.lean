import VerifiedGarbage.Proof.MlKem.AArch64.KemB

/-!
# ML-KEM-768 on AArch64: K-PKE.Encrypt after the matrix

Untrusted: everything here is checked by Lean. `ŷ` (`y_step`), `u` into the
ciphertext (`u_step`), and `v` into it (`v_ok`), with `r` at `RB`, `m` at
`MB`, `Â` as the matrix left it, `t̂` decoded from the bytes of `ek` in a
buffer the function only reads, and the ciphertext in a written buffer
(`EncArgs`). What each step establishes survives the steps after it
(`EInv`), as they write only apart from it (`Far`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {L : Layout}

/-- Where `ek` and the ciphertext are: bytes `[eo, eo + 1152)` of the read
buffer in `slotReg kE`, and bytes `[co, co + 1088)` of the written buffer in
`slotReg kC` (in `scratch`, at `CB`). -/
structure EncArgs (L : Layout) (kE eo kC co : Nat) : Prop where
  hkE : kE < 4
  rE : L.slot kE < L.nrd
  fE : eo + 1152 ≤ L.len (L.slot kE)
  hkC : kC < 4
  wC : L.nrd ≤ L.slot kC
  fC : co + 1088 ≤ L.len (L.slot kC)
  sC : L.slot kC ≠ L.sc ∨ co = CB

/-- `Â` as the matrix left it in `mB`. -/
abbrev aM (L : Layout) (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAt mB (sA L s₀ (aOff i j))

/-- All that `K-PKE.Encrypt` writes: the Keccak state and working space,
`N`, `scratch` past `r ‖ N` and `K'` and `K̄`, the stack below the stack
pointer, and the ciphertext. -/
abbrev encW (L : Layout) (s₀ : State) (kC co : Nat) : List Region :=
  [R (kA s₀) L.sc 0 840, R (kA s₀) L.sc (RB + 32) 1, R (kA s₀) L.sc PB (SV - PB), below s₀.sp 16,
    R (kA s₀) (L.slot kC) co 1088]

/-- After `ŷ[j]` for `j < nY` and `u[i]` for `i < nU`, from memory `mE`. -/
structure EInv (L : Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem) (v : BitVec 64) (rv mv : List Byte)
    (nY nU : Nat) (s : State) : Prop where
  kb : KB L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (sA L s₀ MB) 32 = mv
  a : ∀ i < 3, ∀ j < 3, Reduced s.mem (sA L s₀ (aOff i j)) ∧
    polyAt s.mem (sA L s₀ (aOff i j)) = aM L s₀ mB i j
  y : ∀ j < nY, PolyIs s.mem (sA L s₀ (yOff j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 320 * i)) 320 =
    compressEncode 10 (encU (aM L s₀ mB) rv i)
  fr : Frame (encW L s₀ kC co) mE s.mem

/-- A region apart from what `EInv` describes. -/
def Far (L : Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (kA s₀) L.sc RB 32).Disjoint r ∧ (R (kA s₀) L.sc MB 32).Disjoint r ∧
    (R (kA s₀) L.sc AH 9216).Disjoint r ∧ (R (kA s₀) L.sc YH (1024 * nY)).Disjoint r ∧
    (R (kA s₀) (L.slot kC) co (320 * nU)).Disjoint r ∧ ∃ r' ∈ encW L s₀ kC co, Region.Sub r r'

theorem EInv.frame {s₀ : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {nY nU : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) {s s' : State} (h : EInv L s₀ kC co mE mB v rv mv nY nU s) (hk : KB L s₀ s')
    (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, Far L s₀ kC co nY nU r) : EInv L s₀ kC co mE mB v rv mv nY nU s' := by
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · have hd : ∀ r ∈ W, (polyRegion (sA L s₀ (aOff i j))).Disjoint r := fun r hr =>
      (hW r hr).2.2.1.sub_left (R.sub2 (by simp only [aOff]; omega) (by simp only [aOff]; omega))
    exact ⟨reduced_frame hf hd (h.a i hi j hj).1, by rw [polyAt_frame hf hd]; exact (h.a i hi j hj).2⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.1.sub_left
      (R.sub2 (by omega) (by omega))) (by decide)]
    exact h.u i hi

/-- A buffer of `scratch` apart from what `EInv` describes. -/
theorem far_s {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nY nU o l : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) (f : o + l ≤ SV)
    (h : (o + l ≤ RB ∨ RB + 32 ≤ o) ∧ (o + l ≤ MB ∨ MB + 32 ≤ o) ∧ (o + l ≤ AH ∨ AH + 9216 ≤ o) ∧
      (o + l ≤ YH ∨ YH + 1024 * nY ≤ o) ∧ (o + l ≤ CB) ∧ (o + l ≤ 840 ∨ (o = RB + 32 ∧ l = 1) ∨ PB ≤ o)) :
    Far L s₀ kC co nY nU (R (kA s₀) L.sc o l) := by
  have f' : o + l ≤ 32768 := by simp only [SV] at f; omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨sdisj hp (by decide) f' (by omega), sdisj hp (by decide) f' (by omega),
    sdisj hp (by decide) f' (by omega), sdisj hp (by simp only [YH]; omega) f' (by omega),
    R.disj hp.args (hp.lt A.hkC) hp.scb (by have := A.fC; omega) (by rw [hp.scl]; exact f') ?_, ?_⟩
  · rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inr (by subst hC; simp only [CB] at h5 ⊢; omega))
  · rcases h6 with h6 | ⟨rfl, rfl⟩ | h6
    · exact ⟨_, List.mem_cons_self .., R.sub2 (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        R.sub2 h6 (by simp only [SV, PB] at f ⊢; omega)⟩

theorem far_below {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co)
    {nY nU : Nat} (hnY : nY ≤ 3) (hnU : nU ≤ 3) : Far L s₀ kC co nY nU (below s₀.sp 16) :=
  ⟨below_R hp hp.scb (by rw [hp.scl]; decide), below_R hp hp.scb (by rw [hp.scl]; decide),
    below_R hp hp.scb (by rw [hp.scl]; decide), below_R hp hp.scb (by rw [hp.scl]; simp only [YH]; omega),
    below_R hp (hp.lt A.hkC) (by have := A.fC; omega), ⟨_, by simp, fun _ h => h⟩⟩

/-- Bytes of a buffer the function only reads, as they were. -/
theorem KB.ro_bytes {s₀ s : State} (h : KB L s₀ s) {b o n : Nat} (hb : b < L.nrd) (f : o + n ≤ L.len b) :
    bytesAt s.mem (kA s₀ b + BitVec.ofNat 64 o) n = bytesAt s₀.mem (kA s₀ b + BitVec.ofNat 64 o) n := by
  rw [← bytesAt_slice _ _ f, ← bytesAt_slice _ _ f, h.ro b hb]

theorem po_a {i j : Nat} (hi : i < 3) (hj : j < 3) : PO (aOff i j) :=
  ⟨by simp only [aOff]; omega, by simp only [aOff, AH, SV]; omega⟩
theorem po_y {j : Nat} (hj : j < 3) : PO (yOff j) :=
  ⟨by simp only [yOff, YH, AH]; omega, by simp only [yOff, YH, SV]; omega⟩
theorem po_TP : PO TP := ⟨by decide, by decide⟩
theorem po_PP : PO PP := ⟨by decide, by decide⟩
theorem po_EP : PO EP := ⟨by decide, by decide⟩
theorem po_TH : PO TH := ⟨by decide, by decide⟩

/-- A polynomial buffer of `scratch` that `K-PKE.Encrypt` writes. -/
theorem far_w {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) {off : Nat} (h1 : YH + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB) :
    Far L s₀ kC co nY nU (R (kA s₀) L.sc off 1024) :=
  far_s hp A hnY hnU (by simp only [CB, SV] at *; omega) (by koffs; omega)

theorem far_ns {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) : Far L s₀ kC co nY nU (R (kA s₀) L.sc NS 1024) :=
  far_s hp A hnY hnU (by decide) (by koffs; omega)

theorem far_pcW {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) {off : Nat} (h1 : YH + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB) :
    ∀ r ∈ pcW L s₀ off, Far L s₀ kC co nY nU r := by
  intro r hr
  rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact far_s hp A hnY hnU (by decide) (by koffs; omega)
  · exact far_s hp A hnY hnU (by decide) (by koffs; omega)
  · exact far_below hp A hnY hnU
  · exact far_s hp A hnY hnU (by decide) (by
      refine ⟨.inr (by decide), .inr (by decide), .inl (by decide), .inl (by decide), by decide, .inr (.inl ⟨rfl, rfl⟩)⟩)
  · exact far_s hp A hnY hnU (by decide) (by koffs; omega)
  · exact far_w hp A hnY hnU h1 h2

theorem far_mul {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) {off : Nat} (h1 : YH + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB) :
    ∀ r ∈ [R (kA s₀) L.sc off 1024, R (kA s₀) L.sc NS 1024], Far L s₀ kC co nY nU r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · exact far_w hp A hnY hnU h1 h2
  · exact far_ns hp A hnY hnU

theorem far_one {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ 3) (hnU : nU ≤ 3) {off : Nat} (h1 : YH + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB) :
    ∀ r ∈ [R (kA s₀) L.sc off 1024], Far L s₀ kC co nY nU r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact far_w hp A hnY hnU h1 h2

/-- Two polynomial buffers of `scratch` apart. -/
theorem papart {s₀ : State} (hp : Pre L s₀) {o₁ o₂ : Nat} (h₁ : PO o₁) (h₂ : PO o₂)
    (h : o₁ + 1024 ≤ o₂ ∨ o₂ + 1024 ≤ o₁) : (polyRegion (sA L s₀ o₁)).Disjoint (R (kA s₀) L.sc o₂ 1024) :=
  sdisj hp h₁.le h₂.le h

/-- A polynomial buffer of `scratch` past the NTT's working space is apart from it. -/
theorem pns {s₀ : State} (hp : Pre L s₀) {o : Nat} (h : PO o) :
    (polyRegion (sA L s₀ o)).Disjoint (R (kA s₀) L.sc NS 1024) := h.ns hp

/-! ## `ŷ` -/

theorem y_step {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {j : Nat} (hj : j < 3) {s : State}
    (h : EInv L s₀ kC co mE mB v rv mv j 0 s) : WP isa (encYAt j) s (EInv L s₀ kC co mE mB v rv mv (j + 1) 0) := by
  have hpo := po_y hj
  have h1 : YH + 1024 * j ≤ yOff j := by simp only [yOff]; omega
  have h2 : yOff j + 1024 ≤ CB := by simp only [yOff, YH, CB]; omega
  refine WP.seq (WP.mono (prfCbd_ok hp (N := j) (off := yOff j) (by omega) hpo h.kb h.r)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame (by omega) (by decide) kb₁ x₁ f₁ (far_pcW hp A (by omega) (by decide) h1 h2)
  refine WP.mono (ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame (by omega) (by decide) kb₂ x₂ f₂ (far_mul hp A (by omega) (by decide) h1 h2)
  rw [p₁.2] at p₂
  refine ⟨e₂.kb, e₂.x24, e₂.r, e₂.m, e₂.a, fun j' hj' => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), e₂.fr⟩
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
  · refine polyIs_frame f₂ (fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact papart hp (po_y (by omega)) hpo (by simp only [yOff]; omega)
      · exact pns hp (po_y (by omega))) (polyIs_frame f₁ (fun r hr => ?_) (h.y j' hj'))
    -- `ŷ[j']` is apart from what `prfCbd` writes
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp (po_y (by omega)).le (by decide) (.inr (by simp only [yOff, YH, KEM.ST]; omega))
    · exact sdisj hp (po_y (by omega)).le (by decide) (.inr (by simp only [yOff, YH, KEM.WK]; omega))
    · exact below_R hp hp.scb (by rw [hp.scl]; exact (po_y (by omega)).le)
    · exact sdisj hp (po_y (by omega)).le (by decide) (.inr (by simp only [yOff, YH, RB]; omega))
    · exact sdisj hp (po_y (by omega)).le (by decide) (.inr (by simp only [yOff, YH, PB]; omega))
    · exact papart hp (po_y (by omega)) hpo (by simp only [yOff]; omega)
  · exact p₂

/-! ## `u` and `v` -/

/-- Bytes of the ciphertext past those written so far. -/
theorem far_ct {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {nU o l : Nat}
    (h : co + 320 * nU ≤ o) (f : o + l ≤ co + 1088) : Far L s₀ kC co 3 nU (R (kA s₀) (L.slot kC) o l) := by
  have hb := hp.lt A.hkC
  have fC := A.fC
  have f' : o + l ≤ L.len (L.slot kC) := by omega
  have hs : ∀ {o' l' : Nat}, o' + l' ≤ CB → L.slot kC ≠ L.sc ∨ o' + l' ≤ o ∨ o + l ≤ o' := fun h' => by
    rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inl (by subst hC; omega))
  have g : ∀ {o' l' : Nat}, o' + l' ≤ CB → (R (kA s₀) L.sc o' l').Disjoint (R (kA s₀) (L.slot kC) o l) :=
    fun h' => R.disj hp.args hp.scb hb (by rw [hp.scl]; simp only [CB] at h'; omega) f' (by
      rcases hs h' with e | e
      · exact .inl (Ne.symm e)
      · exact .inr e)
  exact ⟨g (by decide), g (by decide), g (by decide), g (by decide),
    R.disj hp.args hb hb (by omega) f' (.inr (.inl h)), ⟨_, by simp, R.sub2 (by omega) f⟩⟩

theorem u_part1 {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i < 3) {s : State}
    (h : EInv L s₀ kC co mE mB v rv mv 3 i s) {REST : Prog isa} {Q : State → Prop}
    (hR : ∀ s', EInv L s₀ kC co mE mB v rv mv 3 i s' →
      PolyIs s'.mem (sA L s₀ TP) (dot3 (fun j => aM L s₀ mB j i) (encY rv)) → WP isa REST s' Q) :
    WP isa (.seq (mulAt TP (aOff 0 i) (yOff 0)) <| .seq (mulAt PP (aOff 1 i) (yOff 1)) <|
      .seq (addAt TP PP) <| .seq (mulAt PP (aOff 2 i) (yOff 2)) <| .seq (addAt TP PP) REST) s Q := by
  have hn : i ≤ 3 := by omega
  have ha : ∀ {j : Nat}, j < 3 → aOff j i + 1024 ≤ PP ∧ aOff j i + 1024 ≤ TP := fun hj => by
    simp only [aOff, AH, TP, PP]; omega
  have a0 := h.a 0 (by decide) i hi
  have y0 := h.y 0 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_TP (po_a (by decide) hi) (po_y (by decide)) (.inr (ha (by decide)).2)
    (.inr (by decide)) h.kb a0.1 y0.1) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := h.frame (by decide) hn kb₁ x₁ f₁ (far_mul hp A (by decide) hn (by decide) (by decide))
  rw [a0.2, y0.2] at t₁
  have a1 := e₁.a 1 (by decide) i hi
  have y1 := e₁.y 1 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_PP (po_a (by decide) hi) (po_y (by decide)) (.inr (ha (by decide)).1)
    (.inr (by decide)) e₁.kb a1.1 y1.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame (by decide) hn kb₂ x₂ f₂ (far_mul hp A (by decide) hn (by decide) (by decide))
  have t₂ := polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp po_TP po_PP (by decide)
    · exact pns hp po_TP) t₁
  rw [a1.2, y1.2] at p₂
  refine WP.seq (WP.mono (add_ok hp po_TP po_PP (.inl (by decide)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame (by decide) hn kb₃ x₃ f₃ (far_one hp A (by decide) hn (by decide) (by decide))
  rw [t₂.2, p₂.2] at t₃
  have a2 := e₃.a 2 (by decide) i hi
  have y2 := e₃.y 2 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_PP (po_a (by decide) hi) (po_y (by decide)) (.inr (ha (by decide)).1)
    (.inr (by decide)) e₃.kb a2.1 y2.1) fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame (by decide) hn kb₄ x₄ f₄ (far_mul hp A (by decide) hn (by decide) (by decide))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp po_TP po_PP (by decide)
    · exact pns hp po_TP) t₃
  rw [a2.2, y2.2] at p₄
  refine WP.seq (WP.mono (add_ok hp po_TP po_PP (.inl (by decide)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame (by decide) hn kb₅ x₅ f₅ (far_one hp A (by decide) hn (by decide) (by decide))
  rw [t₄.2, p₄.2] at t₅
  exact hR s₅ e₅ t₅

theorem u_part2 {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i < 3) {s : State}
    (h : EInv L s₀ kC co mE mB v rv mv 3 i s)
    (ht : PolyIs s.mem (sA L s₀ TP) (dot3 (fun j => aM L s₀ mB j i) (encY rv))) :
    WP isa (.seq (nttInvAt TP) <| .seq (prfCbd (3 + i) EP) <| .seq (addAt TP EP)
      (ceAt TP 10 (slotReg kC) (co + 320 * i))) s (EInv L s₀ kC co mE mB v rv mv 3 (i + 1)) := by
  have hn : i ≤ 3 := by omega
  refine WP.seq (WP.mono (nttInv_ok hp po_TP h.kb ht.1) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := h.frame (by decide) hn kb₁ x₁ f₁ (far_mul hp A (by decide) hn (by decide) (by decide))
  rw [ht.2] at t₁
  refine WP.seq (WP.mono (prfCbd_ok hp (N := 3 + i) (by omega) po_EP e₁.kb e₁.r)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame (by decide) hn kb₂ x₂ f₂ (far_pcW hp A (by decide) hn (by decide) (by decide))
  have t₂ := polyIs_frame f₂ (fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact below_R hp hp.scb (by rw [hp.scl]; decide)
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact papart hp po_TP po_EP (by decide)) t₁
  refine WP.seq (WP.mono (add_ok hp po_TP po_EP (.inr (by decide)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame (by decide) hn kb₃ x₃ f₃ (far_one hp A (by decide) hn (by decide) (by decide))
  rw [t₂.2, p₂.2] at t₃
  have fC := A.fC
  refine WP.mono (ce_ok hp (off := TP) (d := 10) (k := kC) (o := co + 320 * i) po_TP (by decide) A.hkC A.wC
    (by omega) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; simp only [CB, SV]; omega, .inr (by subst hC; simp only [CB, TP]; omega)⟩)
    e₃.kb t₃.1) fun s₄ ⟨kb₄, f₄, b₄, x₄⟩ => ?_
  have e₄ := e₃.frame (by decide) hn kb₄ x₄ f₄ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by omega)
  refine ⟨e₄.kb, e₄.x24, e₄.r, e₄.m, e₄.a, e₄.y, fun i' hi' => ?_, e₄.fr⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₄.u i' hi'
  · rw [b₄, t₃.2]; rfl

theorem u_step {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i < 3) {s : State}
    (h : EInv L s₀ kC co mE mB v rv mv 3 i s) :
    WP isa (encUAt (slotReg kC) co i) s (EInv L s₀ kC co mE mB v rv mv 3 (i + 1)) :=
  u_part1 hp A hi h fun _ h' t => u_part2 hp A hi h' t

theorem v_part1 {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀ j < 3, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {s : State} (h : EInv L s₀ kC co mE mB v rv mv 3 3 s) {REST : Prog isa} {Q : State → Prop}
    (hR : ∀ s', EInv L s₀ kC co mE mB v rv mv 3 3 s' → PolyIs s'.mem (sA L s₀ TP) (dot3 T (encY rv)) →
      WP isa REST s' Q) :
    WP isa (.seq (dec12At (slotReg kE) eo TH) <| .seq (mulAt TP TH (yOff 0)) <|
      .seq (dec12At (slotReg kE) (eo + 384) TH) <| .seq (mulAt PP TH (yOff 1)) <| .seq (addAt TP PP) <|
      .seq (dec12At (slotReg kE) (eo + 768) TH) <| .seq (mulAt PP TH (yOff 2)) <| .seq (addAt TP PP) REST)
      s Q := by
  have fE := A.fE
  have hs : L.slot kE ≠ L.sc := by have := A.rE; have := hp.scw; omega
  have hT0 : decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 eo) 384) = T 0 := hT 0 (by decide)
  have hT1 : decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384)) 384) = T 1 :=
    hT 1 (by decide)
  have hT2 : decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 768)) 384) = T 2 :=
    hT 2 (by decide)
  -- `t̂[0] ŷ[0]`
  refine WP.seq (WP.mono (dec12_ok hp (k := kE) (o := eo) A.hkE (by omega) po_TH (.inl hs) h.kb)
    fun s₁ ⟨kb₁, f₁, d₁, x₁⟩ => ?_)
  have e₁ := h.frame (by decide) (by decide) kb₁ x₁ f₁ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [h.kb.ro_bytes A.rE (by omega), hT0] at d₁
  have y0 := e₁.y 0 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_TP po_TH (po_y (by decide)) (.inl (by decide)) (.inr (by decide))
    e₁.kb d₁.1 y0.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  have e₂ := e₁.frame (by decide) (by decide) kb₂ x₂ f₂ (far_mul hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [d₁.2, y0.2] at t₂
  -- `t̂[1] ŷ[1]`
  refine WP.seq (WP.mono (dec12_ok hp (k := kE) (o := eo + 384) A.hkE (by omega) po_TH (.inl hs) e₂.kb)
    fun s₃ ⟨kb₃, f₃, d₃, x₃⟩ => ?_)
  have e₃ := e₂.frame (by decide) (by decide) kb₃ x₃ f₃ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [e₂.kb.ro_bytes A.rE (by omega), hT1] at d₃
  have t₃ := polyIs_frame f₃ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp po_TP po_TH (by decide)) t₂
  have y1 := e₃.y 1 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_PP po_TH (po_y (by decide)) (.inl (by decide)) (.inr (by decide))
    e₃.kb d₃.1 y1.1) fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame (by decide) (by decide) kb₄ x₄ f₄ (far_mul hp A (by decide) (by decide) (by decide)
    (by decide))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp po_TP po_PP (by decide)
    · exact pns hp po_TP) t₃
  rw [d₃.2, y1.2] at p₄
  refine WP.seq (WP.mono (add_ok hp po_TP po_PP (.inl (by decide)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame (by decide) (by decide) kb₅ x₅ f₅ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [t₄.2, p₄.2] at t₅
  -- `t̂[2] ŷ[2]`
  refine WP.seq (WP.mono (dec12_ok hp (k := kE) (o := eo + 768) A.hkE (by omega) po_TH (.inl hs) e₅.kb)
    fun s₆ ⟨kb₆, f₆, d₆, x₆⟩ => ?_)
  have e₆ := e₅.frame (by decide) (by decide) kb₆ x₆ f₆ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [e₅.kb.ro_bytes A.rE (by omega), hT2] at d₆
  have t₆ := polyIs_frame f₆ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp po_TP po_TH (by decide)) t₅
  have y2 := e₆.y 2 (by decide)
  refine WP.seq (WP.mono (mul_ok hp po_PP po_TH (po_y (by decide)) (.inl (by decide)) (.inr (by decide))
    e₆.kb d₆.1 y2.1) fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  have e₇ := e₆.frame (by decide) (by decide) kb₇ x₇ f₇ (far_mul hp A (by decide) (by decide) (by decide)
    (by decide))
  have t₇ := polyIs_frame f₇ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp po_TP po_PP (by decide)
    · exact pns hp po_TP) t₆
  rw [d₆.2, y2.2] at p₇
  refine WP.seq (WP.mono (add_ok hp po_TP po_PP (.inl (by decide)) e₇.kb t₇.1 p₇.1)
    fun s₈ ⟨kb₈, f₈, t₈, x₈⟩ => ?_)
  have e₈ := e₇.frame (by decide) (by decide) kb₈ x₈ f₈ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [t₇.2, p₇.2] at t₈
  exact hR s₈ e₈ t₈

/-- `v`. -/
abbrev vPoly (T : Nat → Poly) (rv mv : List Byte) : Poly :=
  add (add (nttInv (dot3 T (encY rv))) (cbd rv 6)) (decodeDecompress 1 mv)

theorem v_part2 {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly} {s : State} (h : EInv L s₀ kC co mE mB v rv mv 3 3 s)
    (ht : PolyIs s.mem (sA L s₀ TP) (dot3 T (encY rv))) :
    WP isa (.seq (nttInvAt TP) <| .seq (prfCbd 6 EP) <| .seq (addAt TP EP) <| .seq (ddAt .x28 MB 1 EP) <|
      .seq (addAt TP EP) (ceAt TP 4 (slotReg kC) (co + 960))) s fun s' =>
      EInv L s₀ kC co mE mB v rv mv 3 3 s' ∧
      bytesAt s'.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 960)) 128 = compressEncode 4 (vPoly T rv mv) := by
  refine WP.seq (WP.mono (nttInv_ok hp po_TP h.kb ht.1) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := h.frame (by decide) (by decide) kb₁ x₁ f₁ (far_mul hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [ht.2] at t₁
  refine WP.seq (WP.mono (prfCbd_ok hp (N := 6) (by decide) po_EP e₁.kb e₁.r) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame (by decide) (by decide) kb₂ x₂ f₂ (far_pcW hp A (by decide) (by decide) (by decide)
    (by decide))
  have fTP : ∀ r ∈ pcW L s₀ EP, (polyRegion (sA L s₀ TP)).Disjoint r := fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact below_R hp hp.scb (by rw [hp.scl]; decide)
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact sdisj hp po_TP.le (by decide) (by decide)
    · exact papart hp po_TP po_EP (by decide)
  have t₂ := polyIs_frame f₂ fTP t₁
  refine WP.seq (WP.mono (add_ok hp po_TP po_EP (.inr (by decide)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame (by decide) (by decide) kb₃ x₃ f₃ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [t₂.2, p₂.2] at t₃
  refine WP.seq (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP) (by decide)
    (by rw [hp.scl]; decide) (by decide) po_EP (.inr (.inl (by decide))) e₃.kb)
    fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame (by decide) (by decide) kb₄ x₄ f₄ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp po_TP po_EP (by decide)) t₃
  have hm : bytesAt s₃.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₃.m
  rw [hm] at p₄
  refine WP.seq (WP.mono (add_ok hp po_TP po_EP (.inr (by decide)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame (by decide) (by decide) kb₅ x₅ f₅ (far_one hp A (by decide) (by decide) (by decide)
    (by decide))
  rw [t₄.2, p₄.2] at t₅
  have fC := A.fC
  refine WP.mono (ce_ok hp (off := TP) (d := 4) (k := kC) (o := co + 960) po_TP (by decide) A.hkC A.wC
    (by omega) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; simp only [CB, SV]; omega, .inr (by subst hC; simp only [CB, TP]; omega)⟩)
    e₅.kb t₅.1) fun s₆ ⟨kb₆, f₆, b₆, x₆⟩ => ?_
  refine ⟨e₅.frame (by decide) (by decide) kb₆ x₆ f₆ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (by omega) (by omega), ?_⟩
  rw [b₆, t₅.2]

/-- `ŷ`, `u` and `v`. -/
theorem encrypt_ok {s₀ : State} (hp : Pre L s₀) {kE eo kC co : Nat} (A : EncArgs L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀ j < 3, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {s : State} (h : EInv L s₀ kC co mE mB v rv mv 0 0 s) :
    WP isa (encryptC (slotReg kE) eo .x28 MB (slotReg kC) co) s fun s' =>
      EInv L s₀ kC co mE mB v rv mv 3 3 s' ∧
      bytesAt s'.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 960)) 128 = compressEncode 4 (vPoly T rv mv) :=
  WP.seq (WP.mono (y_step hp A (j := 0) (by decide) h) fun _ h₁ =>
  WP.seq (WP.mono (y_step hp A (j := 1) (by decide) h₁) fun _ h₂ =>
  WP.seq (WP.mono (y_step hp A (j := 2) (by decide) h₂) fun _ h₃ =>
  WP.seq (WP.mono (u_step hp A (i := 0) (by decide) h₃) fun _ u₁ =>
  WP.seq (WP.mono (u_step hp A (i := 1) (by decide) u₁) fun _ u₂ =>
  WP.seq (WP.mono (u_step hp A (i := 2) (by decide) u₂) fun _ u₃ =>
    v_part1 hp A hT u₃ fun _ h' t => v_part2 hp A h' t))))))

/-- The ciphertext's bytes. -/
theorem ct_at {m : Mem} {p : Addr} {U : Nat → List Byte} {V : List Byte}
    (hu : ∀ i < 3, bytesAt m (p + BitVec.ofNat 64 (320 * i)) 320 = U i) (hv : bytesAt m (p + BitVec.ofNat 64 960) 128 = V) :
    bytesAt m p 1088 = U 0 ++ U 1 ++ U 2 ++ V := by
  have h0 := hu 0 (by decide)
  rw [Nat.mul_zero, ptr_zero] at h0
  have h1 : bytesAt m (p + BitVec.ofNat 64 320) 320 = U 1 := hu 1 (by decide)
  have h2 : bytesAt m (p + BitVec.ofNat 64 (320 + 320)) 320 = U 2 := hu 2 (by decide)
  have hv' : bytesAt m (p + BitVec.ofNat 64 (320 + 320 + 320)) 128 = V := hv
  rw [show (1088 : Nat) = 320 + 320 + 320 + 128 from rfl, bytesAt_add, bytesAt_add, bytesAt_add, h0, h1, h2, hv']

end VG.Proof.MlKem.AArch64.Kem
