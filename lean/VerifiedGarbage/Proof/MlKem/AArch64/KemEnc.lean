import VerifiedGarbage.Proof.MlKem.AArch64.KemB

/-!
# ML-KEM on AArch64: K-PKE.Encrypt after the matrix

`ŷ` (`y_step`), `u` into the ciphertext (`u_step`), and `v` into it (`v_ok`),
with `r` at `RB`, `m` at `MB`, `Â` as the matrix left it, `t̂` decoded from
the bytes of `ek` in a buffer the function only reads, and the ciphertext in a
written buffer (`EncArgs`). What each step establishes survives the steps
after it (`EInv`), as they write only apart from it (`Far`). The steps over
`i < k` are loops (`WPs.range`), and the sums of products in `u[i]` and `v`
loops over `j < k` (`WPs.dot`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay} {L : Layout}

/-- `u[i]`'s bytes end within the first `k` ones. -/
theorem du_le {P : KemLay} {i : Nat} (hi : i < P.k) : 32 * P.du * i + 32 * P.du ≤ 32 * (P.du * P.k) := by
  rw [← Nat.mul_assoc]; exact mul_succ_le hi

/-- Where `ek` and the ciphertext are: bytes `[eo, eo + 384 k)` of the read
buffer in `slotReg kE`, and bytes `[co, co + ctLen)` of the written buffer in
`slotReg kC` (in `scratch`, at `CB`). -/
structure EncArgs (P : KemLay) (L : Layout) (kE eo kC co : Nat) : Prop where
  hkE : kE < 4
  rE : L.slot kE < L.nrd
  fE : eo + 384 * P.k ≤ L.len (L.slot kE)
  hkC : kC < 4
  wC : L.nrd ≤ L.slot kC
  fC : co + P.ctLen ≤ L.len (L.slot kC)
  sC : L.slot kC ≠ L.sc ∨ co = CB P

/-- `Â` as the matrix left it in `mB`. -/
abbrev aM (P : KemLay) (L : Layout) (s₀ : State) (mB : Mem) (i j : Nat) : Poly :=
  polyAt mB (sA L s₀ (aOff P i j))

/-- All that `K-PKE.Encrypt` writes: the Keccak state and working space,
`N`, `scratch` past `r ‖ N` and `K'` and `K̄`, the stack below the stack
pointer, and the ciphertext. -/
abbrev encW (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) : List Region :=
  [R (kA s₀) L.sc 0 840, R (kA s₀) L.sc (RB + 32) 1, R (kA s₀) L.sc PB (SV P - PB), below s₀.sp 16,
    R (kA s₀) (L.slot kC) co P.ctLen]

/-- After `ŷ[j]` for `j < nY` and `u[i]` for `i < nU`, from memory `mE`. -/
structure EInv (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem) (v : BitVec 64)
    (rv mv : List Byte) (nY nU : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (sA L s₀ MB) 32 = mv
  a : ∀ i < P.k, ∀ j < P.k, Reduced s.mem (sA L s₀ (aOff P i j)) ∧
    polyAt s.mem (sA L s₀ (aOff P i j)) = aM P L s₀ mB i j
  y : ∀ j < nY, PolyIs s.mem (sA L s₀ (yOff P j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * i)) (32 * P.du) =
    compressEncode P.du (KPke.encU P.params (aM P L s₀ mB) rv i)
  fr : Frame (encW P L s₀ kC co) mE s.mem

/-- A region apart from what `EInv` describes. -/
def Far (P : KemLay) (L : Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (kA s₀) L.sc RB 32).Disjoint r ∧ (R (kA s₀) L.sc MB 32).Disjoint r ∧
    (R (kA s₀) L.sc AH (1024 * (P.k * P.k))).Disjoint r ∧ (R (kA s₀) L.sc (YH P) (1024 * nY)).Disjoint r ∧
    (R (kA s₀) (L.slot kC) co (32 * P.du * nU)).Disjoint r ∧ ∃ r' ∈ encW P L s₀ kC co, Region.Sub r r'

theorem EInv.frame {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : EInv P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, Far P L s₀ kC co nY nU r) : EInv P L s₀ kC co mE mB v rv mv nY nU s' := by
  have hw := hp.wf
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · have hij := ij_lt hi hj
    have hd : ∀ r ∈ W, (polyRegion (sA L s₀ (aOff P i j))).Disjoint r := fun r hr =>
      (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))
    exact ⟨reduced_frame hf hd (h.a i hi j hj).1, by rw [polyAt_frame hf hd]; exact (h.a i hi j hj).2⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.1.sub_left
      (R.sub2 (by omega) (by have := mul_succ_le (a := 32 * P.du) hi; omega))) (by kom)]
    exact h.u i hi

/-- A buffer of `scratch` apart from what `EInv` describes. -/
theorem far_s {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {nY nU o l : Nat} (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) (f : o + l ≤ SV P)
    (h : (o + l ≤ RB ∨ RB + 32 ≤ o) ∧ (o + l ≤ MB ∨ MB + 32 ≤ o) ∧
      (o + l ≤ AH ∨ AH + 1024 * (P.k * P.k) ≤ o) ∧ (o + l ≤ YH P ∨ YH P + 1024 * nY ≤ o) ∧ (o + l ≤ CB P) ∧
      (o + l ≤ 840 ∨ (o = RB + 32 ∧ l = 1) ∨ PB ≤ o)) :
    Far P L s₀ kC co nY nU (R (kA s₀) L.sc o l) := by
  have hw := hp.wf
  have f' : o + l ≤ SV P + 48 := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hu := Nat.mul_le_mul_left (32 * P.du) hnU
  refine ⟨sdisj hp (by lom) f' (by omega), sdisj hp (by lom) f' (by omega),
    sdisj hp (by lom) f' (by omega), sdisj hp (by lom) f' (by omega),
    hp.args.rdisj (hp.lt A.hkC) hp.scb (by have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom)
      (hp.fs f') (.inr (.inr hp.scw)) ?_, ?_⟩
  · rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inr (by subst hC; omega))
  · rcases h6 with h6 | ⟨rfl, rfl⟩ | h6
    · exact ⟨_, List.mem_cons_self .., R.sub2 (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        R.sub2 h6 (by simp only [PB] at h6 ⊢; omega)⟩

theorem far_below {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {nY nU : Nat} (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) : Far P L s₀ kC co nY nU (below s₀.sp 16) := by
  have hw := hp.wf
  have hu := Nat.mul_le_mul_left (32 * P.du) hnU
  exact ⟨below_R hp hp.scb (hp.fs (by lom)), below_R hp hp.scb (hp.fs (by lom)),
    below_R hp hp.scb (hp.fs (by lom)), below_R hp hp.scb (hp.fs (by lom)),
    below_R hp (hp.lt A.hkC) (by have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom),
    ⟨_, by simp, fun _ h => h⟩⟩

/-- Bytes of a buffer the function only reads, as they were. -/
theorem KB.ro_bytes {s₀ s : State} (h : KB P L s₀ s) {b o n : Nat} (hb : b < L.nrd) (f : o + n ≤ L.len b) :
    bytesAt s.mem (kA s₀ b + BitVec.ofNat 64 o) n = bytesAt s₀.mem (kA s₀ b + BitVec.ofNat 64 o) n := by
  rw [← bytesAt_slice _ _ f, ← bytesAt_slice _ _ f, h.ro b hb]

theorem po_a (hP : P.Wf) {i j : Nat} (hi : i < P.k) (hj : j < P.k) : PO P (aOff P i j) :=
  have := ij_lt hi hj; ⟨by lom, by lom⟩
theorem po_y (hP : P.Wf) {j : Nat} (hj : j < P.k) : PO P (yOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : PO P (TP P) := ⟨by lom, by lom⟩
theorem po_PP (hP : P.Wf) : PO P (PP P) := ⟨by lom, by lom⟩
theorem po_EP (hP : P.Wf) : PO P (EP P) := ⟨by lom, by lom⟩
theorem po_TH (hP : P.Wf) : PO P (TH P) := ⟨by lom, by lom⟩

/-- A polynomial buffer of `scratch` that `K-PKE.Encrypt` writes. -/
theorem far_w {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    Far P L s₀ kC co nY nU (R (kA s₀) L.sc off 1024) :=
  have := hp.wf
  far_s hp A hnY hnU (by lom) (by lom)

theorem far_ns {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) : Far P L s₀ kC co nY nU (R (kA s₀) L.sc NS 1024) :=
  have := hp.wf
  far_s hp A hnY hnU (by lom) (by lom)

theorem far_pcW {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ pcW L s₀ off, Far P L s₀ kC co nY nU r := by
  have := hp.wf
  intro r hr
  rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact far_s hp A hnY hnU (by lom) (by lom)
  · exact far_s hp A hnY hnU (by lom) (by lom)
  · exact far_below hp A hnY hnU
  · exact far_s hp A hnY hnU (by lom) ⟨.inr (by decide), .inr (by decide), .inl (by decide), .inl (by lom),
      by lom, .inr (.inl ⟨rfl, rfl⟩)⟩
  · exact far_s hp A hnY hnU (by lom) (by lom)
  · exact far_w hp A hnY hnU h1 h2

theorem far_mul {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ [R (kA s₀) L.sc off 1024, R (kA s₀) L.sc NS 1024], Far P L s₀ kC co nY nU r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · exact far_w hp A hnY hnU h1 h2
  · exact far_ns hp A hnY hnU

theorem far_one {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ [R (kA s₀) L.sc off 1024], Far P L s₀ kC co nY nU r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact far_w hp A hnY hnU h1 h2

/-- Two polynomial buffers of `scratch` apart. -/
theorem papart {s₀ : State} (hp : Pre P L s₀) {o₁ o₂ : Nat} (h₁ : PO P o₁) (h₂ : PO P o₂)
    (h : o₁ + 1024 ≤ o₂ ∨ o₂ + 1024 ≤ o₁) : (polyRegion (sA L s₀ o₁)).Disjoint (R (kA s₀) L.sc o₂ 1024) :=
  sdisj hp h₁.le h₂.le h

/-- A polynomial buffer of `scratch` past the NTT's working space is apart from it. -/
theorem pns {s₀ : State} (hp : Pre P L s₀) {o : Nat} (h : PO P o) :
    (polyRegion (sA L s₀ o)).Disjoint (R (kA s₀) L.sc NS 1024) := h.ns hp

/-! ## `ŷ` -/

theorem y_step {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {j : Nat} (hj : j < P.k) {s : State}
    (h : EInv P L s₀ kC co mE mB v rv mv j 0 s) :
    WP isa (P.encYAtWith keccak.callee j) s (EInv P L s₀ kC co mE mB v rv mv (j + 1) 0) := by
  have hw := hp.wf
  have hpo := po_y hw hj
  have h1 : YH P + 1024 * j ≤ yOff P j := by simp only [yOff]; omega
  have h2 : yOff P j + 1024 ≤ CB P := by lom
  refine WP.seq (WP.mono (prfCbd_ok hp (N := j) (off := yOff P j) (by lom) hpo h.kb h.r)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame hp kb₁ x₁ f₁ (far_pcW hp A (by omega) (by omega) h1 h2)
  refine WP.mono (ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (by omega) (by omega) h1 h2)
  rw [p₁.2] at p₂
  refine ⟨e₂.kb, e₂.x24, e₂.r, e₂.m, e₂.a, fun j' hj' => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), e₂.fr⟩
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
  · have hy := po_y hw (j := j') (by omega)
    refine polyIs_frame f₂ (fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact papart hp hy hpo (by simp only [yOff]; omega)
      · exact pns hp hy) (polyIs_frame f₁ (fun r hr => ?_) (h.y j' hj'))
    -- `ŷ[j']` is apart from what `prfCbdWith keccak.callee` writes
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp hy.le (by lom) (.inr (by lom))
    · exact sdisj hp hy.le (by lom) (.inr (by lom))
    · exact below_R hp hp.scb (hp.fs hy.le)
    · exact sdisj hp hy.le (by lom) (.inr (by lom))
    · exact sdisj hp hy.le (by lom) (.inr (by lom))
    · exact papart hp hy hpo (by simp only [yOff]; omega)
  · exact p₂

/-! ## `u` and `v` -/

/-- Bytes of the ciphertext past those written so far. -/
theorem far_ct {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nU o l : Nat}
    (h : co + 32 * P.du * nU ≤ o) (f : o + l ≤ co + P.ctLen) :
    Far P L s₀ kC co P.k nU (R (kA s₀) (L.slot kC) o l) := by
  have hw := hp.wf
  have hb := hp.lt A.hkC
  have fC := A.fC
  have f' : o + l ≤ L.len (L.slot kC) := by omega
  have hs : ∀ {o' l' : Nat}, o' + l' ≤ CB P → L.slot kC ≠ L.sc ∨ o' + l' ≤ o ∨ o + l ≤ o' := fun h' => by
    rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inl (by subst hC; omega))
  have g : ∀ {o' l' : Nat}, o' + l' ≤ CB P → (R (kA s₀) L.sc o' l').Disjoint (R (kA s₀) (L.slot kC) o l) :=
    fun h' => hp.args.rdisj hp.scb hb (hp.fs (by lom)) f' (.inr (.inl hp.scw)) (by
      rcases hs h' with e | e
      · exact .inl (Ne.symm e)
      · exact .inr e)
  exact ⟨g (by lom), g (by lom), g (by lom), g (by lom),
    hp.args.rdisj hb hb (by omega) f' (.inl rfl) (.inr (.inl h)), ⟨_, by simp, R.sub2 (by omega) f⟩⟩

/-- `Â[j, i] ŷ[j]` into `h` (`TP` or `PP`). -/
theorem uprod_ok {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {i j h : Nat} (hi : i < P.k) (hj : j < P.k) (hh : h = TP P ∨ h = PP P)
    {s : State} (e : EInv P L s₀ kC co mE mB v rv mv P.k i s) :
    WP isa (mulAt h (aOff P j i) (yOff P j)) s fun s' => EInv P L s₀ kC co mE mB v rv mv P.k i s' ∧
      (∀ a, h = PP P → PolyIs s.mem (sA L s₀ (TP P)) a → PolyIs s'.mem (sA L s₀ (TP P)) a) ∧
      PolyIs s'.mem (sA L s₀ h) (multiplyNTTs (aM P L s₀ mB j i) (encY rv j)) := by
  have hw := hp.wf
  have hji := ij_lt hj hi
  have a₁ := e.a j hj i hi
  have y₁ := e.y j hj
  have ph : PO P h := by rcases hh with rfl | rfl; exacts [po_TP hw, po_PP hw]
  refine WP.mono (mul_ok hp ph (po_a hw hj hi) (po_y hw hj) (.inr (by rcases hh with rfl | rfl <;> lom))
    (.inr (by rcases hh with rfl | rfl <;> lom)) e.kb a₁.1 y₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_
  rw [a₁.2, y₁.2] at t₂
  refine ⟨e.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) (Nat.le_of_lt hi) (by rcases hh with rfl | rfl <;> lom)
    (by rcases hh with rfl | rfl <;> lom)), fun a ep ta => ?_, t₂⟩
  subst ep
  exact polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp (po_TP hw) (po_PP hw) (.inl (by lom))
    · exact pns hp (po_TP hw)) ta

/-- `TP ← TP + PP`. -/
theorem acc_TP {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {nU : Nat} (hnU : nU ≤ P.k) {s : State} {a b : Poly}
    (e : EInv P L s₀ kC co mE mB v rv mv P.k nU s) (ht : PolyIs s.mem (sA L s₀ (TP P)) a)
    (hq : PolyIs s.mem (sA L s₀ (PP P)) b) :
    WP isa (addAt (TP P) (PP P)) s fun s' => EInv P L s₀ kC co mE mB v rv mv P.k nU s' ∧
      PolyIs s'.mem (sA L s₀ (TP P)) (add a b) := by
  have hw := hp.wf
  refine WP.mono (add_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e.kb ht.1 hq.1) fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_
  rw [ht.2, hq.2] at t₃
  exact ⟨e.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) hnU (by lom) (by lom)), t₃⟩

theorem u_step {s₀ : State} (hp : Pre P L s₀) (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i < P.k) {s : State}
    (h : EInv P L s₀ kC co mE mB v rv mv P.k i s) :
    WP isa (P.encUAtWith keccak.callee (slotReg kC) co i) s (EInv P L s₀ kC co mE mB v rv mv P.k (i + 1)) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  have hn : i ≤ P.k := Nat.le_of_lt hi
  refine WPs.seqs (by simp) (WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P)
      (term := fun j h => [mulAt h (aOff P j i) (yOff P j)])
      (E := EInv P L s₀ kC co mE mB v rv mv P.k i)
      (T := fun s a => PolyIs s.mem (sA L s₀ (TP P)) a) (Q := fun s a => PolyIs s.mem (sA L s₀ (PP P)) a)
      (v := fun j => multiplyNTTs (aM P L s₀ mB j i) (encY rv j)) (N := P.k)
      (fun s e => WPs.single (WP.mono (uprod_ok hp A hi k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩))
      (fun j _ hj s a e t => WPs.single (WP.mono (uprod_ok hp A hi hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩))
      (fun s a b e t q => acc_TP hp A hn e t q) k1 (Nat.le_refl _) h) ?_))
  intro s₁ ⟨e₁, t₁⟩
  refine WPs.cons (WP.mono (nttInv_ok hp (po_TP hw) e₁.kb t₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₁.2] at t₂
  refine WPs.cons (WP.mono (prfCbd_ok hp (N := P.k + i) (by lom) (po_EP hw) e₂.kb e₂.r)
    fun s₃ ⟨kb₃, f₃, p₃, x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (far_pcW hp A (Nat.le_refl _) hn (by lom) (by lom))
  have t₃ := polyIs_frame f₃ (fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs (po_TP hw).le)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact papart hp (po_TP hw) (po_EP hw) (by lom)) t₂
  refine WPs.cons (WP.mono (add_ok hp (po_TP hw) (po_EP hw) (.inr (by lom)) e₃.kb t₃.1 p₃.1)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₃.2, p₃.2] at t₄
  have fC := A.fC
  have hu := du_le hi
  refine WPs.single (WP.mono (ceL_ok hp hc (off := TP P) (d := P.du) (k := kC) (o := co + 32 * P.du * i)
    (po_TP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅, f₅, b₅, x₅⟩ => ?_)
  have e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by lom)
  refine ⟨e₅.kb, e₅.x24, e₅.r, e₅.m, e₅.a, e₅.y, fun i' hi' => ?_, e₅.fr⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₅.u i' hi'
  · rw [b₅, t₄.2]; rfl

/-- `t̂[j] ŷ[j]` into `h` (`TP` or `PP`), with `t̂[j]` decoded into `TH`. -/
theorem vprod_ok {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀ j < P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {j h : Nat} (hj : j < P.k) (hh : h = TP P ∨ h = PP P) {s : State}
    (e : EInv P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WPs [dec12At (slotReg kE) (eo + 384 * j) (TH P), mulAt h (TH P) (yOff P j)] s fun s' =>
      EInv P L s₀ kC co mE mB v rv mv P.k P.k s' ∧
      (∀ a, h = PP P → PolyIs s.mem (sA L s₀ (TP P)) a → PolyIs s'.mem (sA L s₀ (TP P)) a) ∧
      PolyIs s'.mem (sA L s₀ h) (multiplyNTTs (T j) (encY rv j)) := by
  have hw := hp.wf
  have fE := A.fE
  have hs : L.slot kE ≠ L.sc := by have := A.rE; have := hp.scw; omega
  have hjE := mul_succ_le (a := 384) hj
  refine WPs.cons (WP.mono (dec12_ok hp (k := kE) (o := eo + 384 * j) A.hkE (by omega) (po_TH hw) (.inl hs) e.kb)
    fun s₁ ⟨kb₁, f₁, d₁, x₁⟩ => ?_)
  have e₁ := e.frame hp kb₁ x₁ f₁ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [e.kb.ro_bytes A.rE (by omega), hT j hj] at d₁
  have y₁ := e₁.y j hj
  have ph : PO P h := by rcases hh with rfl | rfl; exacts [po_TP hw, po_PP hw]
  refine WPs.single (WP.mono (mul_ok hp ph (po_TH hw) (po_y hw hj) (.inl (by rcases hh with rfl | rfl <;> lom))
    (.inr (by rcases hh with rfl | rfl <;> lom)) e₁.kb d₁.1 y₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  rw [d₁.2, y₁.2] at t₂
  refine ⟨e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _)
    (by rcases hh with rfl | rfl <;> lom) (by rcases hh with rfl | rfl <;> lom)), fun a ep ta => ?_, t₂⟩
  subst ep
  refine polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact papart hp (po_TP hw) (po_PP hw) (.inl (by lom))
    · exact pns hp (po_TP hw)) (polyIs_frame f₁ (fun r hr => ?_) ta)
  rw [List.mem_singleton.mp hr]; exact papart hp (po_TP hw) (po_TH hw) (.inl (by lom))

/-- `v`. -/
abbrev vPoly (P : KemLay) (T : Nat → Poly) (rv mv : List Byte) : Poly :=
  add (add (nttInv (KPke.dotK T (encY rv) P.k)) (cbd rv (2 * P.k))) (decodeDecompress 1 mv)

theorem v_ok {s₀ : State} (hp : Pre P L s₀) (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀ j < P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {s : State} (h : EInv P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WP isa (P.encVAtWith keccak.callee (slotReg kE) eo .x28 MB (slotReg kC) co) s fun s' =>
      EInv P L s₀ kC co mE mB v rv mv P.k P.k s' ∧
      bytesAt s'.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * P.k)) (32 * P.dv) =
        compressEncode P.dv (vPoly P T rv mv) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (by simp) (WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P)
      (term := fun j h => [dec12At (slotReg kE) (eo + 384 * j) (TH P), mulAt h (TH P) (yOff P j)])
      (E := EInv P L s₀ kC co mE mB v rv mv P.k P.k)
      (T := fun s a => PolyIs s.mem (sA L s₀ (TP P)) a) (Q := fun s a => PolyIs s.mem (sA L s₀ (PP P)) a)
      (v := fun j => multiplyNTTs (T j) (encY rv j)) (N := P.k)
      (fun s e => WPs.mono (vprod_ok hp A hT k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩)
      (fun j _ hj s a e t => WPs.mono (vprod_ok hp A hT hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩)
      (fun s a b e t q => acc_TP hp A (Nat.le_refl _) e t q) k1 (Nat.le_refl _) h) ?_))
  intro s₀' ⟨e₀, t₀⟩
  refine WPs.cons (WP.mono (nttInv_ok hp (po_TP hw) e₀.kb t₀.1) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := e₀.frame hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  refine WPs.cons (WP.mono (prfCbd_ok hp (N := 2 * P.k) (by lom) (po_EP hw) e₁.kb e₁.r)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_pcW hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have fTP : ∀ r ∈ pcW L s₀ (EP P), (polyRegion (sA L s₀ (TP P))).Disjoint r := fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs (po_TP hw).le)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact papart hp (po_TP hw) (po_EP hw) (by lom)
  have t₂ := polyIs_frame f₂ fTP t₁
  refine WPs.cons (WP.mono (add_ok hp (po_TP hw) (po_EP hw) (.inr (by lom)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (po_EP hw) (.inr (.inl (by lom))) e₃.kb)
    fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_TP hw) (po_EP hw) (by lom)) t₃
  have hm : bytesAt s₃.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₃.m
  rw [hm] at p₄
  refine WPs.cons (WP.mono (add_ok hp (po_TP hw) (po_EP hw) (.inr (by lom)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame hp kb₅ x₅ f₅ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₄.2, p₄.2] at t₅
  have fC := A.fC
  have hmk := Nat.mul_assoc 32 P.du P.k
  refine WPs.single (WP.mono (ceL_ok hp hc (off := TP P) (d := P.dv) (k := kC) (o := co + 32 * P.du * P.k)
    (po_TP hw) (.inr rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₅.kb t₅.1) fun s₆ ⟨kb₆, f₆, b₆, x₆⟩ => ?_)
  refine ⟨e₅.frame hp kb₆ x₆ f₆ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by lom), ?_⟩
  rw [b₆, t₅.2]

/-- `ŷ`, `u` and `v`. -/
theorem encrypt_ok {s₀ : State} (hp : Pre P L s₀) (hc : Calls P) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀ j < P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {s : State} (h : EInv P L s₀ kC co mE mB v rv mv 0 0 s) :
    WP isa (P.encryptCWith keccak.callee (slotReg kE) eo .x28 MB (slotReg kC) co) s fun s' =>
      EInv P L s₀ kC co mE mB v rv mv P.k P.k s' ∧
      bytesAt s'.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * P.k)) (32 * P.dv) =
        compressEncode P.dv (vPoly P T rv mv) := by
  refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (WPs.range
    (I := fun j => EInv P L s₀ kC co mE mB v rv mv j 0) (fun j hj _ h => y_step hp A hj h) h) fun s₁ h₁ =>
    WPs.mono (WPs.range (I := EInv P L s₀ kC co mE mB v rv mv P.k) (fun i hi _ h => u_step hp hc A hi h) h₁)
      fun s₂ h₂ => WPs.single (v_ok hp hc A hT h₂))))

/-- The ciphertext's bytes. -/
theorem ct_at {m : Mem} {p : Addr} {U : Nat → List Byte} {V : List Byte}
    (hu : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (32 * P.du * i)) (32 * P.du) = U i)
    (hv : bytesAt m (p + BitVec.ofNat 64 (32 * P.du * P.k)) (32 * P.dv) = V) :
    bytesAt m p P.ctLen = KPke.catK U P.k ++ V := by
  have cat : ∀ n, n ≤ P.k → bytesAt m p (32 * P.du * n) = KPke.catK U n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Nat.mul_succ, bytesAt_add, ih (by omega), hu n (by omega)]
      exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm
  rw [show P.ctLen = 32 * P.du * P.k + 32 * P.dv by simp only [KemLay.ctLen]; rw [Nat.mul_add, Nat.mul_assoc],
    bytesAt_add, cat P.k (Nat.le_refl _), hv]

end VG.Proof.MlKem.AArch64.Kem
