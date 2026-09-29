import VerifiedGarbage.Proof.MlKem1024.AArch64.KgC2

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`, `t̂`

Untrusted: everything here is checked by Lean. `ê[i]`, `t̂[i]` and its
encodings (`t_step`), keeping the facts established before (`TL`), which
every buffer the step writes is apart from (`Apart`).
-/

namespace VG.Proof.MlKem1024.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KG VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- `Â[i, j]` as the matrix left it. -/
abbrev aM (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAt mB (AR s₀ (4 * i + j))

/-- `t̂[i]`. -/
abbrev tV (s₀ : State) (mB : Mem) (i : Nat) : Poly := kgT1024 (aM s₀ mB) (dB s₀) i

/-- After `t̂[i']` for `i' < i`. -/
structure TL (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  c : CInv s₀ mB v s
  sp : ∀ j < 4, PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff j)) (kgS1024 (dB s₀) j)
  dk : ∀ j < 4, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 = encode12 (kgS1024 (dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tV s₀ mB i') ∧
    bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (1536 + 384 * i')) 384 = encode12 (tV s₀ mB i')

/-- A region apart from what `TL i` describes. -/
def Apart (s₀ : State) (i : Nat) (r : Region) : Prop :=
  (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧ (R (kA s₀) 3 AH 20480).Disjoint r ∧
    (R (kA s₀) 1 0 (384 * i)).Disjoint r ∧ (R (kA s₀) 2 0 (1536 + 384 * i)).Disjoint r

theorem TL.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i ≤ 4) {s s' : State}
    (h : TL s₀ mB v i s) (hk : KB s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Apart s₀ i r) : TL s₀ mB v i s' := by
  refine ⟨h.c.frame hk hx hf fun r hr => ⟨(hW r hr).1, (hW r hr).2.1,
    (hW r hr).2.2.1.sub_left (R.sub2 (Nat.le_refl _) (by decide))⟩, fun j hj => ?_, fun j hj => ?_,
    fun i' hi' => ⟨?_, ?_⟩⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.1.sub_left (R.sub2 (by simp only [sOff, SH, AH]; omega)
      (by simp only [sOff, SH, AH]; omega))) (h.sp j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega) (by omega)))
      (by decide)]
    exact h.dk j hj
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left (R.sub2 (by omega) (by omega)))
      (by decide)]
    exact (h.ek i' hi').1
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega) (by omega)))
      (by decide)]
    exact (h.ek i' hi').2

/-- A buffer of `scratch` past `ŝ`, or the NTT's working space. -/
theorem apart_scr {s₀ : State} (hp : Pre s₀) {i o l : Nat} (hi : i < 4) (f : o + l ≤ kL 3)
    (h : 24608 ≤ o ∨ (o = 3104 ∧ l = 1024)) : Apart s₀ i (R (kA s₀) 3 o l) := by
  have hi' : 0 + 384 * i ≤ kL 1 := by simp only [kL]; omega
  have hi'' : 0 + (1536 + 384 * i) ≤ kL 2 := by simp only [kL]; omega
  refine ⟨hp.args.rdisj (by decide) (by decide) (by decide) f (by offs4; omega),
    hp.args.rdisj (by decide) (by decide) (by decide) f (by offs4; omega),
    hp.args.rdisj (by decide) (by decide) (by decide) f (by offs4; omega),
    hp.args.rdisj (by decide) (by decide) hi' f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) hi'' f (.inl (by decide))⟩

theorem apart_cnW {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) : ∀ r ∈ cnW s₀ EP, Apart s₀ i r := by
  have hi' : 0 + 384 * i ≤ kL 1 := by simp only [kL]; omega
  have hi'' : 0 + (1536 + 384 * i) ≤ kL 2 := by simp only [kL]; omega
  have ho : EP + 1024 ≤ kL 3 := by decide
  intro r hr
  exact ⟨cnW_apart hp (by decide) (by decide) (.inr (by offs4; omega)) ho r hr,
    cnW_apart hp (by decide) (by decide) (.inr (by offs4; omega)) ho r hr,
    cnW_apart hp (by decide) (by decide) (.inr (by offs4; omega)) ho r hr,
    cnW_apart hp (by decide) hi' (.inl (by decide)) ho r hr,
    cnW_apart hp (by decide) hi'' (.inl (by decide)) ho r hr⟩

theorem apart_ek {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) :
    Apart s₀ i (R (kA s₀) 1 (384 * i) 384) := by
  have f : 384 * i + 384 ≤ kL 1 := by simp only [kL]; omega
  refine ⟨hp.args.rdisj (by decide) (by decide) (by decide) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by decide) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by decide) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by simp only [kL]; omega) f (.inr (.inl (by omega))),
    hp.args.rdisj (by decide) (by decide) (by simp only [kL]; omega) f (.inl (by decide))⟩

theorem apart_dk {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) :
    Apart s₀ i (R (kA s₀) 2 (1536 + 384 * i) 384) := by
  have f : 1536 + 384 * i + 384 ≤ kL 2 := by simp only [kL]; omega
  refine ⟨hp.args.rdisj (by decide) (by decide) (by decide) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by decide) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by decide) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by simp only [kL]; omega) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by simp only [kL]; omega) f (.inr (.inl (by omega)))⟩

theorem po_a {i j : Nat} (hi : i < 4) (hj : j < 4) : PolyOff (aOff i j) :=
  ⟨by simp only [aOff]; omega, by simp only [aOff, AH, SV]; omega⟩
theorem po_s {j : Nat} (hj : j < 4) : PolyOff (sOff j) :=
  ⟨by simp only [sOff, SH, AH]; omega, by simp only [sOff, SH, SV]; omega⟩
theorem po_TP : PolyOff TP := ⟨by decide, by decide⟩
theorem po_PP : PolyOff PP := ⟨by decide, by decide⟩
theorem po_EP : PolyOff EP := ⟨by decide, by decide⟩

/-- `ê[i]`'s polynomial and `t̂[i]`'s are apart from what a product into `PP` writes. -/
theorem far_PP {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o = EP ∨ o = TP) :
    ∀ r ∈ [R (kA s₀) 3 PP 1024, R (kA s₀) 3 NS 1024], (polyRegion (kA s₀ 3 + BitVec.ofNat 64 o)).Disjoint r := by
  intro r hr
  rcases ho with rfl | rfl <;> rcases mem2' hr with rfl | rfl <;> rdisj4

theorem far_TP {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [R (kA s₀) 3 TP 1024, R (kA s₀) 3 NS 1024], (polyRegion (kA s₀ 3 + BitVec.ofNat 64 EP)).Disjoint r := by
  intro r hr
  rcases mem2' hr with rfl | rfl <;> rdisj4

theorem apart_mul {s₀ : State} (hp : Pre s₀) {i o : Nat} (hi : i < 4) (ho : o = TP ∨ o = PP) :
    ∀ r ∈ [R (kA s₀) 3 o 1024, R (kA s₀) 3 NS 1024], Apart s₀ i r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · rcases ho with rfl | rfl
    · exact apart_scr hp hi (by decide) (.inl (by decide))
    · exact apart_scr hp hi (by decide) (.inl (by decide))
  · exact apart_scr hp hi (by decide) (.inr ⟨rfl, rfl⟩)

theorem apart_TP {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 4) :
    ∀ r ∈ [R (kA s₀) 3 TP 1024], Apart s₀ i r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact apart_scr hp hi (by decide) (.inl (by decide))

/-- `ê[i]`, and `T = Â[i, 0] ŝ[0] + Â[i, 1] ŝ[1]`. -/
structure TMid (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  tl : TL s₀ mB v i s
  e : PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 EP) (kgE1024 (dB s₀) i)
  t : PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 TP)
    (add (multiplyNTTs (aM s₀ mB i 0) (kgS1024 (dB s₀) 0)) (multiplyNTTs (aM s₀ mB i 1) (kgS1024 (dB s₀) 1)))

theorem t_part1 {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < 4) {s : State}
    (h : TL s₀ mB v i s) {REST : Prog isa} {Q : State → Prop} (hR : ∀ s', TMid s₀ mB v i s' → WP isa REST s' Q) :
    WP isa (.seq (kgCbdNtt (4 + i) EP) <| .seq (kgMul TP (aOff i 0) (sOff 0)) <|
      .seq (kgMul PP (aOff i 1) (sOff 1)) <| .seq (kgAdd TP PP) REST) s Q := by
  refine WP.seq (WP.mono (cbdNtt_ok hp (N := 4 + i) (off := EP) (by omega) po_EP h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, e₁, x₁⟩ => ?_)
  have tl₁ := h.frame (Nat.le_of_lt hi) kb₁ x₁ f₁ (apart_cnW hp hi)
  have a₁ : Reduced s₁.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 0)) ∧
      polyAt s₁.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 0)) = polyAt mB (kA s₀ 3 + BitVec.ofNat 64 (aOff i 0)) :=
    tl₁.c.ahat (4 * i + 0) (by omega)
  have s₁0 := tl₁.sp 0 (by decide)
  refine WP.seq (WP.mono (mul_ok hp (h := TP) (f := aOff i 0) (g := sOff 0) po_TP (po_a hi (by decide))
    (po_s (by decide)) (.inr (by simp only [aOff, AH, TP]; omega)) (.inr (by decide)) kb₁ a₁.1 s₁0.1)
    fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  have tl₂ := tl₁.frame (Nat.le_of_lt hi) kb₂ x₂ f₂ (apart_mul hp hi (.inl rfl))
  have e₂ := polyIs_frame f₂ (far_TP hp) e₁
  rw [a₁.2, s₁0.2] at t₂
  have a₂ : Reduced s₂.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 1)) ∧
      polyAt s₂.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 1)) = polyAt mB (kA s₀ 3 + BitVec.ofNat 64 (aOff i 1)) :=
    tl₂.c.ahat (4 * i + 1) (by omega)
  have s₂1 := tl₂.sp 1 (by decide)
  refine WP.seq (WP.mono (mul_ok hp (h := PP) (f := aOff i 1) (g := sOff 1) po_PP (po_a hi (by decide))
    (po_s (by decide)) (.inr (by simp only [aOff, AH, PP]; omega)) (.inr (by decide)) kb₂ a₂.1 s₂1.1)
    fun s₃ ⟨kb₃, f₃, p₃, x₃⟩ => ?_)
  have tl₃ := tl₂.frame (Nat.le_of_lt hi) kb₃ x₃ f₃ (apart_mul hp hi (.inr rfl))
  have e₃ := polyIs_frame f₃ (far_PP hp (.inl rfl)) e₂
  have t₃ := polyIs_frame f₃ (far_PP hp (.inr rfl)) t₂
  rw [a₂.2, s₂1.2] at p₃
  refine WP.seq (WP.mono (add_ok hp (f := TP) (g := PP) po_TP po_PP (.inl (by decide)) kb₃ t₃.1 p₃.1)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  have tl₄ := tl₃.frame (Nat.le_of_lt hi) kb₄ x₄ f₄ (apart_TP hp hi)
  have e₄ := polyIs_frame f₄ (fun r hr => by rw [List.mem_singleton.mp hr]; rdisj4) e₃
  rw [t₃.2, p₃.2] at t₄
  exact hR s₄ ⟨tl₄, e₄, t₄⟩

/-- `ê[i]`, and `T = Â[i] ∘ ŝ`. -/
structure TMid2 (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  tl : TL s₀ mB v i s
  e : PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 EP) (kgE1024 (dB s₀) i)
  t : PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 TP) (dot4 (aM s₀ mB i) (kgS1024 (dB s₀)))

theorem t_part2 {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < 4) {s : State}
    (h : TMid s₀ mB v i s) {REST : Prog isa} {Q : State → Prop} (hR : ∀ s', TMid2 s₀ mB v i s' → WP isa REST s' Q) :
    WP isa (.seq (kgMul PP (aOff i 2) (sOff 2)) <| .seq (kgAdd TP PP) <|
      .seq (kgMul PP (aOff i 3) (sOff 3)) <| .seq (kgAdd TP PP) REST) s Q := by
  have a₅ : Reduced s.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 2)) ∧
      polyAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 2)) = polyAt mB (kA s₀ 3 + BitVec.ofNat 64 (aOff i 2)) :=
    h.tl.c.ahat (4 * i + 2) (by omega)
  have s2 := h.tl.sp 2 (by decide)
  refine WP.seq (WP.mono (mul_ok hp (h := PP) (f := aOff i 2) (g := sOff 2) po_PP (po_a hi (by decide))
    (po_s (by decide)) (.inr (by simp only [aOff, AH, PP]; omega)) (.inr (by decide)) h.tl.c.kb a₅.1 s2.1)
    fun s₅ ⟨kb₅, f₅, p₅, x₅⟩ => ?_)
  have tl₅ := h.tl.frame (Nat.le_of_lt hi) kb₅ x₅ f₅ (apart_mul hp hi (.inr rfl))
  have e₅ := polyIs_frame f₅ (far_PP hp (.inl rfl)) h.e
  have t₅ := polyIs_frame f₅ (far_PP hp (.inr rfl)) h.t
  rw [a₅.2, s2.2] at p₅
  refine WP.seq (WP.mono (add_ok hp (f := TP) (g := PP) po_TP po_PP (.inl (by decide)) kb₅ t₅.1 p₅.1)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  have tl₆ := tl₅.frame (Nat.le_of_lt hi) kb₆ x₆ f₆ (apart_TP hp hi)
  have e₆ := polyIs_frame f₆ (fun r hr => by rw [List.mem_singleton.mp hr]; rdisj4) e₅
  rw [t₅.2, p₅.2] at t₆
  have a₆ : Reduced s₆.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 3)) ∧
      polyAt s₆.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff i 3)) = polyAt mB (kA s₀ 3 + BitVec.ofNat 64 (aOff i 3)) :=
    tl₆.c.ahat (4 * i + 3) (by omega)
  have s3 := tl₆.sp 3 (by decide)
  refine WP.seq (WP.mono (mul_ok hp (h := PP) (f := aOff i 3) (g := sOff 3) po_PP (po_a hi (by decide))
    (po_s (by decide)) (.inr (by simp only [aOff, AH, PP]; omega)) (.inr (by decide)) kb₆ a₆.1 s3.1)
    fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  have tl₇ := tl₆.frame (Nat.le_of_lt hi) kb₇ x₇ f₇ (apart_mul hp hi (.inr rfl))
  have e₇ := polyIs_frame f₇ (far_PP hp (.inl rfl)) e₆
  have t₇ := polyIs_frame f₇ (far_PP hp (.inr rfl)) t₆
  rw [a₆.2, s3.2] at p₇
  refine WP.seq (WP.mono (add_ok hp (f := TP) (g := PP) po_TP po_PP (.inl (by decide)) kb₇ t₇.1 p₇.1)
    fun s₈ ⟨kb₈, f₈, t₈, x₈⟩ => ?_)
  have tl₈ := tl₇.frame (Nat.le_of_lt hi) kb₈ x₈ f₈ (apart_TP hp hi)
  have e₈ := polyIs_frame f₈ (fun r hr => by rw [List.mem_singleton.mp hr]; rdisj4) e₇
  rw [t₇.2, p₇.2] at t₈
  exact hR s₈ ⟨tl₈, e₈, t₈⟩

theorem t_part3 {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < 4) {s : State}
    (h : TMid2 s₀ mB v i s) :
    WP isa (.seq (kgAdd TP EP) <|
      .seq (kgEnc TP .x26 (384 * i)) (kgEnc TP .x27 (1536 + 384 * i))) s (TL s₀ mB v (i + 1)) := by
  refine WP.seq (WP.mono (add_ok hp (f := TP) (g := EP) po_TP po_EP (.inr (by decide)) h.tl.c.kb h.t.1 h.e.1)
    fun s₇ ⟨kb₇, f₇, t₇, x₇⟩ => ?_)
  have tl₇ := h.tl.frame (Nat.le_of_lt hi) kb₇ x₇ f₇ (apart_TP hp hi)
  rw [h.t.2, h.e.2] at t₇
  have tv : PolyIs s₇.mem (kA s₀ 3 + BitVec.ofNat 64 TP) (tV s₀ mB i) := t₇
  refine WP.seq (WP.mono (enc_ok hp (off := TP) (b := 1) (o := 384 * i) po_TP (.inl rfl)
    (by simp only [kL]; omega) kb₇ tv.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  have tl₈ := tl₇.frame (Nat.le_of_lt hi) kb₈ x₈ f₈ fun r hr => by rw [List.mem_singleton.mp hr]; exact apart_ek hp hi
  have tv₈ := polyIs_frame f₈ (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.args.rdisj (by decide) (by decide) (by decide) (by simp only [kL]; omega) (.inl (by decide))) tv
  refine WP.mono (enc_ok hp (off := TP) (b := 2) (o := 1536 + 384 * i) po_TP (.inr rfl)
    (by simp only [kL]; omega) kb₈ tv₈.1) fun s₉ ⟨kb₉, f₉, b₉, x₉⟩ => ?_
  have tl₉ := tl₈.frame (Nat.le_of_lt hi) kb₉ x₉ f₉ fun r hr => by rw [List.mem_singleton.mp hr]; exact apart_dk hp hi
  refine ⟨tl₉.c, tl₉.sp, tl₉.dk, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact tl₉.ek i' hi'
  · refine ⟨?_, by rw [b₉, tv₈.2]⟩
    rw [bytesAt_frame f₉ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by simp only [kL]; omega) (by simp only [kL]; omega)
        (.inl (by decide))) (by decide), b₈, tv.2]

theorem t_step {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < 4) {s : State}
    (h : TL s₀ mB v i s) : WP isa (Impl.MlKem1024.AArch64.kgT i) s (TL s₀ mB v (i + 1)) :=
  t_part1 hp hi h fun _ hm => t_part2 hp hi hm fun _ hm2 => t_part3 hp hi hm2

end VG.Proof.MlKem1024.AArch64.KeyGen
