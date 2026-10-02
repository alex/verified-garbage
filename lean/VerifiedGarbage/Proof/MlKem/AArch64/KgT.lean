import VerifiedGarbage.Proof.MlKem.AArch64.KgC2

/-!
# ML-KEM on AArch64: `keygen`, `t̂`

`ê[i]`, `t̂[i]` and its encodings (`t_step`), keeping the facts established
before (`TL`), which every buffer the step writes is apart from (`Apart`).
The sum of products in `t̂[i]` is a loop over `j < k` (`WPs.dot`).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `Â[i, j]` as the matrix left it. -/
abbrev aM (P : KemLay) (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAt mB (AR s₀ (P.k * i + j))

/-- `t̂[i]`. -/
abbrev tV (P : KemLay) (s₀ : State) (mB : Mem) (i : Nat) : Poly := KPke.kgT P.params (aM P s₀ mB) (dB s₀) i

/-- After `t̂[i']` for `i' < i`. -/
structure TL (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  c : CInv P s₀ mB v s
  sp : ∀ j < P.k, PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tV P s₀ mB i') ∧
    bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tV P s₀ mB i')

/-- A region apart from what `TL i` describes. -/
def Apart (P : KemLay) (s₀ : State) (i : Nat) (r : Region) : Prop :=
  (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
    (R (kA s₀) 3 AH (1024 * (P.k * P.k) + 1024 * P.k)).Disjoint r ∧
    (R (kA s₀) 1 0 (384 * i)).Disjoint r ∧ (R (kA s₀) 2 0 (384 * P.k + 384 * i)).Disjoint r

theorem TL.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} {s s' : State}
    (h : TL P s₀ mB v i s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Apart P s₀ i r) : TL P s₀ mB v i s' := by
  have hw := hp.wf
  refine ⟨h.c.frame hk hx hf fun r hr => ⟨(hW r hr).1, (hW r hr).2.1,
    (hW r hr).2.2.1.sub_left (R.sub2 (Nat.le_refl _) (by omega))⟩, fun j hj => ?_, fun j hj => ?_,
    fun i' hi' => ⟨?_, ?_⟩⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))) (h.sp j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega)
      (by have := mul_succ_le (a := 384) hj; omega))) (by decide)]
    exact h.dk j hj
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left (R.sub2 (by omega)
      (by have := mul_succ_le (a := 384) hi'; omega))) (by decide)]
    exact (h.ek i' hi').1
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega)
      (by have := mul_succ_le (a := 384) hi'; omega))) (by decide)]
    exact (h.ek i' hi').2

/-- A buffer of `scratch` past `ŝ`, or the NTT's working space. -/
theorem apart_scr {s₀ : State} (hp : Pre P s₀) {i o l : Nat} (hi : i < P.k) (f : o + l ≤ kL P 3)
    (h : EP P ≤ o ∨ (o = 3104 ∧ l = 1024)) : Apart P s₀ i (R (kA s₀) 3 o l) := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) hi' f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) hi'' f (.inl (by decide))⟩

theorem apart_cnW {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ cnW s₀ (EP P), Apart P s₀ i r := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  have ho : EP P + 1024 ≤ kL P 3 := by kl
  intro r hr
  exact ⟨cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    cnW_apart hp (by decide) hi' (.inl (by decide)) ho r hr,
    cnW_apart hp (by decide) hi'' (.inl (by decide)) ho r hr⟩

theorem apart_ek {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    Apart P s₀ i (R (kA s₀) 1 (384 * i) 384) := by
  have f : 384 * i + 384 ≤ kL P 1 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega))),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide))⟩

theorem apart_dk {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    Apart P s₀ i (R (kA s₀) 2 (384 * P.k + 384 * i) 384) := by
  have f : 384 * P.k + 384 * i + 384 ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega)))⟩

theorem po_a (hP : P.Wf) {i j : Nat} (hi : i < P.k) (hj : j < P.k) : PolyOff P (aOff P i j) :=
  have := ij_lt hi hj; ⟨by lom, by lom⟩
theorem po_s (hP : P.Wf) {j : Nat} (hj : j < P.k) : PolyOff P (sOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : PolyOff P (TP P) := ⟨by lom, by lom⟩
theorem po_PP (hP : P.Wf) : PolyOff P (PP P) := ⟨by lom, by lom⟩
theorem po_EP (hP : P.Wf) : PolyOff P (EP P) := ⟨by lom, by lom⟩

/-- `ê[i]`'s polynomial and `t̂[i]`'s are apart from what a product into `PP` writes. -/
theorem far_PP {s₀ : State} (hp : Pre P s₀) {o : Nat} (ho : o = EP P ∨ o = TP P) :
    ∀ r ∈ [R (kA s₀) 3 (PP P) 1024, R (kA s₀) 3 NS 1024],
      (polyRegion (kA s₀ 3 + BitVec.ofNat 64 o)).Disjoint r := by
  intro r hr
  rcases ho with rfl | rfl <;> rcases mem2' hr with rfl | rfl <;> rdisj

theorem far_TP {s₀ : State} (hp : Pre P s₀) :
    ∀ r ∈ [R (kA s₀) 3 (TP P) 1024, R (kA s₀) 3 NS 1024],
      (polyRegion (kA s₀ 3 + BitVec.ofNat 64 (EP P))).Disjoint r := by
  intro r hr
  rcases mem2' hr with rfl | rfl <;> rdisj

theorem apart_mul {s₀ : State} (hp : Pre P s₀) {i o : Nat} (hi : i < P.k) (ho : o = TP P ∨ o = PP P) :
    ∀ r ∈ [R (kA s₀) 3 o 1024, R (kA s₀) 3 NS 1024], Apart P s₀ i r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · rcases ho with rfl | rfl
    · exact apart_scr hp hi (by kl) (.inl (by kl))
    · exact apart_scr hp hi (by kl) (.inl (by kl))
  · exact apart_scr hp hi (by kl) (.inr ⟨rfl, rfl⟩)

theorem apart_TP {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ [R (kA s₀) 3 (TP P) 1024], Apart P s₀ i r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact apart_scr hp hi (by kl) (.inl (by kl))

/-- During `t̂[i]`: `TL i`, and `ê[i]` at `EP`. -/
abbrev TE (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop :=
  TL P s₀ mB v i s ∧ PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (EP P)) (KPke.kgE P.params (dB s₀) i)

/-- `Â[i, j] ŝ[j]` into `h` (`TP` or `PP`). -/
theorem prod_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i j h : Nat} (hi : i < P.k)
    (hj : j < P.k) (hh : h = TP P ∨ h = PP P) {s : State} (e : TE P s₀ mB v i s) :
    WP isa (kgMul h (aOff P i j) (sOff P j)) s fun s' => TE P s₀ mB v i s' ∧
      (∀ a, h = PP P → PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) a →
        PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) a) ∧
      PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 h)
        (multiplyNTTs (aM P s₀ mB i j) (KPke.kgS P.params (dB s₀) j)) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have a₁ : Reduced s.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) ∧
      polyAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) = polyAt mB (kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) :=
    e.1.c.ahat (P.k * i + j) hij
  have s₁ := e.1.sp j hj
  have ph : PolyOff P h := by rcases hh with rfl | rfl; exacts [po_TP hw, po_PP hw]
  refine WP.mono (mul_ok hp (h := h) (f := aOff P i j) (g := sOff P j) ph (po_a hw hi hj) (po_s hw hj)
    (.inr (by rcases hh with rfl | rfl <;> lom)) (.inr (by rcases hh with rfl | rfl <;> lom)) e.1.c.kb a₁.1 s₁.1)
    fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_
  rw [a₁.2, s₁.2] at t₂
  have ho : h = TP P ∨ h = PP P := hh
  refine ⟨⟨e.1.frame hp kb₂ x₂ f₂ (apart_mul hp hi hh),
    polyIs_frame f₂ (by rcases ho with rfl | rfl; exacts [far_TP hp, far_PP hp (.inl rfl)]) e.2⟩,
    fun a ep ta => ?_, t₂⟩
  subst ep
  exact polyIs_frame f₂ (far_PP hp (.inr rfl)) ta

theorem t_step {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) {s : State}
    (h : TL P s₀ mB v i s) : WP isa (P.kgTWith keccak.callee i) s (TL P s₀ mB v (i + 1)) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (List.cons_ne_nil _ _) (WPs.cons ?_)
  refine WP.mono (cbdNtt_ok hp (N := P.k + i) (off := EP P) (by lom) (po_EP hw) h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, e₁, x₁⟩ => ?_
  have te₁ : TE P s₀ mB v i s₁ := ⟨h.frame hp kb₁ x₁ f₁ (apart_cnW hp hi), e₁⟩
  refine WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P) (E := TE P s₀ mB v i)
      (term := fun j h => [kgMul h (aOff P i j) (sOff P j)])
      (T := fun s a => PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) a)
      (Q := fun s a => PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (PP P)) a)
      (v := fun j => multiplyNTTs (aM P s₀ mB i j) (KPke.kgS P.params (dB s₀) j)) (N := P.k)
      (fun s e => WPs.single (WP.mono (prod_ok hp hi k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩))
      (fun j _ hj s a e t => WPs.single (WP.mono (prod_ok hp hi hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩))
      (fun s a b e t q => WP.mono (add_ok hp (f := TP P) (g := PP P) (po_TP hw) (po_PP hw) (.inl (by lom))
        e.1.c.kb t.1 q.1) fun s' ⟨kb', f', t', x'⟩ => ⟨⟨e.1.frame hp kb' x' f' (apart_TP hp hi),
          polyIs_frame f' (fun r hr => by rw [List.mem_singleton.mp hr]; rdisj) e.2⟩, by rw [t.2, q.2] at t'; exact t'⟩)
      k1 (Nat.le_refl _) te₁) ?_)
  intro s₂ ⟨⟨tl₂, e₂⟩, t₂⟩
  refine WPs.cons (WP.mono (add_ok hp (f := TP P) (g := EP P) (po_TP hw) (po_EP hw) (.inr (by lom)) tl₂.c.kb
    t₂.1 e₂.1) fun s₇ ⟨kb₇, f₇, t₇, x₇⟩ => ?_)
  have tl₇ := tl₂.frame hp kb₇ x₇ f₇ (apart_TP hp hi)
  rw [t₂.2, e₂.2] at t₇
  have tv : PolyIs s₇.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) (tV P s₀ mB i) := t₇
  refine WPs.cons (WP.mono (enc_ok hp (off := TP P) (b := 1) (o := 384 * i) (po_TP hw) (.inl rfl)
    (by kl) kb₇ tv.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  have tl₈ := tl₇.frame hp kb₈ x₈ f₈ fun r hr => by rw [List.mem_singleton.mp hr]; exact apart_ek hp hi
  have tv₈ := polyIs_frame f₈ (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) tv
  refine WPs.single (WP.mono (enc_ok hp (off := TP P) (b := 2) (o := 384 * P.k + 384 * i) (po_TP hw) (.inr rfl)
    (by kl) kb₈ tv₈.1) fun s₉ ⟨kb₉, f₉, b₉, x₉⟩ => ?_)
  have tl₉ := tl₈.frame hp kb₉ x₉ f₉ fun r hr => by rw [List.mem_singleton.mp hr]; exact apart_dk hp hi
  refine ⟨tl₉.c, tl₉.sp, tl₉.dk, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact tl₉.ek i' hi'
  · refine ⟨?_, by rw [b₉, tv₈.2]⟩
    rw [bytesAt_frame f₉ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) (by decide), b₈, tv.2]

end VG.Proof.MlKem.AArch64.KeyGen
