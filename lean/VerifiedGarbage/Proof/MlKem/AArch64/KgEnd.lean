import VerifiedGarbage.Proof.MlKem.AArch64.KgT
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on AArch64: `keygen`, the end

The copies of `ρ` into `ek` and `dk`, `H(ek)` into `dk`, the copy of `z`, and
our caller's registers back (`end_ok`); then the bytes of `ek` and `dk` as the
standard puts them together (`ek_at`, `dk_at`).
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-! ## Copies of 32 bytes -/

theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    (m.readW a 64).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

theorem writeW64_byte (m : Mem) (a : Addr) (v : BitVec 64) {i : Nat} (hi : i < 8) :
    m.writeW a v (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega),
    show i < 64 / 8 by omega, ite_true]
  rfl

theorem writeW64_off (m : Mem) (a x : Addr) (v : BitVec 64) (h : ¬ (x - a).toNat < 8) :
    m.writeW a v x = m x := Mem.write_apply h

/-- The 32 bytes at `S + so` copied to `D + dO`, through `x9`. -/
theorem copy_ok {S D : Addr} {sb db : Reg} {so dO : Nat} (hs9 : sb ≠ .x9) (hd9 : db ≠ .x9)
    (hso : so % 8 = 0 ∧ so + 32 ≤ 32768) (hdo : dO % 8 = 0 ∧ dO + 32 ≤ 32768)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 32⟩ ⟨D + BitVec.ofNat 64 dO, 32⟩)
    {s : State} (hS : s.gpr sb = S) (hD : s.gpr db = D)
    (hin : Covers [⟨S + BitVec.ofNat 64 so, 32⟩] (s.rd ++ s.wr))
    (hout : Covers [⟨D + BitVec.ofNat 64 dO, 32⟩] s.wr) :
    WP isa (.block (copy32 sb so db dO)) s fun s' => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (D + BitVec.ofNat 64 dO) 32 = bytesAt s.mem (S + BitVec.ofNat 64 so) 32 := by
  have n9s : sb ∉ [Reg.x9] := by simpa using hs9
  have n9d : db ∉ [Reg.x9] := by simpa using hd9
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k (s' : State) => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 32⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (D + BitVec.ofNat 64 (dO + i)) = s.mem (S + BitVec.ofNat 64 (so + i)))
    (fun k s₁ hk ⟨k₁, f₁, b₁⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ =>
      ⟨k', f', ?_⟩
  · refine wp_ldrx (a := S + BitVec.ofNat 64 (so + 8 * k)) ⟨by omega, by omega⟩ (by rw [k₁.get sb n9s, hS])
      (by rw [k₁.rd, k₁.wr]; exact in_R (A := fun _ => S) (b := 0) hin (k := 8 * k) (by omega) (by decide))
      fun s₂ h₂ e₂ => wp_strx (a := D + BitVec.ofNat 64 (dO + 8 * k)) ⟨by omega, by omega⟩
      (by rw [h₂.get db n9d, k₁.get db n9d, hD])
      (by rw [h₂.wr, k₁.wr]; exact in_R (A := fun _ => D) (b := 0) hout (k := 8 * k) (by omega) (by decide))
      fun s₃ h₃ => wp_nil ?_
    have m₃ : s₃.mem = s₁.mem.writeW (D + BitVec.ofNat 64 (dO + 8 * k))
        (s₁.mem.readW (S + BitVec.ofNat 64 (so + 8 * k)) 64) := by
      rw [h₃.mem, e₂, h₂.mem]
    refine ⟨((k₁.trans h₂.keep).trans h₃.keep).mono, ?_, fun i hi => ?_⟩
    · rw [m₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [← ptr_add]; exact contains_off (by omega) (by decide))
    · rw [m₃]
      rcases (by omega : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [writeW64_off _ _ _ _ (sep_off D (a := dO + i) (n := 1) (b := dO + 8 * k) (k := 8) (by omega)
          (by omega) (by omega) _ (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · rw [show D + BitVec.ofNat 64 (dO + i) = D + BitVec.ofNat 64 (dO + 8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show dO + 8 * k + (i - 8 * k) = dO + i by omega], writeW64_byte _ _ _ (by omega),
          readW64_byte _ _ (by omega), ptr_add, show so + 8 * k + (i - 8 * k) = so + i by omega]
        refine f₁ _ fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact hsep _ (R.contains (A := fun _ => S) (b := 0) (k := i) (n := 1) (by omega) (by decide)) hc
  · refine List.ext_getElem (by simp only [bytesAt_length]) fun i h₁ _ => ?_
    rw [bytesAt_length] at h₁
    rw [bytesAt_getElem, bytesAt_getElem, ptr_add, ptr_add]
    exact b' i (by omega)

/-! ## The bytes of `ek` and `dk` -/

/-- `n` encoded polynomials at `p`. -/
theorem cat_at {m : Mem} {p : Addr} {T : Nat → Poly} : ∀ {n : Nat},
    (∀ i < n, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i)) →
    bytesAt m p (384 * n) = KPke.catK (fun i => encode12 (T i)) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [Nat.mul_succ, bytesAt_add, cat_at fun i hi => h i (by omega), h n (by omega)]
    exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm

variable {P : KemLay}

/-- `ek`'s bytes: the `k` `t̂[i]` and `ρ`, at `p`. -/
theorem ek_at {m : Mem} {p : Addr} {T : Nat → Poly} {ρ : List Byte}
    (h : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i))
    (hr : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) 32 = ρ) :
    bytesAt m p P.ekLen = KPke.catK (fun i => encode12 (T i)) P.k ++ ρ := by
  rw [KemLay.ekLen, bytesAt_add, cat_at h, hr]

/-- `dk`'s bytes: `dk_PKE ‖ ek ‖ h ‖ z`, at `p`. -/
theorem dk_at {m : Mem} {p : Addr} {a b c d : List Byte} (ha : bytesAt m p (384 * P.k) = a)
    (hb : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) P.ekLen = b)
    (hc : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 32)) 32 = c)
    (hd : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 64)) 32 = d) : bytesAt m p P.dkLen = a ++ b ++ c ++ d := by
  have hc' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen)) 32 = c := by
    rw [show 384 * P.k + P.ekLen = 768 * P.k + 32 by simp only [KemLay.ekLen]; omega]; exact hc
  have hd' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen + 32)) 32 = d := by
    rw [show 384 * P.k + P.ekLen + 32 = 768 * P.k + 64 by simp only [KemLay.ekLen]; omega]; exact hd
  rw [show P.dkLen = 384 * P.k + P.ekLen + 32 + 32 by simp only [KemLay.ekLen, KemLay.dkLen]; omega,
    bytesAt_add, bytesAt_add, bytesAt_add, ha, hb, hc', hd']

/-! ## Regions -/

/-- A buffer apart from what `TL i` describes. -/
theorem apart_R {s₀ : State} (hp : Pre P s₀) {i b o l : Nat} (hi : i ≤ P.k) (hb : b < 4) (f : o + l ≤ kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b = 1 → 384 * i ≤ o) (h2 : b = 2 → 384 * P.k + 384 * i ≤ o) :
    Apart P s₀ i (R (kA s₀) b o l) := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb (by kl) f ?_,
    hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb hi' f ?_,
    hp.args.rdisj (by decide) hb hi'' f ?_⟩ <;>
  · by_cases e : b = 3
    · have := h3 e; subst e; kl
    · by_cases e1 : b = 1
      · have := h1 e1; subst e1; kl
      · by_cases e2 : b = 2
        · have := h2 e2; subst e2; kl
        · kl

theorem apart_below {s₀ : State} (hp : Pre P s₀) (i : Nat) (hi : i ≤ P.k) : Apart P s₀ i (below s₀.sp 16) :=
  ⟨below_R hp (by decide) (by kl), below_R hp (by decide) (by kl), below_R hp (by decide) (by kl),
    below_R hp (by decide) (by kl), below_R hp (by decide) (by kl)⟩

/-! ## The end -/

/-- What the function leaves. -/
structure Done (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  ek : bytesAt s.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)
  dk : bytesAt s.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
    KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) ++ zB s₀

theorem pres_own : ∀ r ∈ preserved, r ∉ own → r ∉ [Reg.x0, .x30, .x24, .x25, .x26, .x27, .x28] := by decide

/-- Our caller's registers back, and the result. -/
theorem restore_ok {s₀ : State} (hp : Pre P s₀) {u : State} (hk : KB P s₀ u) :
    WP isa (.block [mov .x0 .x24, .ldr .x .x30 .x28 (SV P + 40), .ldr .x .x24 .x28 (SV P),
      .ldr .x .x25 .x28 (SV P + 8), .ldr .x .x26 .x28 (SV P + 16), .ldr .x .x27 .x28 (SV P + 24),
      .ldr .x .x28 .x28 (SV P + 32)]) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have hw := hp.wf
  have hsv : SV P % 8 = 0 ∧ SV P + 48 ≤ 32768 := by lom
  have cv := cov_r hp hk (b := 3) (o := SV P) (l := 48) (by decide) hp.sv
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV P + 8 * k) = kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 8 ∧
      w.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (own.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact in_R cv (by omega) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = kA s₀ 3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_mov fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 5)) (by kl) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 0)) (by kl) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 1)) (by kl) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 2)) (by kl) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 3)) (by kl) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 4)) (by kl) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp], fun r hr => (o₇.vcs r hr).trans (hk.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ own
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · rw [o₇.get r (pres_own r hr ho), hk.cs r hr ho]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁]

/-- What holds from the copies of `ρ` on. -/
structure EndInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  tl : TL P s₀ mB v P.k s
  rek : bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * P.k)) 32 = rhoK P s₀
  rdk : bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k)) 32 = rhoK P s₀

/-- A region apart from what `EndInv` describes. -/
abbrev Far (P : KemLay) (s₀ : State) (r : Region) : Prop :=
  Apart P s₀ P.k r ∧ (R (kA s₀) 1 (384 * P.k) 32).Disjoint r ∧ (R (kA s₀) 2 (768 * P.k) 32).Disjoint r

theorem EndInv.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s s' : State}
    (h : EndInv P s₀ mB v s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Far P s₀ r) : EndInv P s₀ mB v s' :=
  ⟨h.tl.frame hp hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem far_R {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b ≠ 1) (h2 : b = 2 → 768 * P.k + 32 ≤ o) :
    Far P s₀ (R (kA s₀) b o l) :=
  ⟨apart_R hp (Nat.le_refl _) hb f h3 (fun e => absurd e h1) (fun e => by have := h2 e; omega),
    hp.args.rdisj (by decide) hb (by kl) f (.inl (Ne.symm h1)),
    hp.args.rdisj (by decide) hb (by kl) f (by
      by_cases e : b = 2
      · have := h2 e; subst e; omega
      · exact .inl (Ne.symm e))⟩

theorem far_below {s₀ : State} (hp : Pre P s₀) : Far P s₀ (below s₀.sp 16) :=
  ⟨apart_below hp P.k (Nat.le_refl _), below_R hp (by decide) (by kl), below_R hp (by decide) (by kl)⟩

/-- `ρ` into `ek` and `dk`. -/
theorem rho_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL P s₀ mB v P.k s) :
    WP isa (.block (copy32 .x28 SB .x26 (384 * P.k) ++ copy32 .x28 SB .x27 (768 * P.k))) s fun s' =>
      KB P s₀ s' ∧ EndInv P s₀ mB v s' := by
  have hw := hp.wf
  have kb := h.c.kb
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 1) (so := SB) (dO := 384 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x26 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 1) (by decide) (by kl))) fun sa ⟨ka, fa, ba⟩ => ?_
  have kba := kb.frame ka fa (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 1) (o := 384 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have tla := h.frame hp kba (ka.get .x24) fa fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 1) (o := 384 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (fun _ => Nat.le_refl _) (by kl)
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := SB) (dO := 768 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kba.x28 kba.x27 (cov_r hp kba (b := 3) (by decide) (by kl))
    (cov_w hp kba (b := 2) (by decide) (by kl))) fun sb ⟨kb', fb, bb⟩ => ?_
  have kbb := kba.frame kb' fb (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  refine ⟨kbb, tla.frame hp kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 2) (o := 768 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (by kl) (fun _ => by omega)), ?_, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact h.c.rho

/-- `H(ek)` into `dk`. -/
theorem hek_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (kb : KB P s₀ s)
    (h : EndInv P s₀ mB v s) :
    WP isa (hashWith keccak.callee .x28 ST WK 136 6 [⟨.x26, 0, P.ekLen⟩] [⟨.x27, 768 * P.k + 32, 32⟩]) s
      fun s' => KB P s₀ s' ∧ EndInv P s₀ mB v s' ∧
      bytesAt s'.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
        H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) := by
  have hw := hp.wf
  have e28 : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by rw [kb.x28]
  refine WP.mono (hashWith_ok keccak (hsetup hp kb (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x26, 0, P.ekLen⟩]) (outs := [⟨.x27, 768 * P.k + 32, 32⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 1) hp kb (by decide) (by kl) (by decide) (by kl) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 2) hp kb (by decide) (by kl) (by kl) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ?_
  have kb' := kb.hash hp k' fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨2, 768 * P.k + 32, 32, rfl, by decide, by decide, by kl, .inl (by decide)⟩
  have msg : (List.map (pbytes s) [⟨.x26, 0, P.ekLen⟩]).flatten = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb.x26, ptr_zero]
    exact ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.tl.ek i hi).1) h.rek
  obtain ⟨o, -⟩ := o'
  rw [msg, kb.x27] at o
  refine ⟨kb', h.frame hp kb' (k'.cs _ (by decide) (by decide)) k'.frame fun r hr => ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil] at hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.AArch64.STr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [VG.Proof.MlKem.AArch64.WKr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [kb.sp]; exact far_below hp
    · simp only [preg, kb.x27]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  · rw [o, H_eq]; rfl

/-- `z` into `dk`, and the rest. -/
theorem end_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL P s₀ mB v P.k s) :
    WP isa (P.kgEndWith keccak.callee) s (Done P s₀ mB v) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (rho_ok hp h) fun s₁ ⟨kb₁, h₁⟩ => WP.seq (WP.mono (hek_ok hp kb₁ h₁)
    fun s₂ ⟨kb₂, h₂, hh₂⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have far₃ : ∀ r ∈ [R (kA s₀) 2 (768 * P.k + 64) 32], Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  have h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  have hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
      H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) :=
    ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

end VG.Proof.MlKem.AArch64.KeyGen
