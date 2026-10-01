import VerifiedGarbage.Proof.MlKem1024.AArch64.KgT
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`, the end

Untrusted: everything here is checked by Lean. The copies of `ρ` into `ek`
and `dk`, `H(ek)` into `dk`, the copy of `z`, and our caller's registers
back (`end_ok`); then the bytes of `ek` and `dk` as the standard puts them
together (`ek_at`, `dk_at`).
-/

namespace VG.Proof.MlKem1024.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KG VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32)
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

/-- Four encoded polynomials at `p`. -/
theorem four_at {m : Mem} {p : Addr} {T : Nat → Poly}
    (h : ∀ i < 4, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i)) :
    bytesAt m p 1536 = encode12 (T 0) ++ encode12 (T 1) ++ encode12 (T 2) ++ encode12 (T 3) := by
  have h0 := h 0 (by decide)
  rw [Nat.mul_zero, ptr_zero] at h0
  have h1 : bytesAt m (p + BitVec.ofNat 64 384) 384 = encode12 (T 1) := h 1 (by decide)
  have h2 : bytesAt m (p + BitVec.ofNat 64 (384 + 384)) 384 = encode12 (T 2) := h 2 (by decide)
  have h3 : bytesAt m (p + BitVec.ofNat 64 (384 + 384 + 384)) 384 = encode12 (T 3) := h 3 (by decide)
  rw [show (1536 : Nat) = 384 + 384 + 384 + 384 from rfl, bytesAt_add, bytesAt_add, bytesAt_add, h0, h1, h2,
    h3]

/-- `ek`'s bytes: the four `t̂[i]` and `ρ`, at `p`. -/
theorem ek_at {m : Mem} {p : Addr} {T : Nat → Poly} {ρ : List Byte}
    (h : ∀ i < 4, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i))
    (hr : bytesAt m (p + BitVec.ofNat 64 1536) 32 = ρ) :
    bytesAt m p 1568 = encode12 (T 0) ++ encode12 (T 1) ++ encode12 (T 2) ++ encode12 (T 3) ++ ρ := by
  rw [show (1568 : Nat) = 1536 + 32 from rfl, bytesAt_add, four_at h, hr]

/-- `dk`'s bytes: `dk_PKE ‖ ek ‖ h ‖ z`, at `p`. -/
theorem dk_at {m : Mem} {p : Addr} {a b c d : List Byte} (ha : bytesAt m p 1536 = a)
    (hb : bytesAt m (p + BitVec.ofNat 64 1536) 1568 = b) (hc : bytesAt m (p + BitVec.ofNat 64 3104) 32 = c)
    (hd : bytesAt m (p + BitVec.ofNat 64 3136) 32 = d) : bytesAt m p 3168 = a ++ b ++ c ++ d := by
  have hc' : bytesAt m (p + BitVec.ofNat 64 (1536 + 1568)) 32 = c := hc
  have hd' : bytesAt m (p + BitVec.ofNat 64 (1536 + 1568 + 32)) 32 = d := hd
  rw [show (3168 : Nat) = 1536 + 1568 + 32 + 32 from rfl, bytesAt_add, bytesAt_add, bytesAt_add, ha, hb, hc',
    hd']

/-! ## Regions -/

/-- A buffer apart from what `TL i` describes. -/
theorem apart_R {s₀ : State} (hp : Pre s₀) {i b o l : Nat} (hi : i ≤ 4) (hb : b < 4) (f : o + l ≤ kL b)
    (h3 : b = 3 → o + l ≤ 840 ∨ 24608 ≤ o) (h1 : b = 1 → 384 * i ≤ o) (h2 : b = 2 → 1536 + 384 * i ≤ o) :
    Apart s₀ i (R (kA s₀) b o l) := by
  have hi' : 0 + 384 * i ≤ kL 1 := by simp only [kL]; omega
  have hi'' : 0 + (1536 + 384 * i) ≤ kL 2 := by simp only [kL]; omega
  refine ⟨hp.args.rdisj (by decide) hb (by decide) f ?_, hp.args.rdisj (by decide) hb (by decide) f ?_,
    hp.args.rdisj (by decide) hb (by decide) f ?_, hp.args.rdisj (by decide) hb hi' f ?_,
    hp.args.rdisj (by decide) hb hi'' f ?_⟩ <;>
  · by_cases e : b = 3
    · have := h3 e; subst e; offs4; omega
    · by_cases e1 : b = 1
      · have := h1 e1; subst e1; offs4; omega
      · by_cases e2 : b = 2
        · have := h2 e2; subst e2; offs4; omega
        · offs4; omega

theorem apart_below {s₀ : State} (hp : Pre s₀) (i : Nat) (hi : i ≤ 4) : Apart s₀ i (below s₀.sp 16) :=
  ⟨below_R hp (by decide) (by decide), below_R hp (by decide) (by decide), below_R hp (by decide) (by decide),
    below_R hp (by decide) (by simp only [kL]; omega), below_R hp (by decide) (by simp only [kL]; omega)⟩

/-! ## The end -/

/-- What the function leaves. -/
structure Done (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : GprAbi s₀ s
  x0 : s.gpr .x0 = v
  ek : bytesAt s.mem (kA s₀ 1) 1568 = ekPKE1024 (aM s₀ mB) (dB s₀)
  dk : bytesAt s.mem (kA s₀ 2) 3168 =
    dkPKE1024 (dB s₀) ++ ekPKE1024 (aM s₀ mB) (dB s₀) ++ H (ekPKE1024 (aM s₀ mB) (dB s₀)) ++ zB s₀

theorem pres_own : ∀ r ∈ preserved, r ∉ own → r ∉ [Reg.x0, .x30, .x24, .x25, .x26, .x27, .x28] := by decide

/-- Our caller's registers back, and the result. -/
theorem restore_ok {s₀ : State} (hp : Pre s₀) {u : State} (hk : KB s₀ u) :
    WP isa (.block [mov .x0 .x24, .ldr .x .x30 .x28 (SV + 40), .ldr .x .x24 .x28 SV,
      .ldr .x .x25 .x28 (SV + 8), .ldr .x .x26 .x28 (SV + 16), .ldr .x .x27 .x28 (SV + 24),
      .ldr .x .x28 .x28 (SV + 32)]) u fun u' =>
      GprAbi s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have cv := cov_r hp hk (b := 3) (o := SV) (l := 48) (by decide) (by decide)
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV + 8 * k) = kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * k)) 8 ∧
      w.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = s₀.gpr (own.getD k .x0) :=
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
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * 5)) (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * 0)) (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * 1)) (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * 2)) (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * 3)) (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * 4)) (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp]⟩, ?_, o₇.mem⟩
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
structure EndInv (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  tl : TL s₀ mB v 4 s
  rek : bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 1536) 32 = rhoK s₀
  rdk : bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 3072) 32 = rhoK s₀

/-- A region apart from what `EndInv` describes. -/
abbrev Far (s₀ : State) (r : Region) : Prop :=
  Apart s₀ 4 r ∧ (R (kA s₀) 1 1536 32).Disjoint r ∧ (R (kA s₀) 2 3072 32).Disjoint r

theorem EndInv.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {s s' : State} (h : EndInv s₀ mB v s)
    (hk : KB s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, Far s₀ r) : EndInv s₀ mB v s' :=
  ⟨h.tl.frame (Nat.le_refl _) hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem far_R {s₀ : State} (hp : Pre s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b)
    (h3 : b = 3 → o + l ≤ 840 ∨ 24608 ≤ o) (h1 : b ≠ 1) (h2 : b = 2 → 3104 ≤ o) :
    Far s₀ (R (kA s₀) b o l) :=
  ⟨apart_R hp (Nat.le_refl _) hb f h3 (fun e => absurd e h1) (fun e => by have := h2 e; omega),
    hp.args.rdisj (by decide) hb (by decide) f (.inl (Ne.symm h1)),
    hp.args.rdisj (by decide) hb (by decide) f (by
      by_cases e : b = 2
      · have := h2 e; subst e; omega
      · exact .inl (Ne.symm e))⟩

theorem far_below {s₀ : State} (hp : Pre s₀) : Far s₀ (below s₀.sp 16) :=
  ⟨apart_below hp 4 (Nat.le_refl _), below_R hp (by decide) (by decide), below_R hp (by decide) (by decide)⟩

/-- `ρ` into `ek` and `dk`. -/
theorem rho_ok {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL s₀ mB v 4 s) :
    WP isa (.block (copy32 .x28 SB .x26 1536 ++ copy32 .x28 SB .x27 3072)) s fun s' =>
      KB s₀ s' ∧ EndInv s₀ mB v s' := by
  have kb := h.c.kb
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 1) (so := SB) (dO := 1536) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide))
    kb.x28 kb.x26 (cov_r hp kb (b := 3) (by decide) (by decide))
    (cov_w hp kb (b := 1) (by decide) (by decide))) fun sa ⟨ka, fa, ba⟩ => ?_
  have kba := kb.frame ka fa (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 1) (o := 1536) (l := 32) (by decide) (by decide) (by decide) (by decide)
  have tla := h.frame (Nat.le_refl _) kba (ka.get .x24) fa fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 1) (o := 1536) (l := 32) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := SB) (dO := 3072) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide))
    kba.x28 kba.x27 (cov_r hp kba (b := 3) (by decide) (by decide))
    (cov_w hp kba (b := 2) (by decide) (by decide))) fun sb ⟨kb', fb, bb⟩ => ?_
  have kbb := kba.frame kb' fb (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 3072) (l := 32) (by decide) (by decide) (by decide) (by decide)
  refine ⟨kbb, tla.frame (Nat.le_refl _) kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 2) (o := 3072) (l := 32) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)), ?_, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)]
    exact h.c.rho

/-- `H(ek)` into `dk`. -/
theorem hek_ok {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {s : State} (kb : KB s₀ s)
    (h : EndInv s₀ mB v s) :
    WP isa (hash .x28 ST WK 136 6 [⟨.x26, 0, 1568⟩] [⟨.x27, 3104, 32⟩]) s fun s' =>
      KB s₀ s' ∧ EndInv s₀ mB v s' ∧
      bytesAt s'.mem (kA s₀ 2 + BitVec.ofNat 64 3104) 32 = H (ekPKE1024 (aM s₀ mB) (dB s₀)) := by
  have e28 : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by rw [kb.x28]
  refine WP.mono (hash_ok (hsetup hp kb (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x26, 0, 1568⟩]) (outs := [⟨.x27, 3104, 32⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 1) hp kb (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 2) hp kb (by decide) (by decide) (by decide) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ?_
  have kb' := kb.hash hp k' fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨2, 3104, 32, rfl, by decide, by decide, by decide, by decide⟩
  have msg : (List.map (pbytes s) [⟨.x26, 0, 1568⟩]).flatten = ekPKE1024 (aM s₀ mB) (dB s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb.x26, ptr_zero]
    exact ek_at (T := tV s₀ mB) (ρ := rhoK s₀) (fun i hi => (h.tl.ek i hi).1) h.rek
  obtain ⟨o, -⟩ := o'
  rw [msg, kb.x27] at o
  refine ⟨kb', h.frame kb' (k'.cs _ (by decide) (by decide)) k'.frame fun r hr => ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil] at hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.AArch64.STr, e28]
      exact far_R hp (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [VG.Proof.MlKem.AArch64.WKr, e28]
      exact far_R hp (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [kb.sp]; exact far_below hp
    · simp only [preg, kb.x27]
      exact far_R hp (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [o, H_eq]; rfl

/-- `z` into `dk`, and the rest. -/
theorem end_ok {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL s₀ mB v 4 s) :
    WP isa kgEnd s (Done s₀ mB v) := by
  refine WP.seq (WP.mono (rho_ok hp h) fun s₁ ⟨kb₁, h₁⟩ => WP.seq (WP.mono (hek_ok hp kb₁ h₁)
    fun s₂ ⟨kb₂, h₂, hh₂⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 3136) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by decide))
    (cov_w hp kb₂ (b := 2) (by decide) (by decide))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 3136) (l := 32) (by decide) (by decide) (by decide) (by decide)
  have far₃ : ∀ r ∈ [R (kA s₀) 2 3136 32], Far s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by decide) (by decide) (by decide) (by decide)
  have h₃ := h₂.frame kb₃ (k₃.get .x24) f₃ far₃
  have hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 3104) 32 = H (ekPKE1024 (aM s₀ mB) (dB s₀)) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 3136) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (kA s₀ 1) 1568 = ekPKE1024 (aM s₀ mB) (dB s₀) :=
    ek_at (T := tV s₀ mB) (ρ := rhoK s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (kA s₀ 2) 3168 =
      dkPKE1024 (dB s₀) ++ ekPKE1024 (aM s₀ mB) (dB s₀) ++ H (ekPKE1024 (aM s₀ mB) (dB s₀)) ++ zB s₀ :=
    dk_at (four_at (T := kgS1024 (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tV s₀ mB) (ρ := rhoK s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

end VG.Proof.MlKem1024.AArch64.KeyGen
