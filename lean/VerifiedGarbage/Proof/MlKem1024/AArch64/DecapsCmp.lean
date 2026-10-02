import VerifiedGarbage.Proof.MlKem1024.AArch64.DecapsA

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_decaps`, the comparison and the key

`c = c'` as the OR of the bytes of `c ⊕ c'` being 0 (`cmp_ok`), without
branching, then a mask of ones exactly when they are equal, and `K'` or `K̄`
into `key` through it (`sel_ok`).
-/

namespace VG.Proof.MlKem1024.AArch64.Decaps

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KEM VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32 slotReg argReg kemOwn deCmpBody)
open VG.Proof.MlKem1024.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem1024.AArch64.KeyGen (readW64_byte writeW64_byte writeW64_off)

theorem sel_val (a b : BitVec 64) (e : Bool) :
    ((a ^^^ b) &&& (if e then (0 : BitVec 64) - 1 else 0)) ^^^ b = if e then a else b := by
  cases e
  · simp
  · simp only [ite_true]
    rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]

theorem mask_val (x : BitVec 64) (h : x.toNat < 256) :
    (0 : BitVec 64) - ((x - 1) >>> 63) = if x = 0 then (0 : BitVec 64) - 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have h1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hx
      · exact h0
    have : (x - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_lsr, toNat_sub_n (show (1 : BitVec 64).toNat ≤ x.toNat from h1)]
      show (x.toNat - 1) / 2 ^ 63 = 0
      omega
    rw [this]; rfl

theorem xor_zero_iff (a b : BitVec 8) : (a.setWidth 64 ^^^ b.setWidth 64 = 0) ↔ a = b := by
  constructor
  · intro h
    have h' := BitVec.xor_eq_zero_iff.mp h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
    exact this
  · intro h; rw [h]; exact BitVec.xor_self

theorem bytesAt_succ' (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  rw [bytesAt_add]
  refine congrArg (bytesAt m p k ++ ·) (bytesAt_eq rfl fun i hi => ?_)
  have : i = 0 := by omega
  subst this
  rw [ptr_zero]; rfl

/-! ## `c = c'` -/

/-- After `k` bytes of `c` (at `kA s₀ 1`) and `c'` (at `CB`). -/
structure CInv (s₀ s : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x0, .x1, .x2, .x9, .x10, .x11] s u
  mem : u.mem = s.mem
  x0 : u.gpr .x0 = kA s₀ 1 + BitVec.ofNat 64 k
  x1 : u.gpr .x1 = kA s₀ 3 + BitVec.ofNat 64 (CB + k)
  x2 : (u.gpr .x2).toNat = 1568 - k
  x10 : (u.gpr .x10).toNat < 256
  eq : u.gpr .x10 = 0 ↔ bytesAt s.mem (kA s₀ 1) k = bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 CB) k

theorem cstep {s₀ : State} (hp : Pre deL s₀) {s : State} (hk : KB deL s₀ s) {k : Nat} (hk' : k < 1568)
    {u : State} (h : CInv s₀ s k u) :
    WP isa (.block deCmpBody) u fun u' => CInv s₀ s (k + 1) u' ∧ ((u'.gpr .x2).toNat ≠ 0 ↔ k + 1 ≠ 1568) := by
  have hcr := cov_r hp hk (b := 1) (o := 0) (l := 1568) (by decide) (by decide)
  have hsr := cov_sr hp hk (o := CB) (l := 1568) (by decide)
  have in₁ : InRegions (u.rd ++ u.wr) (kA s₀ 1 + BitVec.ofNat 64 k) 1 := by
    rw [h.keep.rd, h.keep.wr]
    have := in_R hcr (k := k) (n := 1) (by omega) (by decide)
    rwa [Nat.zero_add] at this
  have in₂ : InRegions (u.rd ++ u.wr) (kA s₀ 3 + BitVec.ofNat 64 (CB + k)) 1 := by
    rw [h.keep.rd, h.keep.wr]
    exact in_R hsr (k := k) (n := 1) (by omega) (by decide)
  refine wp_ldrb (a := kA s₀ 1 + BitVec.ofNat 64 k) (by decide) (by rw [h.x0, ptr_zero]) in₁
    fun u₁ g₁ v₁ => ?_
  refine wp_ldrb (a := kA s₀ 3 + BitVec.ofNat 64 (CB + k)) (by decide)
    (by rw [g₁.get .x1, h.x1, ptr_zero]) (by rw [g₁.rd, g₁.wr]; exact in₂) fun u₂ g₂ v₂ => ?_
  refine wp_eor fun u₃ g₃ v₃ => wp_orr fun u₄ g₄ v₄ => wp_addImm (by decide) fun u₅ g₅ v₅ =>
    wp_addImm (by decide) fun u₆ g₆ v₆ => wp_subImm (by decide) fun u₇ g₇ v₇ => wp_nil ?_
  have o₇ : Only [.x0, .x1, .x2, .x9, .x10, .x11] u u₇ :=
    ((((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).trans g₆).trans g₇).mono
  have m₁ : u₁.mem = s.mem := by rw [g₁.mem, h.mem]
  have x9 : u₃.gpr .x9 = (s.mem (kA s₀ 1 + BitVec.ofNat 64 k)).setWidth 64 ^^^
      (s.mem (kA s₀ 3 + BitVec.ofNat 64 (CB + k))).setWidth 64 := by
    rw [v₃, g₂.get .x9, v₁, v₂, m₁, h.mem]
  have x10 : u₇.gpr .x10 = u.gpr .x10 ||| u₃.gpr .x9 := by
    rw [g₇.get .x10, g₆.get .x10, g₅.get .x10, v₄, g₃.get .x10, g₂.get .x10, g₁.get .x10]
  have x2 : u₇.gpr .x2 = u.gpr .x2 - BitVec.ofNat 64 1 := by
    rw [v₇, g₆.get .x2, g₅.get .x2, g₄.get .x2, g₃.get .x2, g₂.get .x2, g₁.get .x2]
  have hx2 : (u₇.gpr .x2).toNat = 1568 - (k + 1) := by
    rw [x2, toNat_sub_n (show (BitVec.ofNat 64 1).toNat ≤ (u.gpr .x2).toNat by
      rw [h.x2, BitVec.toNat_ofNat]; omega), h.x2, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨h.keep.trans o₇.keep |>.mono, by rw [o₇.mem, h.mem], ?_, ?_, hx2, ?_, ?_⟩, by rw [hx2]; omega⟩
  · rw [g₇.get .x0, g₆.get .x0, v₅, g₄.get .x0, g₃.get .x0, g₂.get .x0, g₁.get .x0, h.x0, ptr_add]
  · rw [g₇.get .x1, v₆, g₅.get .x1, g₄.get .x1, g₃.get .x1, g₂.get .x1, g₁.get .x1, h.x1, ptr_add,
      Nat.add_assoc]
  · rw [x10, BitVec.toNat_or, x9, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have a := (s.mem (kA s₀ 1 + BitVec.ofNat 64 k)).isLt
    have b := (s.mem (kA s₀ 3 + BitVec.ofNat 64 (CB + k))).isLt
    have c := h.x10
    exact Nat.or_lt_two_pow (n := 8) c (Nat.xor_lt_two_pow (by omega) (by omega))
  · have e1 : u.gpr .x10 ||| u₃.gpr .x9 = 0 ↔ u.gpr .x10 = 0 ∧ u₃.gpr .x9 = 0 := BitVec.or_eq_zero_iff
    rw [x10, e1, h.eq, x9, xor_zero_iff, bytesAt_succ', bytesAt_succ', ptr_add]
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro e
      obtain ⟨h1, h2⟩ := List.append_inj e (by rw [bytesAt_length, bytesAt_length])
      exact ⟨h1, List.head_eq_of_cons_eq h2⟩

theorem cmp_ok {s₀ : State} (hp : Pre deL s₀) {s : State} (hk : KB deL s₀ s) {c' : List Byte}
    (hc : bytesAt s.mem (sA deL s₀ CB) 1568 = c') :
    WP isa deCmp s fun s' => Keep [.x0, .x1, .x2, .x9, .x10, .x11] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .x10 = if cD s₀ = c' then (0 : BitVec 64) - 1 else 0 := by
  refine WP.seq ?_
  rw [List.append_assoc]
  refine wp_ptrTo (by decide) (by decide) fun s₁ h₁ e₁ => wp_ptrTo (by decide) (by decide)
    fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have o₄ : Only [.x0, .x1, .x2, .x9, .x10, .x11] s s₄ := (((h₁.trans h₂).trans h₃).trans h₄).mono
  have z : ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0 := by simp
  have c₀ : CInv s₀ s 0 s₄ :=
    ⟨o₄.keep, o₄.mem, by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, hk.x26]; rfl,
      by rw [h₄.get .x1, h₃.get .x1, e₂, h₁.get .x28, hk.x28]; rfl,
      by rw [h₄.get .x2, e₃]; simp, by rw [e₄, z]; decide,
      by rw [e₄, z]; exact ⟨fun _ => (List.eq_nil_of_length_eq_zero (bytesAt_length _ _ _)).trans
        (List.eq_nil_of_length_eq_zero (bytesAt_length _ _ _)).symm, fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (count_loop (n := 1568) (by decide) (CInv s₀ s) (fun k hk' u h => cstep hp hk hk' h)
    c₀) fun s₅ h₅ => ?_)
  refine wp_subImm (by decide) fun s₆ h₆ e₆ => wp_lsr (by decide) fun s₇ h₇ e₇ => wp_movz fun s₈ h₈ e₈ =>
    wp_sub fun s₉ h₉ e₉ => wp_nil ?_
  have o₉ : Only [.x10, .x11] s₅ s₉ := (((h₆.trans h₇).trans h₈).trans h₉).mono
  refine ⟨h₅.keep.trans o₉.keep |>.mono, by rw [o₉.mem, h₅.mem], ?_⟩
  have ex : (0 : BitVec 64) - ((s₅.gpr .x10 - 1) >>> 63) = s₉.gpr .x10 := by
    rw [e₉, h₈.get .x10, e₈, e₇, e₆]; rfl
  rw [← ex, mask_val _ h₅.x10]
  have hcD : bytesAt s.mem (kA s₀ 1) 1568 = cD s₀ := hk.ro (b := 1) (by decide)
  have he := h₅.eq
  rw [hcD, show kA s₀ 3 + BitVec.ofNat 64 CB = sA deL s₀ CB from rfl, hc] at he
  by_cases e : cD s₀ = c'
  · rw [ite_eq_left (he.mpr e), ite_eq_left e]
  · rw [ite_eq_right (fun h => e (he.mp h)), ite_eq_right e]

/-! ## The key -/

/-- `K'` (at `KP`) or `K̄` (at `JB`) into `key`. -/
theorem sel_ok {s₀ : State} (hp : Pre deL s₀) {s : State} (hk : KB deL s₀ s) {e : Bool}
    (hm : s.gpr .x10 = if e then (0 : BitVec 64) - 1 else 0) :
    WP isa (.block deSel) s fun s' => Keep [.x12, .x13] s s' ∧
      Frame [R (kA s₀) 2 0 32] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ 2) 32 = if e then bytesAt s.mem (sA deL s₀ KP) 32 else bytesAt s.mem (sA deL s₀ JB) 32 := by
  have hkr := cov_sr hp hk (o := KP) (l := 32) (by decide)
  have hjr := cov_sr hp hk (o := JB) (l := 32) (by decide)
  have hw := cov_w hp hk (b := 2) (o := 0) (l := 32) (by decide) (by decide)
  have sk : ∀ {o : Nat}, o + 32 ≤ 49152 → ∀ r ∈ [R (kA s₀) 2 0 32],
      (R (kA s₀) deL.sc o 32).Disjoint r := fun f r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.args.rdisj (by decide) (by decide) (by rw [hp.scl]; exact f) (by decide) (by decide)
      (.inl (by decide))
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k (u : State) => Keep [.x12, .x13] s u ∧
      Frame [R (kA s₀) 2 0 32] s.mem u.mem ∧
      ∀ i < 8 * k, u.mem (kA s₀ 2 + BitVec.ofNat 64 i) =
        if e then s.mem (sA deL s₀ KP + BitVec.ofNat 64 i) else s.mem (sA deL s₀ JB + BitVec.ofNat 64 i))
    (fun k u hk' ⟨k₁, f₁, b₁⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ => ⟨k', f', ?_⟩
  · have r₁ : ∀ {o : Nat}, o + 32 ≤ 49152 → ∀ {j : Nat}, j < 32 →
        u.mem (sA deL s₀ o + BitVec.ofNat 64 j) = s.mem (sA deL s₀ o + BitVec.ofNat 64 j) := fun {o} f {j} hj =>
      f₁.bytes (R := R (kA s₀) deL.sc o 32) (sk f) (show 32 ≤ 2 ^ 64 by decide) hj
    refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (KP + 8 * k)) ⟨by simp only [KP]; omega, by simp only [KP]; omega⟩
      (by rw [k₁.get .x28, hk.x28]; rfl) (by rw [k₁.rd, k₁.wr]; exact in_R hkr (k := 8 * k) (by omega) (by decide))
      fun u₁ g₁ v₁ => ?_
    refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (JB + 8 * k)) ⟨by simp only [JB]; omega, by simp only [JB]; omega⟩
      (by rw [g₁.get .x28, k₁.get .x28, hk.x28]; rfl)
      (by rw [g₁.rd, g₁.wr, k₁.rd, k₁.wr]; exact in_R hjr (k := 8 * k) (by omega) (by decide))
      fun u₂ g₂ v₂ => ?_
    refine wp_eor fun u₃ g₃ v₃ => wp_and fun u₄ g₄ v₄ => wp_eor fun u₅ g₅ v₅ => ?_
    have o₅ : Only [.x12, .x13] u u₅ := ((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).mono
    refine wp_strx (a := kA s₀ 2 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩
      (by rw [o₅.get .x27, k₁.get .x27, hk.x27]; rfl)
      (by
        rw [o₅.wr, k₁.wr]
        have := in_R hw (k := 8 * k) (n := 8) (by omega) (by decide)
        rwa [Nat.zero_add] at this) fun u₆ g₆ => wp_nil ?_
    have mk : u₃.gpr .x10 = if e then (0 : BitVec 64) - 1 else 0 := by
      rw [g₃.get .x10, g₂.get .x10, g₁.get .x10, k₁.get .x10, hm]
    have a12 : u₂.gpr .x12 = u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (KP + 8 * k)) 64 := by
      rw [g₂.get .x12, v₁]
    have a13 : u₂.gpr .x13 = u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (JB + 8 * k)) 64 := by
      rw [v₂, g₁.mem]
    have val : u₅.gpr .x12 = if e then u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (KP + 8 * k)) 64
        else u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (JB + 8 * k)) 64 := by
      rw [v₅, g₄.get .x13, g₃.get .x13, v₄, v₃, a12, a13, mk, sel_val]
    have m₆ : u₆.mem = u.mem.writeW (kA s₀ 2 + BitVec.ofNat 64 (8 * k)) (u₅.gpr .x12) := by
      rw [g₆.mem, o₅.mem]
    refine ⟨(k₁.trans (o₅.keep.trans g₆.keep)).mono, ?_, fun i hi => ?_⟩
    · rw [m₆]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [show kA s₀ 2 + BitVec.ofNat 64 (8 * k) = kA s₀ 2 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * k) by
          rw [ptr_add, Nat.zero_add]]
        exact contains_off (by omega) (by decide))
    · rw [m₆]
      rcases (by omega : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [writeW64_off _ _ _ _ (by
          rw [show kA s₀ 2 = kA s₀ 2 + BitVec.ofNat 64 0 from (ptr_zero _).symm, ptr_add, ptr_add]
          exact sep_off _ (a := 0 + i) (n := 1) (b := 0 + 8 * k) (k := 8) (by omega) (by omega) (by omega) _
            (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · have hj : i - 8 * k < 8 := by omega
        rw [show kA s₀ 2 + BitVec.ofNat 64 i = kA s₀ 2 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show 8 * k + (i - 8 * k) = i by omega], writeW64_byte _ _ _ hj, val]
        have e₁ : ∀ o, o + 32 ≤ 49152 → kA s₀ 3 + BitVec.ofNat 64 (o + 8 * k) + BitVec.ofNat 64 (i - 8 * k) =
            sA deL s₀ o + BitVec.ofNat 64 i := fun o _ => by
          rw [ptr_add, show sA deL s₀ o = kA s₀ 3 + BitVec.ofNat 64 o from rfl, ptr_add,
            show o + 8 * k + (i - 8 * k) = o + i by omega]
        cases e
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [readW64_byte _ _ hj, e₁ JB (by decide), r₁ (by decide) (by omega)]
        · simp only [↓reduceIte]
          rw [readW64_byte _ _ hj, e₁ KP (by decide), r₁ (by decide) (by omega)]
  · cases e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine bytesAt_eq (bytesAt_length _ _ _) fun i hi => ?_
      rw [bytesAt_getElem, b' i (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      refine bytesAt_eq (bytesAt_length _ _ _) fun i hi => ?_
      rw [bytesAt_getElem, b' i (by omega)]
      simp only [↓reduceIte]

end VG.Proof.MlKem1024.AArch64.Decaps
