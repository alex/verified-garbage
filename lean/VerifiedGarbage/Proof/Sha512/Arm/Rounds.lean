import VerifiedGarbage.Proof.Sha512.Arm.Steps

/-!
# SHA-512 on ARMv7: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Spec.Sha512 (HashValue Word Block W)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.Sha256.Arm.Stream (readW_writeW_save)

/-! ## 64-bit words in memory -/

theorem A_eq {b : BitVec 32} {off : Nat} (h : b.toNat + off < 2 ^ 32) :
    A b off = State.addr b + BitVec.ofNat 64 off :=
  addr_add h

theorem rd64_write64_self (m : Mem) {b : BitVec 32} {o : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) : rd64 (write64 m b o x) b o = x := by
  simp only [rd64, write64]
  rw [Mem.readW_writeW_self32, A_eq (by omega), A_eq (b := b) (off := o + 4) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32, hi_append_lo]

theorem rd64_write64_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    rd64 (write64 m b o x) b o' = rd64 m b o' := by
  simp only [rd64, write64]
  rw [A_eq (b := b) (off := o) (by omega), A_eq (b := b) (off := o + 4) (by omega),
    A_eq (b := b) (off := o') (by omega), A_eq (b := b) (off := o' + 4) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega)]

theorem contains_A {b : BitVec 32} {N o : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 4 ≤ N) :
    (⟨State.addr b, N⟩ : Region).Contains (A b o) 4 := by
  rw [A_eq (by omega)]; exact contains_offset ho (by omega)

theorem rd64_write64_disj (m : Mem) {b b' : BitVec 32} {N N' o o' : Nat} (x : BitVec 64)
    (hd : Region.Disjoint ⟨State.addr b, N⟩ ⟨State.addr b', N'⟩)
    (hfit : b.toNat + N ≤ 2 ^ 32) (hfit' : b'.toNat + N' ≤ 2 ^ 32) (ho : o + 8 ≤ N) (ho' : o' + 8 ≤ N') :
    rd64 (write64 m b o x) b' o' = rd64 m b' o' := by
  have s : ∀ i j, i + 4 ≤ N → j + 4 ≤ N' → Mem.Sep (A b' j) (32 / 8) (A b i) (32 / 8) :=
    fun i j hi hj => hd.symm.sep (contains_A hfit' hj) (contains_A hfit hi)
  simp only [rd64, write64]
  rw [Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide)]

theorem frame_write64 {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hr : ⟨State.addr b, N⟩ ∈ rs) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) (x : BitVec 64) :
    Frame rs m (write64 m' b o x) :=
  (h.writeW hr _ (contains_A hfit (by omega))).writeW hr _ (contains_A hfit (by omega))

theorem Reg64.of_mem {wr : List Region} {B : BitVec 32} {N : Nat} (h : ⟨State.addr B, N⟩ ∈ wr)
    (hfit : B.toNat + N ≤ 2 ^ 32) : Reg64 wr B N :=
  fun _ ho => ⟨⟨_, h, contains_A hfit (by omega)⟩, ⟨_, h, contains_A hfit (by omega)⟩⟩

/-! ## Offsets -/

theorem vOff_lt (t k : Nat) : vOff t k + 8 ≤ 64 := by simp only [vOff]; omega

theorem wOff_lt (j : Nat) : wOff j + 8 ≤ 192 := by simp only [wOff]; omega

theorem vOff_sep (t : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    vOff t i + 8 ≤ vOff t j ∨ vOff t j + 8 ≤ vOff t i := by
  simp only [vOff]; omega

theorem vOff_succ_zero (t : Nat) : vOff (t + 1) 0 = vOff t 7 := by simp only [vOff]; omega

theorem vOff_succ (t k : Nat) (hk : k < 7) : vOff (t + 1) (k + 1) = vOff t k := by
  simp only [vOff]; omega

theorem wOff_sep {i j : Nat} (h : i % 16 ≠ j % 16) : wOff i + 8 ≤ wOff j ∨ wOff j + 8 ≤ wOff i := by
  simp only [wOff]; omega

/-! ## Rounds -/

/-- The registers the compression function writes. -/
def temps : List Reg := [X0, X1, Y0, Y1, Z0, Z1, E0, E1]

/-- The hash value's region (with the buffer) and the working variables' region. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 192⟩
abbrev varR (scr : BitVec 32) : Region := ⟨State.addr scr, 64⟩

/-- What the compression function needs of its state `s`, with `state = st`, `scratch = scr`. -/
structure Ctx (st scr : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  fitS : st.toNat + 192 ≤ 2 ^ 32
  fitV : scr.toNat + 64 ≤ 2 ^ 32
  disj : (stR st).Disjoint (varR scr)
  wS : Reg64 s.wr st 192
  wV : Reg64 s.wr scr 64

theorem Wrote.mono' {ds es : List Reg} {s s' : State} {m : Mem} (w : Wrote ds s s' m)
    (h : ∀ r ∈ ds, r ∈ es) : Wrote es s s' m :=
  ⟨fun r hr => w.gpr r fun hd => hr (h r hd), w.mem, w.rd, w.wr, w.sp⟩

theorem Ctx.of_eq {st scr : BitVec 32} {s s' : State} (c : Ctx st scr s) (h0 : s'.gpr .r0 = s.gpr .r0)
    (h3 : s'.gpr .r3 = s.gpr .r3) (hwr : s'.wr = s.wr) : Ctx st scr s' :=
  ⟨h0.trans c.r0, h3.trans c.r3, c.fitS, c.fitV, c.disj, hwr ▸ c.wS, hwr ▸ c.wV⟩

theorem Ctx.of_wrote {st scr : BitVec 32} {s s' : State} {ds : List Reg} {m : Mem} (c : Ctx st scr s)
    (w : Wrote ds s s' m) (h0 : .r0 ∉ ds) (h3 : .r3 ∉ ds) : Ctx st scr s' :=
  ⟨(w.gpr _ h0).trans c.r0, (w.gpr _ h3).trans c.r3, c.fitS, c.fitV, c.disj, w.wr ▸ c.wS,
    w.wr ▸ c.wV⟩

/-- The rounds' invariant after `t` rounds, from `s₀`. -/
structure RInv (st scr : BitVec 32) (H : HashValue) (M : Block) (s₀ : State) (t : Nat) (s : State) :
    Prop where
  vars : ∀ k (hk : k < 8), rd64 s.mem scr (vOff t k) = (Spec.Sha512.rounds H M t)[k]
  win : ∀ j < t, t ≤ j + 16 → rd64 s.mem st (wOff j) = W M j
  raw : ∀ j, t ≤ j → j < 16 → rd64 s.mem st (wOff j) = rd64 s₀.mem st (wOff j)
  hash : ∀ k < 8, rd64 s.mem st (8 * k) = rd64 s₀.mem st (8 * k)
  gpr : ∀ r, r ∉ temps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [stR st, varR scr] s₀.mem s.mem

theorem roundKW_get (v : HashValue) (a b : Word) {k : Nat} (hk : k < 8) (h0 : k ≠ 0) (h4 : k ≠ 4) :
    (roundKW v a b)[k] = v[k - 1] := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The memory after round `t`'s message word and round. -/
theorem round_ok {st scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx st scr s) (hI : RInv st scr H M s₀ t s) (ht : t < 80) (s₁ : State)
    (w₁ : Wrote temps s s₁ (write64 s.mem st (wOff t) (W M t))) :
    WP isa (.block (round t)) s₁ (RInv st scr H M s₀ (t + 1)) := by
  have c₁ := c.of_wrote w₁ (by decide) (by decide)
  set v := Spec.Sha512.rounds H M t with hv
  have hvar : ∀ k (hk : k < 8), rd64 s₁.mem scr (vOff t k) = v[k] := fun k hk => by
    rw [w₁.mem, rd64_write64_disj _ _ c.disj c.fitS c.fitV (wOff_lt t) (vOff_lt t k), hI.vars k hk]
  have hw : rd64 s₁.mem st (wOff t) = W M t := by
    rw [w₁.mem, rd64_write64_self _ _ (by have := wOff_lt t; have := c.fitS; omega)]
  rw [← List.append_nil (round t)]
  unfold round
  refine wp_roundW (vOff_lt t 0) (vOff_lt t 1) (vOff_lt t 2) (vOff_lt t 3) (vOff_lt t 4) (vOff_lt t 5)
    (vOff_lt t 6) (vOff_lt t 7) (wOff_lt t) c₁.wS c₁.wV c₁.r0 c₁.r3 fun s₂ w₂ => WP.block_nil ?_
  rw [hvar 0 (by omega), hvar 1 (by omega), hvar 2 (by omega), hvar 3 (by omega), hvar 4 (by omega),
    hvar 5 (by omega), hvar 6 (by omega), hvar 7 (by omega), hw] at w₂
  have fitV := c.fitV
  have fitS := c.fitS
  have hnext : Spec.Sha512.rounds H M (t + 1) = roundKW v (Spec.Sha512.K t) (W M t) := by
    rw [rounds_succ, round_eq]
  refine ⟨fun k hk => ?_, fun j hj hj' => ?_, fun j hj hj' => ?_, fun k hk => ?_, fun r hr => ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [w₂.mem, hnext]
    by_cases h4 : k = 4
    · subst h4
      rw [show vOff (t + 1) 4 = vOff t 3 from vOff_succ t 3 (by omega),
        rd64_write64_self (b := scr) (o := vOff t 3) _ _ (by have := vOff_lt t 3; omega)]
      rfl
    · have e3 : ∀ i, i < 8 → i ≠ 3 → vOff t i + 8 ≤ vOff t 3 ∨ vOff t 3 + 8 ≤ vOff t i :=
        fun i hi h => vOff_sep t hi (by omega) h
      by_cases h0 : k = 0
      · subst h0
        rw [vOff_succ_zero, rd64_write64_ne (b := scr) (o := vOff t 3) (o' := vOff t 7) _ _
          (by have := vOff_lt t 3; omega) (by have := vOff_lt t 7; omega) (e3 7 (by omega) (by omega)).symm,
          rd64_write64_self (b := scr) (o := vOff t 7) _ _ (by have := vOff_lt t 7; omega)]
        rfl
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        rw [vOff_succ t i (by omega), rd64_write64_ne (b := scr) (o := vOff t 3) (o' := vOff t i) _ _
          (by have := vOff_lt t 3; omega) (by have := vOff_lt t i; omega) (e3 i (by omega) (by omega)).symm,
          rd64_write64_ne (b := scr) (o := vOff t 7) (o' := vOff t i) _ _
            (by have := vOff_lt t 7; omega) (by have := vOff_lt t i; omega)
            (vOff_sep t (by omega) (by omega) (by omega)),
          hvar i (by omega), roundKW_get _ _ _ hk h0 h4]
        simp only [Nat.add_sub_cancel]
  · rw [w₂.mem, rd64_write64_disj _ _ c.disj.symm fitV fitS (vOff_lt t 3) (wOff_lt j),
      rd64_write64_disj _ _ c.disj.symm fitV fitS (vOff_lt t 7) (wOff_lt j)]
    by_cases hjt : j = t
    · subst hjt; exact hw
    · rw [w₁.mem, rd64_write64_ne (b := st) (o := wOff t) (o' := wOff j) _ _
        (by have := wOff_lt t; omega) (by have := wOff_lt j; omega)
        (wOff_sep (by omega))]
      exact hI.win j (by omega) (by omega)
  · rw [w₂.mem, rd64_write64_disj _ _ c.disj.symm fitV fitS (vOff_lt t 3) (wOff_lt j),
      rd64_write64_disj _ _ c.disj.symm fitV fitS (vOff_lt t 7) (wOff_lt j), w₁.mem,
      rd64_write64_ne (b := st) (o := wOff t) (o' := wOff j) _ _
        (by have := wOff_lt t; omega) (by have := wOff_lt j; omega)
        (wOff_sep (by omega))]
    exact hI.raw j (by omega) hj'
  · rw [w₂.mem, rd64_write64_disj _ _ c.disj.symm fitV fitS (vOff_lt t 3) (by omega : 8 * k + 8 ≤ 192),
      rd64_write64_disj _ _ c.disj.symm fitV fitS (vOff_lt t 7) (by omega : 8 * k + 8 ≤ 192), w₁.mem,
      rd64_write64_ne (b := st) (o := wOff t) (o' := 8 * k) _ _ (by have := wOff_lt t; omega)
        (by omega) (by simp only [wOff]; omega)]
    exact hI.hash k hk
  · rw [w₂.gpr r hr, w₁.gpr r hr, hI.gpr r hr]
  · rw [w₂.rd, w₁.rd, hI.rd]
  · rw [w₂.wr, w₁.wr, hI.wr]
  · rw [w₂.sp, w₁.sp, hI.sp]
  · rw [w₂.mem, w₁.mem]
    exact frame_write64 (frame_write64 (frame_write64 hI.frame (by simp) fitS (wOff_lt t) _)
      (by simp) fitV (vOff_lt t 7) _) (by simp) fitV (vOff_lt t 3) _

theorem Ctx.of_rinv {st scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx st scr s₀) (hI : RInv st scr H M s₀ t s) : Ctx st scr s :=
  ⟨(hI.gpr _ (by decide)).trans c.r0, (hI.gpr _ (by decide)).trans c.r3, c.fitS, c.fitV, c.disj,
    hI.wr ▸ c.wS, hI.wr ▸ c.wV⟩

/-- The block's words, as `loadW` makes them from its bytes. -/
def Raw (st : BitVec 32) (M : Block) (m : Mem) : Prop :=
  ∀ j < 16, rev (lo (rd64 m st (wOff j))) ++ rev (hi (rd64 m st (wOff j))) = W M j

theorem step_ok {st scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c₀ : Ctx st scr s₀) (hM : Raw st M s₀.mem) (hI : RInv st scr H M s₀ t s) (ht : t < 80) :
    WP isa (.block (schedule t ++ round t)) s (RInv st scr H M s₀ (t + 1)) := by
  have c := c₀.of_rinv hI
  by_cases h16 : t < 16
  · unfold schedule; simp only [h16, ↓reduceIte]
    refine wp_loadW (by omega) (wOff_lt t) c.wS c.r0 fun s₁ w₁ => round_ok c hI ht s₁ ?_
    rw [hI.raw t (by omega) h16, hM t h16] at w₁
    exact (w₁.mono' (by decide))
  · unfold schedule; simp only [h16, ↓reduceIte]
    have e : ∀ i, 1 ≤ i → i ≤ 16 → rd64 s.mem st (wOff (t + 16 - i)) = W M (t - i) :=
      fun i hi hi' => by
        rw [show wOff (t + 16 - i) = wOff (t - i) by simp only [wOff]; omega]
        exact hI.win _ (by omega) (by omega)
    refine wp_expandW (by omega) (wOff_lt _) (wOff_lt _) (wOff_lt _) (wOff_lt _) c.wS c.r0
      fun s₁ w₁ => round_ok c hI ht s₁ ?_
    have e16 : rd64 s.mem st (wOff t) = W M (t - 16) := by
      rw [← e 16 (by omega) (by omega), show t + 16 - 16 = t by omega]
    rw [show t + 14 = t + 16 - 2 by omega, show t + 9 = t + 16 - 7 by omega,
      show t + 1 = t + 16 - 15 by omega, e 2 (by omega) (by omega), e 7 (by omega) (by omega),
      e 15 (by omega) (by omega), e16, ← W_ge M (by omega)] at w₁
    exact (w₁.mono' (by decide))

theorem rounds_ok {st scr : BitVec 32} {H : HashValue} {M : Block} {s₀ : State}
    (c₀ : Ctx st scr s₀) (hM : Raw st M s₀.mem)
    (h0 : ∀ k (hk : k < 8), rd64 s₀.mem scr (8 * k) = H[k]) :
    ∀ t ≤ 80, WP isa (rounds t) s₀ (RInv st scr H M s₀ t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil ⟨fun k hk => ?_, fun j hj => absurd hj (by omega), fun _ _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
    rw [show vOff 0 k = 8 * k by simp only [vOff]; omega, h0 k hk]; rfl
  | succ t ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun s hI => step_ok c₀ hM hI (by omega))

end VG.Proof.Sha512.Arm
