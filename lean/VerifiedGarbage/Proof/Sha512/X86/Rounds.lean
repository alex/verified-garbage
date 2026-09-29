import VerifiedGarbage.Proof.Sha512.X86.Steps
import VerifiedGarbage.Proof.Sha512.Spec

/-!
# SHA-512 on x86 (32-bit): the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86 VG.Impl.Sha512.X86
open VG.Spec.Sha512 (HashValue Word Block W)
open VG.Proof.Sha256.X86.Stream (contains_addr)
open VG.Proof.Sha512.Arm (hi_append_lo)

/-! ## 64-bit words in memory -/

theorem frame_write64 {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hr : ⟨b.setWidth 64, N⟩ ∈ rs) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) (x : BitVec 64) :
    Frame rs m (write64 m' b o x) :=
  (h.writeW hr _ (contains_addr (by omega) (by omega) hfit)).writeW hr _
    (contains_addr (by omega) (by omega) hfit)

theorem Acc.of_mem {wr : List Region} {B : BitVec 32} {N : Nat} (h : ⟨B.setWidth 64, N⟩ ∈ wr)
    (hfit : B.toNat + N ≤ 2 ^ 32) : Acc wr B N :=
  fun _ ho => ⟨_, h, contains_addr ho (by omega) hfit⟩

theorem rd64_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b.setWidth 64, N⟩ r) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) :
    rd64 m' b o = rd64 m b o := by
  simp only [rd64]
  rw [h.readW (contains_addr (by omega) (by omega) hfit) hd (by decide),
    h.readW (contains_addr (by omega) (by omega) hfit) hd (by decide)]

/-! ## Offsets -/

theorem vOff_lt (t k : Nat) : vOff t k + 8 ≤ 64 := by simp only [vOff]; omega

theorem wOff_lt (j : Nat) : wOff j + 8 ≤ 192 := by simp only [wOff]; omega

/-- The working variables are below the message schedule. -/
theorem vw_sep (t k j : Nat) : vOff t k + 8 ≤ wOff j := by simp only [vOff, wOff]; omega

theorem vOff_sep (t : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    vOff t i + 8 ≤ vOff t j ∨ vOff t j + 8 ≤ vOff t i := by
  simp only [vOff]; omega

theorem vOff_succ_zero (t : Nat) : vOff (t + 1) 0 = vOff t 7 := by simp only [vOff]; omega

theorem vOff_succ (t k : Nat) (hk : k < 7) : vOff (t + 1) (k + 1) = vOff t k := by
  simp only [vOff]; omega

theorem wOff_sep {i j : Nat} (h : i % 16 ≠ j % 16) : wOff i + 8 ≤ wOff j ∨ wOff j + 8 ≤ wOff i := by
  simp only [wOff]; omega

/-! ## Rounds -/

/-- The registers the rounds write. -/
def temps : List Reg := [Y0, Y1, Z0, Z1, T]

/-- The part of the scratch region the rounds write (not the saved registers
and the block count). -/
abbrev workR (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 192⟩

/-- What the rounds need of their state `s`, with `scratch = scr` in `esi`. -/
structure Ctx (scr : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = scr
  fitV : scr.toNat + 224 ≤ 2 ^ 32
  wV : Acc s.wr scr 224

theorem Ctx.of_wrote {scr : BitVec 32} {s s' : State} {ds : List Reg} {m : Mem} (c : Ctx scr s)
    (w : Wrote ds s s' m) (h : .esi ∉ ds) : Ctx scr s' :=
  ⟨(w.gpr _ h).trans c.esi, c.fitV, w.wr ▸ c.wV⟩

/-- The rounds' invariant after `t` rounds, from `s₀`. -/
structure RInv (scr : BitVec 32) (H : HashValue) (M : Block) (s₀ : State) (t : Nat) (s : State) :
    Prop where
  vars : ∀ k (hk : k < 8), rd64 s.mem scr (vOff t k) = (Spec.Sha512.rounds H M t)[k]
  win : ∀ j < t, t ≤ j + 16 → rd64 s.mem scr (wOff j) = W M j
  gpr : ∀ r, r ∉ temps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR scr] s₀.mem s.mem

theorem roundKW_get (v : HashValue) (a b : Word) {k : Nat} (hk : k < 8) (h0 : k ≠ 0) (h4 : k ≠ 4) :
    (roundKW v a b)[k] = v[k - 1] := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The memory after round `t`'s message word and round. -/
theorem round_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx scr s) (hI : RInv scr H M s₀ t s) (ht : t < 80) (s₁ : State)
    (w₁ : Wrote temps s s₁ (write64 s.mem scr (wOff t) (W M t))) :
    WP isa (.block (round t)) s₁ (RInv scr H M s₀ (t + 1)) := by
  have c₁ := c.of_wrote w₁ (by decide)
  have fitV := c.fitV
  set v := Spec.Sha512.rounds H M t with hv
  have wt := wOff_lt t
  have hvar : ∀ k (hk : k < 8), rd64 s₁.mem scr (vOff t k) = v[k] := fun k hk => by
    rw [w₁.mem, rd64_write64_ne _ _ (by omega) (by have := vOff_lt t k; omega)
      (.inr (vw_sep t k t)), hI.vars k hk]
  have hw : rd64 s₁.mem scr (wOff t) = W M t := by
    rw [w₁.mem, rd64_write64_self _ _ (by omega)]
  rw [← List.append_nil (round t)]
  unfold round
  have v0 := vOff_lt t 0
  have v1 := vOff_lt t 1
  have v2 := vOff_lt t 2
  have v3 := vOff_lt t 3
  have v7 := vOff_lt t 7
  refine wp_roundW (N := 224) (by omega) (by omega) (by omega) (by omega)
    (by have := vOff_lt t 4; omega) (by have := vOff_lt t 5; omega) (by have := vOff_lt t 6; omega)
    (by omega) (by omega) fitV (vOff_sep t (by omega) (by omega) (by omega))
    (vOff_sep t (by omega) (by omega) (by omega)) (vOff_sep t (by omega) (by omega) (by omega))
    c₁.wV c₁.esi fun s₂ w₂ => WP.block_nil ?_
  rw [hvar 0 (by omega), hvar 1 (by omega), hvar 2 (by omega), hvar 3 (by omega), hvar 4 (by omega),
    hvar 5 (by omega), hvar 6 (by omega), hvar 7 (by omega), hw] at w₂
  have hnext : Spec.Sha512.rounds H M (t + 1) = roundKW v (Spec.Sha512.K t) (W M t) := by
    rw [rounds_succ, round_eq]
  have e73 : vOff t 3 + 8 ≤ vOff t 7 ∨ vOff t 7 + 8 ≤ vOff t 3 := vOff_sep t (by omega) (by omega) (by omega)
  refine ⟨fun k hk => ?_, fun j hj hj' => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [w₂.mem, hnext]
    by_cases h4 : k = 4
    · subst h4
      rw [show vOff (t + 1) 4 = vOff t 3 from vOff_succ t 3 (by omega),
        rd64_write64_ne (b := scr) (o := vOff t 7) (o' := vOff t 3) _ _ (by omega) (by omega) e73.symm,
        rd64_write64_self (b := scr) (o := vOff t 3) _ _ (by omega)]
      rfl
    · by_cases h0 : k = 0
      · subst h0
        rw [vOff_succ_zero, rd64_write64_self (b := scr) (o := vOff t 7) _ _ (by omega)]
        rfl
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        have vi := vOff_lt t i
        rw [vOff_succ t i (by omega),
          rd64_write64_ne (b := scr) (o := vOff t 7) (o' := vOff t i) _ _ (by omega) (by omega)
            (vOff_sep t (by omega) (by omega) (by omega)),
          rd64_write64_ne (b := scr) (o := vOff t 3) (o' := vOff t i) _ _ (by omega) (by omega)
            (vOff_sep t (by omega) (by omega) (by omega)),
          hvar i (by omega), roundKW_get _ _ _ hk h0 h4]
        simp only [Nat.add_sub_cancel]
  · have wj := wOff_lt j
    rw [w₂.mem, rd64_write64_ne (b := scr) (o := vOff t 7) (o' := wOff j) _ _ (by omega) (by omega)
        (.inl (vw_sep t 7 j)),
      rd64_write64_ne (b := scr) (o := vOff t 3) (o' := wOff j) _ _ (by omega) (by omega)
        (.inl (vw_sep t 3 j))]
    by_cases hjt : j = t
    · subst hjt; exact hw
    · rw [w₁.mem, rd64_write64_ne (b := scr) (o := wOff t) (o' := wOff j) _ _
        (by omega) (by omega) (wOff_sep (by omega))]
      exact hI.win j (by omega) (by omega)
  · rw [w₂.gpr r hr, w₁.gpr r hr, hI.gpr r hr]
  · rw [w₂.rd, w₁.rd, hI.rd]
  · rw [w₂.wr, w₁.wr, hI.wr]
  · rw [w₂.mem, w₁.mem]
    exact frame_write64 (N := 192) (frame_write64 (N := 192) (frame_write64 (N := 192) hI.frame (by simp)
      (by omega) (wOff_lt t) _) (by simp) (by omega) (by omega) _) (by simp) (by omega) (by omega) _

theorem Ctx.of_rinv {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx scr s₀) (hI : RInv scr H M s₀ t s) : Ctx scr s :=
  ⟨(hI.gpr _ (by decide)).trans c.esi, c.fitV, hI.wr ▸ c.wV⟩

/-- The block at `bk`'s words, as `loadW` makes them from its bytes. -/
def Raw (bk : BitVec 32) (M : Block) (m : Mem) : Prop :=
  ∀ j < 16, bswap (m.readW (addr bk (8 * j)) 32) ++ bswap (m.readW (addr bk (8 * j + 4)) 32) = W M j

/-- Where the block is: at `bk` (in `edi`), readable, and apart from the scratch region. -/
structure BlkCtx (scr bk : BitVec 32) (s₀ : State) : Prop where
  edi : s₀.gpr .edi = bk
  fitB : bk.toNat + 128 ≤ 2 ^ 32
  disj : Region.Disjoint ⟨bk.setWidth 64, 128⟩ (workR scr)
  rd : ∀ o, o + 4 ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (addr bk o) 4

theorem step_ok {scr bk : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c₀ : Ctx scr s₀) (hB : BlkCtx scr bk s₀) (hM : Raw bk M s₀.mem)
    (hI : RInv scr H M s₀ t s) (ht : t < 80) :
    WP isa (.block (schedule t ++ round t)) s (RInv scr H M s₀ (t + 1)) := by
  have c := c₀.of_rinv hI
  by_cases h16 : t < 16
  · unfold schedule; simp only [h16, ↓reduceIte]
    have rdB : ∀ o, o + 4 ≤ 128 → s.mem.readW (addr bk o) 32 = s₀.mem.readW (addr bk o) 32 :=
      fun o ho => hI.frame.readW (contains_addr ho (by omega) hB.fitB)
        (fun r hr => by simp at hr; subst hr; exact hB.disj) (by decide)
    refine wp_loadW (N := 224) (by have := wOff_lt t; omega) c.wV c.esi
      (by rw [hI.gpr _ (by decide), hB.edi]) (by rw [hI.rd, hI.wr]; exact hB.rd _ (by omega))
      (by rw [hI.rd, hI.wr]; exact hB.rd _ (by omega)) fun s₁ w₁ => round_ok c hI ht s₁ ?_
    rw [rdB _ (by omega), rdB _ (by omega), hM t h16] at w₁
    exact (w₁.mono' (by decide))
  · unfold schedule; simp only [h16, ↓reduceIte]
    have e : ∀ i, 1 ≤ i → i ≤ 16 → rd64 s.mem scr (wOff (t + 16 - i)) = W M (t - i) :=
      fun i hi hi' => by
        rw [show wOff (t + 16 - i) = wOff (t - i) by simp only [wOff]; omega]
        exact hI.win _ (by omega) (by omega)
    have w' : ∀ j, wOff j + 8 ≤ 224 := fun j => by have := wOff_lt j; omega
    refine wp_expandW (N := 224) (w' _) (w' _) (w' _) (w' _) c.wV c.esi fun s₁ w₁ => round_ok c hI ht s₁ ?_
    have e16 : rd64 s.mem scr (wOff t) = W M (t - 16) := by
      rw [← e 16 (by omega) (by omega), show t + 16 - 16 = t by omega]
    rw [show t + 14 = t + 16 - 2 by omega, show t + 9 = t + 16 - 7 by omega,
      show t + 1 = t + 16 - 15 by omega, e 2 (by omega) (by omega), e 7 (by omega) (by omega),
      e 15 (by omega) (by omega), e16, ← W_ge M (by omega)] at w₁
    exact (w₁.mono' (by decide))

theorem rounds_ok {scr bk : BitVec 32} {H : HashValue} {M : Block} {s₀ : State}
    (c₀ : Ctx scr s₀) (hB : BlkCtx scr bk s₀) (hM : Raw bk M s₀.mem)
    (h0 : ∀ k (hk : k < 8), rd64 s₀.mem scr (8 * k) = H[k]) :
    ∀ t ≤ 80, WP isa (rounds t) s₀ (RInv scr H M s₀ t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil ⟨fun k hk => ?_, fun j hj => absurd hj (by omega),
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
    rw [show vOff 0 k = 8 * k by simp only [vOff]; omega, h0 k hk]; rfl
  | succ t ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun s hI => step_ok c₀ hB hM hI (by omega))

end VG.Proof.Sha512.X86
