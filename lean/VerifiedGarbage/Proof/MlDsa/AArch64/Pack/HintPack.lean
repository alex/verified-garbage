import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Hint
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlKem.AArch64.MemTaint
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_pack`

The code follows the fold form of `HintBitPack` (`Pack/Hint.lean`) step by
step: the bytes of `y` are the array of the spec, and `x5` its index, which
stays below `ω` because it counts the 1s before the current coefficient
(`hpIdx_lt`).

Constant time but for the hint: once `y` is zeroed, the two runs agree on
all the memory the function may access (the hint, which the contract lets
it leak, and `y`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_lsr wp_ldrw wp_strb wp_addImm wp_subImm wp_movz wp_mov
  wp_nil eval_nonzero ne_zero_iff toNat_readW32 toNat_ofNat_lt toNat_imm setWidth8_of_toNat ptr_add ptr_zero
  count_loop abi_of agree_of)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_getD bytesAt_eq bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_pack(h = x0, hlen = x1, omega = w2, y = x3, len = x4)`. -/
def hintBitPackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat * 4⟩] ∧ s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat * 4⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
    (wArg s .x2, (s.gpr .x4).toNat - wArg s .x2) ∈ hintParams ∧ wArg s .x2 ≤ (s.gpr .x4).toNat ∧
    (s.gpr .x1).toNat = 256 * ((s.gpr .x4).toNat - wArg s .x2) ∧
    hintOnes (hintAt s.mem (s.gpr .x0) ((s.gpr .x4).toNat - wArg s .x2)) ≤ wArg s .x2
  post s s' := bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
    hintBitPack (wArg s .x2) ((s.gpr .x4).toNat - wArg s .x2)
      (hintAt s.mem (s.gpr .x0) ((s.gpr .x4).toNat - wArg s .x2))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    (List.range (s₁.gpr .x1).toNat).map (fun i => (coeffAt s₁.mem (s₁.gpr .x0) i).toNat) =
      (List.range (s₂.gpr .x1).toNat).map (fun i => (coeffAt s₂.mem (s₂.gpr .x0) i).toNat)

/-- `x + 1`, of a number. -/
theorem ofNat_succ64 (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 1 = BitVec.ofNat 64 (x + 1) := by
  rw [BitVec.ofNat_add_ofNat]

/-- The low byte of a register holding a number. -/
theorem lowByte (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- `k = hlen / 256` and `ω = len - k`, from the lengths. -/
theorem lsr8_toNat (x : BitVec 64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : hintBitPackK.pre s₀)

/-- The arguments. -/
abbrev hω (s₀ : State) : Nat := wArg s₀ .x2
abbrev hk (s₀ : State) : Nat := (s₀.gpr .x4).toNat - wArg s₀ .x2
abbrev hLen (s₀ : State) : Nat := (s₀.gpr .x4).toNat
abbrev hH (s₀ : State) : List (Vector Bool n) := hintAt s₀.mem (s₀.gpr .x0) (hk s₀)
abbrev hR (s₀ : State) : Region := ⟨s₀.gpr .x0, (s₀.gpr .x1).toNat * 4⟩
abbrev yR (s₀ : State) : Region := ⟨s₀.gpr .x3, hLen s₀⟩

include hp in
theorem hp_facts : 4 ≤ hk s₀ ∧ hk s₀ ≤ 8 ∧ hω s₀ ≤ 80 ∧ hω s₀ + hk s₀ = hLen s₀ ∧
    (s₀.gpr .x1).toNat = 256 * hk s₀ := by
  have := mem_hintParams hp.2.2.2.1
  have := hp.2.2.2.2.1
  have := hp.2.2.2.2.2.1
  simp only [hk, hω, hLen] at *
  omega

/-! ## Zeroing `y` -/

/-- What `hbpInit` leaves. -/
def hbpInitPost (s₀ s : State) : Prop :=
  (∀ t < hLen s₀, s.mem (s₀.gpr .x3 + BitVec.ofNat 64 t) = 0) ∧ Frame [yR s₀] s₀.mem s.mem ∧
    s.gpr .x0 = s₀.gpr .x0 ∧ s.gpr .x3 = s₀.gpr .x3 ∧ s.gpr .x2 = s₀.gpr .x4 - (s₀.gpr .x1 >>> 8) ∧
    s.gpr .x12 = s₀.gpr .x1 >>> 8 ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp

include hp in
theorem hbpInit_ok : WP isa hbpInit s₀ (hbpInitPost s₀) := by
  obtain ⟨hk4, -, -, hsum, -⟩ := hp_facts hp
  have hwr := hp.2.1
  have hl : hLen s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  unfold hbpInit hbpPro
  refine WP.seq (wp_lsr (by decide) fun s₁ o₁ e₁ => wp_sub fun s₂ o₂ e₂ => wp_movz fun s₃ o₃ e₃ =>
    wp_mov fun s₄ o₄ e₄ => wp_mov fun s₅ o₅ e₅ => wp_nil ?_)
  have k₅ := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  have x15 : s₅.gpr .x15 = 0 := by rw [o₅.get .x15, o₄.get .x15, e₃]; rfl
  refine WP.mono (count_loop (n := hLen s₀) (by omega) (fun t s => s.gpr .x9 = s₀.gpr .x3 + BitVec.ofNat 64 t ∧
      (s.gpr .x10).toNat = hLen s₀ - t ∧ Keep [.x9, .x10] s₅ s ∧ Frame [yR s₀] s₀.mem s.mem ∧
      ∀ u < t, s.mem (s₀.gpr .x3 + BitVec.ofNat 64 u) = 0)
    (fun t ht s ⟨h9, h10, hk, hf, hz⟩ => ?_)
    ⟨by rw [o₅.get .x9, e₄, o₃.get .x3, o₂.get .x3, o₁.get .x3, ptr_zero],
      (by rw [e₅, o₄.get .x4, o₃.get .x4, o₂.get .x4, o₁.get .x4, Nat.sub_zero]), Keep.refl _ _, by rw [k₅.mem]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s ⟨_, _, hk, hf, hz⟩ => ⟨hz, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : (yR s₀).Contains (s₀.gpr .x3 + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega) (by omega)
    refine wp_strb (by decide) (by rw [h9, ptr_zero]) (by rw [hk.wr, k₅.wr, hwr]; exact ⟨_, .head _, hc⟩)
      fun s₁ h₁ => wp_addImm (by decide) fun s₂ o₂ e₂ => wp_subImm (by decide) fun s₃ o₃ e₃ => wp_nil
        ⟨⟨by rw [o₃.get .x9, e₂, h₁.gpr, h9, ptr_add], by rw [e₃, o₂.get .x10, h₁.gpr]; exact count_step h10 ht,
          ((hk.trans h₁.keep).trans (o₂.keep.trans o₃.keep)).mono, ?_, fun u hu => ?_⟩, ?_⟩
    · rw [o₃.mem, o₂.mem, h₁.mem]
      exact hf.writeW (List.mem_singleton_self _) _ hc
    · rw [o₃.mem, o₂.mem, h₁.mem, VG.WriteBytes.writeW8_apply]
      by_cases e : u = t
      · subst e; rw [ite_eq_left rfl, hk.get .x15, x15]; rfl
      · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) e)]; exact hz u (by omega)
    · rw [e₃, o₂.get .x10, h₁.gpr, count_step h10 ht]; omega
  · rw [hk.get .x0, k₅.get .x0]
  · rw [hk.get .x3, k₅.get .x3]
  · rw [hk.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, e₂, o₁.get .x4, e₁]
  · rw [hk.get .x12, o₅.get .x12, o₄.get .x12, o₃.get .x12, o₂.get .x12, e₁]
  · rw [hk.rd, k₅.rd]
  · rw [hk.wr, k₅.wr]
  · rw [hk.sp, k₅.sp]

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (hω s₀) (hH s₀)) (Array.replicate (hω s₀ + hk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((hH s₀).getD i noHint)) (hpS s₀ i)

theorem hpS_idx (s₀ : State) (i : Nat) : (hpS s₀ i).2 = onesBefore (hH s₀) i 0 := by
  rw [hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (hpT s₀ i j).2 = onesBefore (hH s₀) i j := by
  rw [hpT, hpSteps_idx, hpS_idx]; unfold onesBefore; rfl

theorem hpT_succ (s₀ : State) (i j : Nat) :
    hpT s₀ i (j + 1) = hpStep ((hH s₀).getD i noHint) (hpT s₀ i j) j := by
  rw [hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    hpS s₀ (i + 1) = ((hpT s₀ i n).1.set! (hω s₀ + i) (BitVec.ofNat 8 (hpT s₀ i n).2), (hpT s₀ i n).2) := by
  rw [hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-- Before coefficient `j` of polynomial `i`. -/
structure CInv (s₀ : State) (i j : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (4 * (256 * i + j))
  x3 : s.gpr .x3 = s₀.gpr .x3
  x5 : s.gpr .x5 = BitVec.ofNat 64 (hpT s₀ i j).2
  x6 : s.gpr .x6 = s₀.gpr .x3 + BitVec.ofNat 64 (hω s₀ + i)
  x7 : s.gpr .x7 = BitVec.ofNat 64 j
  x8 : (s.gpr .x8).toNat = 256 - j
  x12 : (s.gpr .x12).toNat = hk s₀ - i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .x3) (hLen s₀) = (hpT s₀ i j).1.toList

/-- The end of a coefficient: the pointer, `j` and the count. -/
theorem coefTail_ok {i j : Nat} (hj : j < 256) {s : State}
    (x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (4 * (256 * i + j))) (x3 : s.gpr .x3 = s₀.gpr .x3)
    (x5 : s.gpr .x5 = BitVec.ofNat 64 (hpT s₀ i (j + 1)).2)
    (x6 : s.gpr .x6 = s₀.gpr .x3 + BitVec.ofNat 64 (hω s₀ + i)) (x7 : s.gpr .x7 = BitVec.ofNat 64 j)
    (x8 : (s.gpr .x8).toNat = 256 - j) (x12 : (s.gpr .x12).toNat = hk s₀ - i) (rd : s.rd = s₀.rd)
    (wr : s.wr = s₀.wr) (sp : s.sp = s₀.sp) (frame : Frame [yR s₀] s₀.mem s.mem)
    (y : bytesAt s.mem (s₀.gpr .x3) (hLen s₀) = (hpT s₀ i (j + 1)).1.toList) :
    WP isa (.block [.addImm .x .x0 .x0 4, .addImm .x .x7 .x7 1, .subImm .x .x8 .x8 1]) s fun s' =>
      CInv s₀ i (j + 1) s' ∧ ((s'.gpr .x8).toNat ≠ 0 ↔ j + 1 ≠ 256) :=
  wp_addImm (by decide) fun s₁ o₁ e₁ => wp_addImm (by decide) fun s₂ o₂ e₂ => wp_subImm (by decide)
    fun s₃ o₃ e₃ => wp_nil (by
      have k₃ := (o₁.trans o₂).trans o₃
      have c8 : (s₃.gpr .x8).toNat = 256 - (j + 1) := by
        rw [e₃, o₂.get .x8, o₁.get .x8]; exact count_step x8 hj
      refine ⟨⟨?_, by rw [k₃.get .x3, x3], by rw [k₃.get .x5, x5], by rw [k₃.get .x6, x6], ?_, c8,
        by rw [k₃.get .x12, x12], by rw [k₃.rd, rd], by rw [k₃.wr, wr], by rw [k₃.sp, sp],
        by rw [k₃.mem]; exact frame, by rw [k₃.mem]; exact y⟩, by rw [c8]; omega⟩
      · rw [o₃.get .x0, o₂.get .x0, e₁, x0, ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
      · rw [o₃.get .x7, e₂, o₁.get .x7, x7, ofNat_succ64])

include hp in
/-- Coefficient `j` of polynomial `i`: if it is not 0, `y[index] ← j`. -/
theorem coef_ok {i j : Nat} (hi : i < hk s₀) (hj : j < 256) {s : State} (hI : CInv s₀ i j s) :
    WP isa hbpCoef s fun s' => CInv s₀ i (j + 1) s' ∧ ((s'.gpr .x8).toNat ≠ 0 ↔ j + 1 ≠ 256) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr1⟩ := hp_facts hp
  obtain ⟨hrd, hwr, hsep, -, -, -, hones⟩ := hp
  have hones' : hintOnes (hH s₀) ≤ hω s₀ := hones
  have hpos : 256 * i + j < 256 * hk s₀ := by omega
  have hR' : (hR s₀).Contains (coeffAddr (s₀.gpr .x0) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  have hw : s.mem.readW (coeffAddr (s₀.gpr .x0) (256 * i + j)) 32 = coeffAt s₀.mem (s₀.gpr .x0) (256 * i + j) :=
    hI.frame.readW hR' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by decide)
  have hbit := hintAt_get (m := s₀.mem) (p := s₀.gpr .x0) hi (show j < n from hj)
  have hT := hpT_succ s₀ i j
  have hidx := hpT_idx s₀ i j
  unfold hbpCoef
  refine WP.seq (wp_ldrw (a := coeffAddr (s₀.gpr .x0) (256 * i + j)) ⟨by decide, by decide⟩
    (by rw [hI.x0, ptr_zero]) (by rw [hI.rd, hI.wr, hrd]; exact ⟨_, .head _, hR'⟩) fun s₁ o₁ e₁ => wp_nil ?_)
  have hb : (s₁.gpr .x9 != 0) = ((hH s₀).getD i noHint)[j]! := by
    rw [hbit, ne_zero_iff, e₁, toNat_readW32, hw]
    exact decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl), fun h e => h (BitVec.eq_of_toNat_eq e)⟩
  refine WP.seq (WP.ite _ (eval_nonzero s₁ .x9) (fun h1 => ?_) (fun h0 => ?_))
  · -- A 1: `y[index] ← j`.
    rw [hb] at h1
    have hlt : (hpT s₀ i j).2 < hLen s₀ := by
      have : onesBefore (hH s₀) i j < hintOnes (hH s₀) :=
        hpIdx_lt (hintAt_length s₀.mem (s₀.gpr .x0) _) hi (show j < n from hj) h1
      rw [hidx]; omega
    have hc : (yR s₀).Contains (s₀.gpr .x3 + BitVec.ofNat 64 (hpT s₀ i j).2) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    unfold hbpSet
    refine wp_add fun s₂ o₂ e₂ => wp_strb (by decide) (by rw [e₂, o₁.get .x3, o₁.get .x5, hI.x3, hI.x5, ptr_zero])
      (by rw [o₂.wr, o₁.wr, hI.wr, hwr]; exact ⟨_, .head _, hc⟩) fun s₃ h₃ =>
      wp_addImm (by decide) fun s₄ o₄ e₄ => wp_nil ?_
    have k₄ := ((o₁.keep.trans o₂.keep).trans h₃.keep).trans o₄.keep
    have m₄ : s₄.mem = s.mem.writeW (s₀.gpr .x3 + BitVec.ofNat 64 (hpT s₀ i j).2) (BitVec.ofNat 8 j) := by
      rw [o₄.mem, h₃.mem, o₂.mem, o₁.mem, o₂.get .x7, o₁.get .x7, hI.x7, lowByte]
    have hT1 : hpT s₀ i (j + 1) = ((hpT s₀ i j).1.set! (hpT s₀ i j).2 (BitVec.ofNat 8 j), (hpT s₀ i j).2 + 1) := by
      rw [hT, hpStep, h1]; rfl
    refine coefTail_ok hj (by rw [k₄.get .x0, hI.x0]) (by rw [k₄.get .x3, hI.x3])
      (by rw [e₄, h₃.gpr, o₂.get .x5, o₁.get .x5, hI.x5, hT1, ofNat_succ64]) (by rw [k₄.get .x6, hI.x6])
      (by rw [k₄.get .x7, hI.x7]) (by rw [k₄.get .x8, hI.x8]) (by rw [k₄.get .x12, hI.x12]) (by rw [k₄.rd, hI.rd])
      (by rw [k₄.wr, hI.wr]) (by rw [k₄.sp, hI.sp]) ?_ ?_
    · rw [m₄]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [m₄, bytesAt_writeW8 _ _ hlt (by omega), hI.y, hT1]
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · -- A 0.
    rw [hb] at h0
    have hT0 : hpT s₀ i (j + 1) = hpT s₀ i j := by rw [hT, hpStep, h0]; rfl
    refine WP.block_nil (coefTail_ok hj (by rw [o₁.get .x0, hI.x0]) (by rw [o₁.get .x3, hI.x3])
      (by rw [o₁.get .x5, hI.x5, hT0]) (by rw [o₁.get .x6, hI.x6]) (by rw [o₁.get .x7, hI.x7])
      (by rw [o₁.get .x8, hI.x8]) (by rw [o₁.get .x12, hI.x12]) (by rw [o₁.rd, hI.rd]) (by rw [o₁.wr, hI.wr])
      (by rw [o₁.sp, hI.sp]) (by rw [o₁.mem]; exact hI.frame) (by rw [o₁.mem, hI.y, hT0]))

/-- Before polynomial `i`. -/
structure HPInv (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (4 * (256 * i))
  x3 : s.gpr .x3 = s₀.gpr .x3
  x5 : s.gpr .x5 = BitVec.ofNat 64 (hpS s₀ i).2
  x6 : s.gpr .x6 = s₀.gpr .x3 + BitVec.ofNat 64 (hω s₀ + i)
  x12 : (s.gpr .x12).toNat = hk s₀ - i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .x3) (hLen s₀) = (hpS s₀ i).1.toList

include hp in
theorem poly_ok {i : Nat} (hi : i < hk s₀) {s : State} (hP : HPInv s₀ i s) :
    WP isa hbpPoly s fun s' => HPInv s₀ (i + 1) s' ∧ ((s'.gpr .x12).toNat ≠ 0 ↔ i + 1 ≠ hk s₀) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr1⟩ := hp_facts hp
  have hwr := hp.2.1
  have hones : hintOnes (hH s₀) ≤ hω s₀ := hp.2.2.2.2.2.2
  unfold hbpPoly
  refine WP.seq (wp_movz fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ => wp_nil ?_)
  have k₂ := o₁.trans o₂
  refine WP.seq (WP.mono (count_loop (n := 256) (by decide) (CInv s₀ i)
    (fun j hj s hI => coef_ok hp hi hj hI) (s := s₂) ⟨by rw [k₂.get .x0, hP.x0, Nat.add_zero], by rw [k₂.get .x3, hP.x3],
      by rw [k₂.get .x5, hP.x5]; rfl, by rw [k₂.get .x6, hP.x6], by rw [o₂.get .x7, e₁]; rfl,
      by rw [e₂, toNat_imm]; rfl, by rw [k₂.get .x12, hP.x12], by rw [k₂.rd, hP.rd], by rw [k₂.wr, hP.wr],
      by rw [k₂.sp, hP.sp], by rw [k₂.mem]; exact hP.frame, by rw [k₂.mem, hP.y]; rfl⟩) fun s₃ hI => ?_)
  have hidx : (hpT s₀ i 256).2 < 2 ^ 8 := by
    have h1 : onesBefore (hH s₀) i 256 ≤ hintOnes (hH s₀) := onesBefore_n_le (hintAt_length _ _ _) hi
    rw [hpT_idx]; omega
  have hc : (yR s₀).Contains (s₀.gpr .x3 + BitVec.ofNat 64 (hω s₀ + i)) 1 := Offset.contains_base _ (by omega) (by omega)
  refine wp_strb (by decide) (by rw [hI.x6, ptr_zero]) (by rw [hI.wr, hwr]; exact ⟨_, .head _, hc⟩)
    fun s₄ h₄ => wp_addImm (by decide) fun s₅ o₅ e₅ => wp_subImm (by decide) fun s₆ o₆ e₆ => wp_nil ?_
  have k₆ := (h₄.keep.trans o₅.keep).trans o₆.keep
  have c12 : (s₆.gpr .x12).toNat = hk s₀ - (i + 1) := by
    rw [e₆, o₅.get .x12, h₄.gpr]; exact count_step hI.x12 hi
  have m₆ : s₆.mem = s₃.mem.writeW (s₀.gpr .x3 + BitVec.ofNat 64 (hω s₀ + i)) (BitVec.ofNat 8 (hpT s₀ i 256).2) := by
    rw [o₆.mem, o₅.mem, h₄.mem, hI.x5, lowByte]
  refine ⟨⟨?_, by rw [k₆.get .x3, hI.x3], by rw [k₆.get .x5, hI.x5, hpS_succ], ?_, c12, by rw [k₆.rd, hI.rd],
    by rw [k₆.wr, hI.wr], by rw [k₆.sp, hI.sp], ?_, ?_⟩, by rw [c12]; omega⟩
  · rw [k₆.get .x0, hI.x0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega]
  · rw [o₆.get .x6, e₅, h₄.gpr, hI.x6, ptr_add, Nat.add_assoc]
  · rw [m₆]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
  · rw [m₆, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, hpS_succ]
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

include hp in
theorem hbpMain_ok {s : State} (hI : hbpInitPost s₀ s) :
    WP isa hbpMain s fun s' => HPInv s₀ (hk s₀) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr1⟩ := hp_facts hp
  obtain ⟨hz, hf, h0, h3, h2, h12, hrd, hwr, hsp⟩ := hI
  have hl := (s₀.gpr .x4).isLt
  have e4 : hLen s₀ = (s₀.gpr .x4).toNat := rfl
  have hx12 : (s₀.gpr .x1 >>> 8).toNat = hk s₀ := by rw [lsr8_toNat, hr1]; omega
  have hx2 : s.gpr .x2 = BitVec.ofNat 64 (hω s₀) := by
    rw [h2]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hx12, toNat_ofNat_lt (by omega)]
    omega
  unfold hbpMain
  refine WP.seq (wp_movz fun s₁ o₁ e₁ => wp_add fun s₂ o₂ e₂ => wp_nil ?_)
  have k₂ := o₁.trans o₂
  refine count_loop (n := hk s₀) (by omega) (HPInv s₀) (fun i hi s hP => poly_ok hp hi hP)
    ⟨by rw [k₂.get .x0, h0]; exact (ptr_zero _).symm, by rw [k₂.get .x3, h3],
      by rw [o₂.get .x5, e₁]; rfl, by rw [e₂, o₁.get .x3, o₁.get .x2, h3, hx2, Nat.add_zero],
      by rw [k₂.get .x12, h12, hx12]; rfl, by rw [k₂.rd, hrd], by rw [k₂.wr, hwr], by rw [k₂.sp, hsp],
      by rw [k₂.mem]; exact hf, ?_⟩
  rw [k₂.mem]
  show _ = (Array.replicate (hω s₀ + hk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]
  exact bytesAt_eq (by simp) fun t ht => by rw [hz t ht]; simp

end

theorem hintBitPack_correct (s : State) (hs : hintBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.hintBitPack s t s' ∧ abiPreserved s s' ∧ hintBitPackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := WP.seq (c₁ := hbpInit) (c₂ := hbpMain)
    (WP.mono (hbpInit_ok hs) fun _ h => hbpMain_ok hs h)
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hb.y.trans (hintBitPack_eq _ _ _).symm⟩

/-! ## Constant time -/

/-- The public registers of the loops: the pointers, `k`, `ω`. -/
abbrev hbpTaint : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x0, .x2, .x3, .x12]

theorem hintBitPack_ct :
    ConstantTime isa hintBitPackK.pre hintBitPackK.pub Impl.MlDsa.AArch64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := memTaint.Agree hbpTaint) ?_
    (RelCT.taint (A := memTaint) hbpTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := hbpInitPost)
    (RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x3, .x4])
      (fun _ _ ⟨_, _, h0, h1, h3, h4, hsp, _⟩ => agree_of hsp (by simp [h0, h1, h3, h4])) (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨hbpInit_ok hx, hbpInit_ok hy⟩)) (fun _ _ h => h) fun x' y' ⟨_, x, y, ⟨hx, hy, hp⟩, fx, fy⟩ => ?_
  obtain ⟨hz₁, hf₁, a0, a3, a2, a12, rd₁, wr₁, sp₁⟩ := fx
  obtain ⟨hz₂, hf₂, b0, b3, b2, b12, rd₂, wr₂, sp₂⟩ := fy
  obtain ⟨p0, p1, p3, p4, psp, hleak⟩ := hp
  have hrd : x'.rd = y'.rd := by rw [rd₁, rd₂, hx.1, hy.1, p0, p1]
  have hwr : x'.wr = y'.wr := by rw [wr₁, wr₂, hx.2.1, hy.2.1, p3, p4]
  refine ⟨agree_of (by rw [sp₁, sp₂, psp]) fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a0, b0, p0]
    · rw [a2, b2, p4, p1]
    · rw [a3, b3, p3]
    · rw [a12, b12, p1]
  · rw [rd₁, wr₁, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      rw [hf₁ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'),
        hf₂ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [yR, hLen, ← p3, ← p4] at hc'
          exact hx.2.2.1 a hc hc')]
      exact bytes_of_words (by rw [← p0, ← p1] at hleak; exact hleak) hc
    · -- `y`: zeros.
      have hlt : (a - x.gpr .x3).toNat < (x.gpr .x4).toNat := by simp only [Region.Contains] at hc; omega
      have ea : a = x.gpr .x3 + BitVec.ofNat 64 (a - x.gpr .x3).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := hz₁ _ hlt
      have h₂ := hz₂ _ (show _ < (y.gpr .x4).toNat by rw [← p4]; exact hlt)
      rw [← p3, ← ea] at h₂
      rw [← ea] at h₁
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def hintBitPackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1024 | .x2 => 80 | .x3 => 0x3000 | .x4 => 84 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

theorem hintBitPack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.hintBitPack (hintBitPackContract AArch64.abi) :=
  Verified.of_correct hintBitPack_correct hintBitPack_ct
    { pre := by sig_implies_pre [hintBitPackContract, hintBitPackSig, hintBitPackK, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [hintBitPackContract, hintBitPackSig, hintBitPackK, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [hintBitPackContract, hintBitPackSig, hintBitPackK, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨hintBitPackSat, ?_⟩
        sig_pre [hintBitPackContract, hintBitPackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | (rw [hintOnes_zero]; exact Nat.zero_le _)
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack
