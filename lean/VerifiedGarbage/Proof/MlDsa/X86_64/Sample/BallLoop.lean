import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMaskLoop
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball

/-!
# ML-DSA on x86-64: the loops of `vg_mldsa_sample_in_ball`

The polynomial `c` is kept in memory as the words that represent its
coefficients modulo `q` (`CStored`); the first loop zeroes it (`bZero_ok`),
and an iteration of the second does what `bStep` does to it and to `i` (in
`rdi`), with the sign bits not yet used in `r9` (`bBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt coeffAt IPoly n)
open VG.Impl.MlKem.X86_64 (at_)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-! ## Zeroing -/

/-- After `k` iterations of the zeroing loop. -/
structure ZAt (s₀ : State) (aP : Addr) (k : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = aP + BitVec.ofNat 64 (4 * k)
  rax : s.gpr .rax = 0
  keep : Keep [.rax, .rdi, .rcx] s₀ s
  frame : Frame [pR aP] s₀.mem s.mem
  zero : ∀ j < k, coeffAt s.mem aP j = 0

theorem zStep_ok (s : State) {a : Addr} (ha : s.gpr .rdi = a) (hw : InRegions s.wr a 4) :
    WP isa (.block [.store32 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a ((s.gpr .rax).setWidth 32) ∧ s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 4 ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [ha, hw]
  rfl

/-- The zeroing loop: the 256 coefficients at `rbp` set to 0. -/
theorem bZero_ok (s₀ : State) {aP : Addr} (hbp : s₀.gpr .rbp = aP) (hw : pR aP ∈ s₀.wr) :
    WP isa bZero s₀ fun s => Keep [.rax, .rdi, .rcx] s₀ s ∧ Frame [pR aP] s₀.mem s.mem ∧
      CStored s.mem aP (Vector.replicate n 0) := by
  refine WP.seq (WP.mono (WP.keep [.rax, .rdi] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .rax = 0 ∧
      s.gpr .rdi = aP) (by xrun [hbp]) (by decide)) fun s1 ⟨⟨hm1, hax, hdi⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s => s.mem = s1.mem ∧ s.gpr .rcx = BitVec.ofNat 64 256)
    (by xrun) (by decide)) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_)
  refine wp_countdown (N := 256) (by decide) (by decide) (ZAt s₀ aP) (fun k hk s hI _ => ?_)
    (fun s h => ⟨h.keep, h.frame, fun j hj => ?_⟩)
    ⟨by rw [k2.gpr (by decide), hdi]; simp, by rw [k2.gpr (by decide), hax], (k1.trans k2).mono (by simp),
      by rw [hm2, hm1]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ hcx
  · have ha : s.gpr .rdi = coeffAddr aP k := by rw [hI.rdi]
    refine WP.mono (zStep_ok s ha (by rw [hI.keep.2.2]; exact ⟨_, hw, coeff_contains _ hk⟩))
      fun s' ⟨⟨hm, hdi', hcx', hz⟩, k'⟩ => ⟨⟨?_, by rw [k'.gpr (by decide), hI.rax], hI.keep.trans k' |>.mono (by simp),
        ?_, fun j hj => ?_⟩, hcx', hz⟩
    · rw [hdi', hI.rdi, offAdd, Nat.mul_succ]
    · rw [hm]; exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk)
    · rw [hm, coeffAt_writeW _ _ (by omega) hk, hI.rax]
      by_cases e : k = j
      · rw [ifT e]; rfl
      · rw [ifF e]; exact hI.zero j (by omega)
  · rw [h.zero j hj, getElem!_pos _ j (by simp only [n]; omega), Vector.getElem_replicate]
    rfl

/-! ## Setting a coefficient -/

theorem and1_beq (x : BitVec 64) : ((x &&& 1) == 0) = !x.getLsbD 0 := by
  have h1 : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
    by_cases h : x.toNat % 2 = 1 <;> simp [h]
  rw [h2]
  by_cases h : x.toNat % 2 = 1
  · simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega
  · simp only [h, decide_false, Bool.not_false, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h1]; simp; omega

theorem ea_cJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    s.ea cJ = coeffAddr aP j := by
  simp only [State.ea, cJ, hbp, hax]
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem bSet1_ok (s : State) {a b : Addr} (hb : s.ea cJ = b) (ha : s.ea aJ = a)
    (hr : InRegions (s.rd ++ s.wr) b 4) (hw : InRegions s.wr a 4) :
    WP isa (.block [.mov32 .rdx (.mem cJ), .store32 aJ .rdx, .alu .test .r9 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW a (s.mem.readW b 32) ∧ s'.zf = some ((s.gpr .r9 &&& 1) == 0) ∧
        s'.gpr .r9 = s.gpr .r9) ∧ Keep [.rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by rfl)
  have ha' : (s.setReg .rdx (BitVec.setWidth 64 (s.mem.readW b 32))).ea aJ = a := by
    rw [← ha]; rfl
  xrun [hb, hr, hw, ha', sw32_64]

theorem bSet3_ok (s : State) {b : Addr} (hb : s.ea cJ = b) (hw : InRegions s.wr b 4) :
    WP isa (.block [.store32 cJ .rdx, .shift .shr .r9 1, .alu .add .rdi (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW b ((s.gpr .rdx).setWidth 32) ∧ s'.gpr .r9 = s.gpr .r9 >>> 1 ∧
        s'.gpr .rdi = s.gpr .rdi + 1) ∧ Keep [.r9, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hb, hw]

/-- The word of the sign: 1, or `q - 1` for -1. -/
theorem sgn_word (b : Bool) : (if b then (qImm - 1 : BitVec 32) else 1) = zw (ofInt (if b then -1 else 1)) := by
  cases b <;> decide

theorem movRdx_ok (s : State) (v : BitVec 32) :
    WP isa (.block [.mov32 .rdx (.imm v)]) s fun s' => (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = v) ∧
      Keep [.rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sw32_64]

/-- The word of the sign `b`. -/
theorem bSign_ok (s : State) (b : Bool) (hz : s.zf = some (!b)) :
    WP isa (.ite .e (.block [.mov32 .rdx (.imm 1)]) (.block [.mov32 .rdx (.imm (qImm - 1))])) s fun s' =>
      (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = (if b then qImm - 1 else 1)) ∧ Keep [.rdx] s s' := by
  cases b
  · exact WP.ite true hz (fun _ => movRdx_ok s 1) (fun h => absurd h (by decide))
  · exact WP.ite false hz (fun h => absurd h (by decide)) (fun _ => movRdx_ok s (qImm - 1))

/-- `c[i] ← c[j]`, `c[j] ← ±1` (with the sign bit 0 of `r9`), `i` incremented. -/
theorem bSet_ok (s : State) {aP : Addr} {c : IPoly} {i j : Nat} (hij : j ≤ i) (hi : i < 256)
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (hw : pR aP ∈ s.wr) (hrd : pR aP ∈ s.rd ++ s.wr) (hst : CStored s.mem aP c) :
    WP isa bSet s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (i + 1) ∧
      CStored s'.mem aP ((c.set! i c[j]!).set! j (if (s.gpr .r9).getLsbD 0 then -1 else 1)) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .r9 = s.gpr .r9 >>> 1 ∧ Keep [.rdx, .r9, .rdi] s s' := by
  refine WP.seq (WP.mono (bSet1_ok s (ea_cJ s hbp hax) (ea_aJ s hbp hdi) ⟨_, hrd, coeff_contains _ (by omega)⟩
    ⟨_, hw, coeff_contains _ hi⟩) fun s1 ⟨⟨hm1, hz1, h91⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (bSign_ok s1 ((s.gpr .r9).getLsbD 0) (by rw [hz1, and1_beq]))
    fun s2 ⟨⟨hm2, hdx2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (bSet3_ok s2 (b := coeffAddr aP j) (ea_cJ s2 (by rw [k12.gpr (by decide), hbp])
    (by rw [k12.gpr (by decide), hax])) (by rw [k12.2.2]; exact ⟨_, hw, coeff_contains _ (by omega)⟩))
    fun s3 ⟨⟨hm3, h93, hdi3⟩, k3⟩ => ⟨?_, fun k hk => ?_, ?_, ?_, (k12.trans k3).mono (by simp)⟩
  · rw [hdi3, k12.gpr (by decide), hdi]; exact ofNat64_succ (by omega)
  · rw [hm3, hm2, hm1, hdx2, coeffAt_writeW _ _ hk (by omega), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega), ipoly_set!_get _ _ (by simp only [n]; omega)]
    by_cases ejk : j = k
    · subst ejk; rw [ifT rfl, ifT rfl, sgn_word]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : i = k
      · subst eik; rw [ifT rfl, ifT rfl, ← coeffAt_eq, hst j (by omega)]
      · rw [ifF eik, ifF eik]; exact hst k hk
  · rw [hm3, hm2, hm1]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by omega))
  · rw [h93, k2.gpr (by decide), h91]

/-! ## An iteration -/

theorem bLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (.block [.movzx8 .rax (at_ .rsi 0), .alu .cmp .rdi (.reg .rax)]) s fun s' =>
      (s'.gpr .rax = BitVec.ofNat 64 (s.mem (s.gpr .rsi)).toNat ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < (s.mem (s.gpr .rsi)).toNat)) ∧ s'.mem = s.mem ∧
        s'.gpr .rdi = s.gpr .rdi) ∧ Keep [.rax, .rdi] s s' := by
  refine WP.keep _ ?_ (by rfl)
  have e : BitVec.setWidth 64 (s.mem (s.gpr .rsi)) = BitVec.ofNat 64 (s.mem (s.gpr .rsi)).toNat := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth64_8, BitVec.toNat_ofNat]; have := (s.mem (s.gpr .rsi)).isLt; omega
  xrun [h0, e]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .rsi)).isLt; omega)]

/-- The try of the byte at `rsi`, if `i < 256`. -/
theorem bMid_ok (s : State) {aP : Addr} {c : IPoly} {i : Nat} {τ : Nat} {h : Array Bool}
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hi : i ≤ 256) (hw : pR aP ∈ s.wr)
    (hrd : pR aP ∈ s.rd ++ s.wr) (hst : CStored s.mem aP c) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (hsg : i < 256 → (s.gpr .r9).getLsbD 0 = h.getD (i + τ - 256) false)
    (hcf : s.cf = some (decide (i < 256))) :
    WP isa (.ite .b bTry (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 ∧
      CStored s'.mem aP (bStep τ h (c, i) (s.mem (s.gpr .rsi))).1 ∧ Frame [pR aP] s.mem s'.mem ∧
      s'.gpr .r9 = (if (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 = i then s.gpr .r9 else s.gpr .r9 >>> 1) ∧
      Keep [.rax, .rdx, .r9, .rdi] s s' := by
  refine WP.ite (decide (i < 256)) hcf (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    have hl : (s.gpr .rdi).toNat = i := by rw [hdi, ofNat64_toNat (by omega)]
    refine WP.seq (WP.mono (bLoad_ok s h0) fun s1 ⟨⟨hax, hcf1, hm1, hdi1⟩, k1⟩ => ?_)
    rw [hl] at hcf1
    refine WP.ite (decide (i < (s.mem (s.gpr .rsi)).toNat)) hcf1 (fun hj => ?_) (fun hj => ?_)
    · simp only [decide_eq_true_eq] at hj
      have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) = (c, i) := by
        unfold bStep; rw [ifT (show (c, i).2 < n from hb), ifT hj]
      rw [e]
      exact WP.block_nil ⟨by rw [hdi1, hdi], by rw [hm1]; exact hst, by rw [hm1]; exact Frame.refl _ _,
        by rw [ifT rfl, k1.gpr (by decide)], k1.mono (by simp)⟩
    · simp only [decide_eq_false_iff_not] at hj
      have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) =
          ((c.set! i c[(s.mem (s.gpr .rsi)).toNat]!).set! (s.mem (s.gpr .rsi)).toNat
            (if h.getD (i + τ - 256) false then -1 else 1), i + 1) := by
        unfold bStep; rw [ifT (show (c, i).2 < n from hb), ifF hj]
      rw [e, ← hsg hb]
      have h91 : s1.gpr .r9 = s.gpr .r9 := k1.gpr (by decide)
      refine WP.mono (bSet_ok s1 (aP := aP) (c := c) (by omega) hb (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hax
        (by rw [k1.2.2]; exact hw) (by rw [k1.2.1, k1.2.2]; exact hrd) (by rw [hm1]; exact hst))
        fun s2 ⟨hdi2, hst2, hf2, h92, k2⟩ => ⟨hdi2, by rw [h91] at hst2; exact hst2,
          by rw [← hm1]; exact hf2, by rw [ifF (by omega), h92, h91], (k1.trans k2).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    have e : bStep τ h (c, i) (s.mem (s.gpr .rsi)) = (c, i) := by
      unfold bStep; rw [ifF (show ¬ (c, i).2 < n from hb)]
    rw [e]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, by rw [ifT rfl], Keep.refl _ _⟩

/-- An iteration: what `bStep` does to the polynomial and `i`. -/
theorem bBody_ok (s : State) {aP : Addr} {c : IPoly} {i : Nat} {τ : Nat} {h : Array Bool}
    (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 i) (hi : i ≤ 256) (hw : pR aP ∈ s.wr)
    (hrd : pR aP ∈ s.rd ++ s.wr) (hst : CStored s.mem aP c) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (hsg : i < 256 → (s.gpr .r9).getLsbD 0 = h.getD (i + τ - 256) false) :
    WP isa bBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 ∧
      CStored s'.mem aP (bStep τ h (c, i) (s.mem (s.gpr .rsi))).1 ∧ Frame [pR aP] s.mem s'.mem ∧
      s'.gpr .r9 = (if (bStep τ h (c, i) (s.mem (s.gpr .rsi))).2 = i then s.gpr .r9 else s.gpr .r9 >>> 1) ∧
      s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r9, .rdi, .rsi, .rcx] s s' := by
  refine WP.seq (WP.mono (cmpRdi_ok s) fun s1 ⟨hcf1, hm1, hg1, hrd1, hwr1⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg1], hrd1, hwr1⟩
  refine WP.seq (WP.mono (bMid_ok s1 (aP := aP) (τ := τ) (h := h) (c := c) (by rw [hg1, hbp]) (by rw [hg1, hdi]) hi
    (by rw [hwr1]; exact hw) (by rw [hrd1, hwr1]; exact hrd) (by rw [hm1]; exact hst)
    (by rw [hrd1, hwr1, hg1]; exact h0) (by rw [hg1]; exact hsg)
    (by rw [hcf1, hdi, ofNat64_toNat (by omega)])) fun s2 ⟨hdi2, hst2, hf2, h92, k2⟩ => ?_)
  rw [hm1, hg1] at hdi2 hst2 h92
  rw [hm1] at hf2
  refine WP.mono (step_ok s2 1) fun s3 ⟨⟨hsi3, hcx3, hz3, hm3⟩, k3⟩ => ?_
  have hsi2 : s2.gpr .rsi = s.gpr .rsi := by rw [k2.gpr (by decide), hg1]
  have hcx2 : s2.gpr .rcx = s.gpr .rcx := by rw [k2.gpr (by decide), hg1]
  exact ⟨by rw [k3.gpr (by decide), hdi2], by rw [hm3]; exact hst2, by rw [hm3]; exact hf2,
    by rw [k3.gpr (by decide), h92], by rw [hsi3, hsi2, sx1'], by rw [hcx3, hcx2], by rw [hz3, hcx2],
    ((k1.trans k2).trans k3).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample