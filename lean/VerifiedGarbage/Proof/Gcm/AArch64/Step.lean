import VerifiedGarbage.Impl.Gcm.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH on AArch64: one step of Algorithm 1

Untrusted: everything here is checked by Lean. What the instructions of a
step (`Impl.Gcm.AArch64.step`) compute on the two halves of a 128-bit value,
stated on the whole value, and the 128 steps.
-/

open VG.PowLit

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64 VG.Impl.Gcm.AArch64 VG.Proof.Gcm
open VG.Spec.Gcm (Block)

/-! ## The bit manipulations -/

/-- `lsl hi, hi, 1; lsr t, lo, 63; orr hi, hi, t; lsl lo, lo, 1` shifts
`hi ++ lo` left by one bit. -/
theorem shl1 (a b : BitVec 64) : (a <<< 1 ||| b >>> 63) ++ b <<< 1 = (a ++ b) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < 64
  · by_cases h0 : i = 0
    · subst h0; simp
    · simp [h1, h0, hi, show i - 1 < 64 by omega]
  · by_cases h64 : i = 64
    · subst h64; simp
    · simp [h1, hi, show i - 64 < 64 by omega, show ¬ i - 1 < 64 by omega]
      rw [BitVec.getLsbD_of_ge b (63 + (i - 64)) (by omega), Bool.or_false,
        decide_eq_false (show i - 64 ≠ 0 by omega), decide_eq_false (show i ≠ 0 by omega)]
      simp only [Bool.not_false, Bool.true_and]
      congr 1

/-- `0 − (x >>> 63)` is all ones if the top bit of `x` is set, and zero otherwise. -/
theorem neg_msb (x : BitVec 64) :
    (0 : BitVec 64) - x >>> 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  have h : x >>> 63 = if x.msb then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
    rcases (by omega : i = 0 ∨ 0 < i) with h | h
    · subst h; cases x.getLsbD (64 - 1) <;> simp
    · simp only [show 63 + i ≥ 64 by omega, BitVec.getLsbD_of_ge]
      split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  rw [h]; split <;> decide

/-- `lsl t, lo, 63; lsr t, t, 63` isolates the lowest bit. -/
theorem neg_lsb (x : BitVec 64) :
    (0 : BitVec 64) - x <<< 63 >>> 63 = if x.getLsbD 0 then BitVec.allOnes 64 else 0 := by
  rw [neg_msb]
  have : (x <<< 63).msb = x.getLsbD 0 := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]; simp
  rw [this]

theorem mask_z (zh zl vh vl : BitVec 64) (c : Bool) :
    (zh ^^^ (vh &&& if c then BitVec.allOnes 64 else 0)) ++
      (zl ^^^ (vl &&& if c then BitVec.allOnes 64 else 0)) =
      if c then (zh ++ zl) ^^^ (vh ++ vl) else zh ++ zl := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_append]

theorem R_eq : Spec.Gcm.R = rHigh ++ 0#64 := by decide

/-- `lsr lo, lo, 1; lsl t, hi, 63; orr lo, lo, t; lsr hi, hi, 1` shifts
`hi ++ lo` right by one bit. -/
theorem shr1 (a b : BitVec 64) : a >>> 1 ++ (b >>> 1 ||| a <<< 63) = (a ++ b) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 63 ∨ i = 63 ∨ 64 ≤ i) with h | h | h
  · simp [h, show 1 + i < 64 by omega, show i < 64 by omega]
  · subst h; simp
  · simp only [show ¬ 1 + i < 64 by omega, show ¬ i < 64 by omega, ite_false]
    congr 1; omega

theorem update_v (vh vl : BitVec 64) :
    (vh >>> 1 ^^^ ((0 : BitVec 64) - vl <<< 63 >>> 63 &&& rHigh)) ++ (vl >>> 1 ||| vh <<< 63) =
      if (vh ++ vl).getLsbD 0 then ((vh ++ vl) >>> 1) ^^^ Spec.Gcm.R else (vh ++ vl) >>> 1 := by
  rw [neg_lsb, R_eq, BitVec.getLsbD_append, ← shr1]
  simp only [show (0 : Nat) < 64 by decide, ite_true]
  cases vl.getLsbD 0
  · simp
  · simp only [ite_true, BitVec.allOnes_and]
    rw [BitVec.xor_append, BitVec.xor_zero]

theorem msb_shiftLeft (x : Block) (k : Nat) : (x <<< k).msb = x.getMsbD k := by
  rw [BitVec.msb_eq_getMsbD_zero, BitVec.getMsbD_shiftLeft, Nat.zero_add]

/-! ## One step -/

/-- The registers a step does not write. -/
def stepKeep : List Reg := [.x0, .x1, .x2, .x3, .x4, RH, CNT, ZERO]

set_option simprocs false in
theorem step_ok (x : Block) (zv : Block × Block) (k : Nat) (s : State)
    (hx : s.gpr XH ++ s.gpr XL = x <<< k)
    (hzv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = zv)
    (hr : s.gpr RH = rHigh) (hz : s.gpr ZERO = 0) :
    WP isa (.block step) s fun s' =>
      s'.gpr XH ++ s'.gpr XL = x <<< (k + 1) ∧
      (s'.gpr ZH ++ s'.gpr ZL, s'.gpr VH ++ s'.gpr VL) = mulStep x zv k ∧
      (∀ r ∈ stepKeep, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hzv
  simp only [XH, XL, ZH, ZL, VH, VL, RH, ZERO] at hx hr hz ⊢
  apply WP.of_runBlock
  simp only [step, XH, XL, ZH, ZL, VH, VL, M, T, RH, ZERO]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, State.write, BitVec.setWidth_eq, Size.bits,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  and_intros
  · rw [shl1, hx, BitVec.shiftLeft_add]
  · have hmsb : (s.gpr .x5).msb = x.getMsbD k := by
      rw [← msb_shiftLeft, ← hx, BitVec.msb_append]; rfl
    rw [hz, neg_msb, hmsb, mask_z, hr, update_v]
    rfl
  · intro r hr
    simp only [stepKeep, RH, CNT, ZERO, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_false]
  all_goals trivial

/-! ## The 128 steps -/

/-- The registers the multiplication does not write. -/
def keepRegs : List Reg := [.x0, .x1, .x2, .x3, .x4]

theorem keep_sub {r : Reg} (h : r ∈ keepRegs) : r ∈ stepKeep := by
  simp only [keepRegs, stepKeep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

/-- After `k` steps of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (sB : State) (k : Nat) (s : State) : Prop where
  xr : s.gpr XH ++ s.gpr XL = x <<< k
  zv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = mulSteps x h k
  rh : s.gpr RH = rHigh
  zero : s.gpr ZERO = 0
  keep : ∀ r ∈ keepRegs, s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem inner_step {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s) :
    WP isa (.block step) s fun s' => Inner x h sB (k + 1) s' ∧ s'.gpr CNT = s.gpr CNT := by
  refine WP.mono (step_ok x _ k s hs.xr hs.zv hs.rh hs.zero)
    fun s' ⟨hx, hzv, hk, hm, hrd, hwr⟩ => ?_
  refine ⟨⟨hx, by rw [hzv, mulSteps_succ], by rw [hk _ (by simp [stepKeep]), hs.rh],
    by rw [hk _ (by simp [stepKeep]), hs.zero],
    fun r hr => by rw [hk r (keep_sub hr), hs.keep r hr], by rw [hm, hs.mem], by rw [hrd, hs.rd],
    by rw [hwr, hs.wr]⟩, hk _ (by simp [stepKeep])⟩

theorem Inner.of_gpr {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s)
    {s' : State} (hg : ∀ r, r ≠ CNT → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inner x h sB k s' where
  xr := by rw [hg XH (by decide), hg XL (by decide)]; exact hs.xr
  zv := by rw [hg ZH (by decide), hg ZL (by decide), hg VH (by decide), hg VL (by decide)]; exact hs.zv
  rh := by rw [hg RH (by decide)]; exact hs.rh
  zero := by rw [hg ZERO (by decide)]; exact hs.zero
  keep r hr := by
    have : r ≠ CNT := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hg r this]; exact hs.keep r hr
  mem := hm.trans hs.mem
  rd := hrd.trans hs.rd
  wr := hwr.trans hs.wr

set_option simprocs false in
theorem steps_ok {x h : Block} {sB : State} {j : Nat} (hj : j < 128 / unroll) {s : State}
    (hs : Inner x h sB (unroll * j) s) (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)) :
    WP isa (.block steps) s fun s' => Inner x h sB (unroll * (j + 1)) s' ∧
      s'.gpr CNT = BitVec.ofNat 64 (128 / unroll - (j + 1)) := by
  rw [steps, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := unroll)
    (fun k s' => Inner x h sB (unroll * j + k) s' ∧ s'.gpr CNT = s.gpr CNT)
    (fun k s' _ ⟨hs', hc'⟩ => WP.mono (inner_step hs') fun s'' ⟨h₁, h₂⟩ => ⟨h₁, h₂.trans hc'⟩)
    unroll (Nat.le_refl _) s ⟨hs, rfl⟩) fun s₁ ⟨hs₁, hc₁⟩ => ?_
  have e : 128 / unroll - j = (128 / unroll - (j + 1)) + 1 := by
    simp only [unroll] at hj ⊢; omega
  rw [e] at hc
  apply WP.of_runBlock
  simp only [CNT] at hc hc₁ ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, State.write, BitVec.setWidth_eq, Size.bits,
    ite_true, hc₁, hc, Option.some.injEq, exists_eq_left']
  have hlt : 128 / unroll - (j + 1) < 2 ^ 64 := by simp only [unroll]; omega
  generalize 128 / unroll - (j + 1) = c at hlt ⊢
  have e2 : BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 c := by bv_omega_using []
  rw [e2]
  refine ⟨?_, rfl⟩
  rw [Nat.mul_succ]
  exact hs₁.of_gpr (fun r hr => ite_eq_right hr) rfl rfl rfl

/-- The loop of `128 / unroll` iterations: all 128 steps. -/
theorem mul_ok {x h : Block} {sB s : State} (hs : Inner x h sB 0 s)
    (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll)) :
    WP isa (.loop (.block steps) (.nonzero .x CNT)) s (Inner x h sB 128) := by
  let Inv : Nat → State → Prop := fun m s =>
    ∃ j, m = 128 / unroll - j ∧ j < 128 / unroll ∧ Inner x h sB (unroll * j) s ∧
      s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)
  refine WP.loop (M := isa) Inv (fun m s ⟨j, hm, hj, hs, hc⟩ => ?_) _ s
    ⟨0, rfl, by decide, hs, hc⟩
  subst hm
  refine WP.mono (steps_ok hj hs hc) fun s' ⟨hs', hc'⟩ => ?_
  have hev : eval (.nonzero .x CNT) s' = some (BitVec.ofNat 64 (128 / unroll - (j + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hc']
  by_cases hlast : j + 1 = 128 / unroll
  · left
    rw [hlast, Nat.sub_self] at hev
    refine ⟨hev.trans (by decide), ?_⟩
    rw [hlast] at hs'
    exact hs'
  · right
    have hne : BitVec.ofNat 64 (128 / unroll - (j + 1)) ≠ 0 := by
      simp only [unroll] at hlast hj ⊢
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine ⟨hev.trans (by simpa using hne), _, by omega, j + 1, rfl, by omega, hs', hc'⟩

end VG.Proof.Gcm.AArch64
