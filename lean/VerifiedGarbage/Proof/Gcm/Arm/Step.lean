import VerifiedGarbage.Impl.Gcm.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Straight
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# GHASH on ARMv7: the steps of Algorithm 1

Untrusted: everything here is checked by Lean. What the instructions of a
step (`Impl.Gcm.Arm.step`) compute on the four words of a 128-bit value,
stated on the whole value; a byte of `x` (8 steps); and the 16 bytes.
-/

namespace VG.Proof.Gcm.Arm

open VG VG.Arm VG.Impl.Gcm.Arm VG.Proof.Gcm
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsl wp_mov wp_add wp_sub wp_cmp wp_ldrb)
open VG.Spec.Gcm (Block)

/-! ## Four words as a block -/

/-- Four words, the most significant first. -/
def w4 (a b c d : BitVec 32) : Block := a ++ b ++ c ++ d

theorem getLsbD_w4 (a b c d : BitVec 32) (i : Nat) :
    (w4 a b c d).getLsbD i =
      if i < 32 then d.getLsbD i else if i < 64 then c.getLsbD (i - 32)
      else if i < 96 then b.getLsbD (i - 64) else a.getLsbD (i - 96) := by
  simp only [w4, BitVec.getLsbD_append]
  repeat' split
  all_goals first | omega | rfl

/-- `x >>> 31 − 1` is all ones if the top bit of `x` is clear, and zero otherwise. -/
theorem neg_top (x : BitVec 32) :
    x >>> 31 - 1 = if (!x.msb) = true then BitVec.allOnes 32 else 0 := by
  have h : x >>> 31 = if x.msb then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
    rcases (by omega : i = 0 ∨ 0 < i) with h | h
    · subst h; cases x.getLsbD (32 - 1) <;> simp
    · simp only [show 31 + i ≥ 32 by omega, BitVec.getLsbD_of_ge]
      split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  rw [h]; cases x.msb <;> decide

/-- `((v ∧ 1) ⊕ 1) − 1` is all ones if the lowest bit of `v` is set, and zero otherwise. -/
theorem lsb_mask (v : BitVec 32) :
    (v &&& 1 ^^^ 1) - 1 = if v.getLsbD 0 then BitVec.allOnes 32 else 0 := by
  have h : v &&& 1 = if v.getLsbD 0 then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and]
    rcases (by omega : i = 0 ∨ 0 < i) with h | h
    · subst h; cases v.getLsbD 0 <;> simp
    · split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  rw [h]; cases v.getLsbD 0 <;> decide

theorem w4_xor (a b c d a' b' c' d' : BitVec 32) :
    w4 a b c d ^^^ w4 a' b' c' d' = w4 (a ^^^ a') (b ^^^ b') (c ^^^ c') (d ^^^ d') := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_w4, getLsbD_w4, getLsbD_w4]
  by_cases h1 : i < 32 <;> by_cases h2 : i < 64 <;> by_cases h3 : i < 96 <;>
    simp [h1, h2, h3, BitVec.getLsbD_xor]

theorem mask_z4 (z0 z1 z2 z3 v0 v1 v2 v3 : BitVec 32) (c : Bool) :
    w4 (z0 ^^^ (v0 &&& if c then BitVec.allOnes 32 else 0))
        (z1 ^^^ (v1 &&& if c then BitVec.allOnes 32 else 0))
        (z2 ^^^ (v2 &&& if c then BitVec.allOnes 32 else 0))
        (z3 ^^^ (v3 &&& if c then BitVec.allOnes 32 else 0)) =
      if c then w4 z0 z1 z2 z3 ^^^ w4 v0 v1 v2 v3 else w4 z0 z1 z2 z3 := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, w4_xor]

/-- The shifts and `eor`s of `V` shift the four words right by one bit. -/
theorem shr4 (a b c d : BitVec 32) :
    w4 (a >>> 1) (b >>> 1 ^^^ a <<< 31) (c >>> 1 ^^^ b <<< 31) (d >>> 1 ^^^ c <<< 31) =
      w4 a b c d >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, getLsbD_w4, getLsbD_w4]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 31 ∨ i = 31 ∨ (32 ≤ i ∧ i < 63) ∨ i = 63 ∨ (64 ≤ i ∧ i < 95) ∨ i = 95 ∨
    (96 ≤ i ∧ i < 127) ∨ i = 127) with h | h | h | h | h | h | h | h
  · simp [h, show 1 + i < 32 by omega, show i < 32 by omega]
  · subst h; simp
  · simp [show ¬ i < 32 by omega, show i < 64 by omega, show 1 + i < 64 by omega,
      show ¬ 1 + i < 32 by omega, show i - 32 < 31 by omega, show 1 + (i - 32) = 1 + i - 32 by omega]
  · subst h; simp
  · simp [show ¬ i < 64 by omega, show i < 96 by omega, show 1 + i < 96 by omega,
      show ¬ 1 + i < 64 by omega, show ¬ i < 32 by omega, show ¬ 1 + i < 32 by omega,
      show i - 64 < 31 by omega, show 1 + (i - 64) = 1 + i - 64 by omega]
  · subst h; simp
  · simp [show ¬ i < 96 by omega, show ¬ 1 + i < 96 by omega, show ¬ i < 64 by omega,
      show ¬ 1 + i < 64 by omega, show ¬ i < 32 by omega, show ¬ 1 + i < 32 by omega,
      show 1 + (i - 96) = 1 + i - 96 by omega]
  · subst h; simp

theorem R_eq4 : Spec.Gcm.R = w4 0xE1000000 0 0 0 := by decide

theorem update_v4 (v0 v1 v2 v3 : BitVec 32) :
    w4 (v0 >>> 1 ^^^ ((if v3.getLsbD 0 then BitVec.allOnes 32 else 0) &&& 0xE1000000))
        (v1 >>> 1 ^^^ v0 <<< 31) (v2 >>> 1 ^^^ v1 <<< 31) (v3 >>> 1 ^^^ v2 <<< 31) =
      if (w4 v0 v1 v2 v3).getLsbD 0 then (w4 v0 v1 v2 v3 >>> 1) ^^^ Spec.Gcm.R
      else w4 v0 v1 v2 v3 >>> 1 := by
  have h0 : (w4 v0 v1 v2 v3).getLsbD 0 = v3.getLsbD 0 := by rw [getLsbD_w4]; rfl
  rw [h0, ← shr4, R_eq4]
  cases v3.getLsbD 0
  · simp
  · simp only [ite_true, BitVec.allOnes_and, w4_xor]
    simp

/-! ## One step -/

/-- `Z` and `V` in a state. -/
def zvOf (s : State) : Block × Block :=
  (w4 (s.gpr (Z 0)) (s.gpr (Z 1)) (s.gpr (Z 2)) (s.gpr (Z 3)),
   w4 (s.gpr (V 0)) (s.gpr (V 1)) (s.gpr (V 2)) (s.gpr (V 3)))

/-- The registers a step does not write. -/
def stepKeep : List Reg := [.r1, .r12, .lr]

set_option simprocs false in
theorem step_ok (x : Block) (k : Nat) (s : State) (xr : BitVec 32)
    (hx : s.gpr XR = xr) (hmsb : xr.msb = !(x.getMsbD k)) :
    WP isa (.block step) s fun s' =>
      s'.gpr XR = xr <<< 1 ∧ zvOf s' = mulStep x (zvOf s) k ∧
      (∀ r ∈ stepKeep, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  subst hx
  simp only [XR] at hmsb ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [step, XR, Z, V, M, T, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.setReg, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_, trivial⟩
  · simp only [zvOf, mulStep, Z, V]
    simp (config := {decide := true}) only [ite_true, ite_false]
    rw [neg_top, hmsb, Bool.not_not, mask_z4, lsb_mask, update_v4]
  · intro r hr
    simp only [stepKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp (config := {decide := true}) only [ite_false]

/-! ## A byte of `x` -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem ff_bit : ∀ u < 8, (0xFF : BitVec 32).getLsbD u = true := by decide

/-- The top bit of the inverted byte, shifted left by `t`, is the complement of bit `t` of the byte
(from the left). -/
theorem xr_msb (b : BitVec 8) {t : Nat} (ht : t < 8) :
    ((b.setWidth 32 ^^^ 0xFF) <<< 24 <<< t).msb = !(b.getMsbD t) := by
  have e : 32 - 1 - t - 24 = 7 - t := by omega
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getMsbD_eq_getLsbD, e, ff_bit _ (by omega)]
  simp [show ¬ 32 - 1 < t by omega, show ¬ 32 - 1 - t < 24 by omega, ht,
    show 31 - t < 32 by omega, show 7 - t < 32 by omega]

/-- The block `x` whose bits the steps use: its bytes at `y`. -/
structure Bytes (x : Block) (y : BitVec 32) (sB : State) : Prop where
  fit : y.toNat + 16 ≤ 2 ^ 32
  inr : (⟨State.addr y, 16⟩ : Region) ∈ sB.rd ++ sB.wr
  bits : ∀ j < 16, ∀ t < 8, (sB.mem (State.addr y + BitVec.ofNat 64 j)).getMsbD t = x.getMsbD (8 * j + t)

/-- After the bytes `0 … j − 1` of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (y : BitVec 32) (sB : State) (j : Nat) (s : State) : Prop where
  zv : zvOf s = mulSteps x h (8 * j)
  xp : s.gpr XP = y + BitVec.ofNat 32 j
  yp : s.gpr YP = y
  sb : s.gpr SB = sB.gpr SB
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem zvOf_eq {s s' : State} (h : ∀ r, r ≠ XR → r ≠ XP → r ≠ T → r ≠ M → s'.gpr r = s.gpr r) :
    zvOf s' = zvOf s := by
  simp only [zvOf, Z, V]
  rw [h .r2 (by decide) (by decide) (by decide) (by decide), h .r3 (by decide) (by decide) (by decide) (by decide),
    h .r4 (by decide) (by decide) (by decide) (by decide), h .r5 (by decide) (by decide) (by decide) (by decide),
    h .r6 (by decide) (by decide) (by decide) (by decide), h .r7 (by decide) (by decide) (by decide) (by decide),
    h .r8 (by decide) (by decide) (by decide) (by decide), h .r9 (by decide) (by decide) (by decide) (by decide)]

theorem beq_16 {j : Nat} (hj : j < 16) :
    (BitVec.ofNat 32 (j + 1) - 16 == 0) = decide (j + 1 = 16) := by
  by_cases h : j + 1 = 16
  · rw [h]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    bv_omega

theorem byte_ok {x h : Block} {y : BitVec 32} {sB : State} (hB : Bytes x y sB) {j : Nat} (hj : j < 16)
    {s : State} (hs : Inner x h y sB j s) :
    WP isa (.block steps) s fun s' => Inner x h y sB (j + 1) s' ∧ s'.z = decide (j + 1 = 16) := by
  have hfit := hB.fit
  rw [steps, WP.block_append_iff, WP.block_append_iff]
  have ha : State.addr (s.gpr XP + BitVec.ofNat 32 0) = State.addr y + BitVec.ofNat 64 j := by
    rw [hs.xp, BitVec.add_zero, addr_add (by omega)]
  have hin : InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 j) 1 := by
    rw [hs.rd, hs.wr, ← addr_add (by omega)]; exact Straight.in_off hB.inr hfit (by omega) (by decide)
  refine wp_ldrb (by decide) ha hin fun s₁ u₁ => ?_
  refine wp_eor (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_lsl (by decide)) fun s₃ u₃ =>
    wp_add (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  let b : BitVec 8 := sB.mem (State.addr y + BitVec.ofNat 64 j)
  have hx₄ : s₄.gpr XR = (b.setWidth 32 ^^^ 0xFF) <<< 24 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, hs.mem]
  have g₄ : ∀ r, r ≠ XR → r ≠ XP → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₄.other _ h2, u₃.other _ h1, u₂.other _ h1, u₁.other _ h1]
  have xp₄ : s₄.gpr XP = y + BitVec.ofNat 32 (j + 1) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hs.xp]
    bv_omega
  have zv₄ : zvOf s₄ = zvOf s := zvOf_eq fun r h1 h2 _ _ => g₄ r h1 h2
  let Inv : Nat → State → Prop := fun t s' =>
    s'.gpr XR = (b.setWidth 32 ^^^ 0xFF) <<< 24 <<< t ∧ zvOf s' = mulSteps x h (8 * j + t) ∧
    s'.gpr XP = y + BitVec.ofNat 32 (j + 1) ∧ s'.gpr YP = y ∧ s'.gpr SB = sB.gpr SB ∧
    s'.mem = sB.mem ∧ s'.rd = sB.rd ∧ s'.wr = sB.wr ∧ s'.sp = sB.sp
  have hI₀ : Inv 0 s₄ := by
    refine ⟨by rw [hx₄, BitVec.shiftLeft_zero], by rw [zv₄, hs.zv, Nat.add_zero], xp₄, by rw [g₄ _ (by decide) (by decide), hs.yp],
      by rw [g₄ _ (by decide) (by decide), hs.sb], ?_, ?_, ?_, ?_⟩
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hs.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hs.wr]
    · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hs.sp]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) Inv (fun t s' ht hI => ?_) 8 (Nat.le_refl _) s₄ hI₀)
    fun s₅ hI₅ => ?_
  · obtain ⟨hx, hzv, hxp, hyp, hsb, hm, hrd, hwr, hsp⟩ := hI
    refine WP.mono (step_ok x (8 * j + t) s' _ hx ?_) fun s'' ⟨hx', hzv', hk, hm', hrd', hwr', hsp'⟩ => ?_
    · rw [xr_msb _ ht, ← hB.bits j hj t ht]
    · refine ⟨by rw [hx', BitVec.shiftLeft_add], by rw [hzv', hzv, ← Nat.add_assoc, mulSteps_succ],
        (hk XP (by decide)).trans hxp, (hk YP (by decide)).trans hyp,
        (hk SB (by decide)).trans hsb, hm'.trans hm, hrd'.trans hrd, hwr'.trans hwr,
        hsp'.trans hsp⟩
  · obtain ⟨-, hzv, hxp, hyp, hsb, hm, hrd, hwr, hsp⟩ := hI₅
    refine wp_sub (op2_reg _ _) fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
    have t₆ : s₆.gpr T = BitVec.ofNat 32 (j + 1) := by
      rw [u₆.gpr, hxp, hyp]; bv_omega
    have g₇ : ∀ r, r ≠ T → s₇.gpr r = s₅.gpr r := fun r hr => by rw [f₇.gpr, u₆.other _ hr]
    refine ⟨⟨?_, by rw [g₇ _ (by decide)]; exact hxp, by rw [g₇ _ (by decide)]; exact hyp,
      by rw [g₇ _ (by decide)]; exact hsb, by rw [f₇.mem, u₆.mem]; exact hm,
      by rw [f₇.rd, u₆.rd]; exact hrd, by rw [f₇.wr, u₆.wr]; exact hwr,
      by rw [f₇.sp, u₆.sp]; exact hsp⟩, ?_⟩
    · rw [zvOf_eq (fun r _ _ h3 _ => g₇ r h3), hzv, Nat.mul_succ]
    · rw [z₇, t₆, beq_16 hj]

/-! ## The 128 steps -/

theorem mul_ok {x h : Block} {y : BitVec 32} {sB : State} (hB : Bytes x y sB) {s : State}
    (hs : Inner x h y sB 0 s) : WP isa (.loop (.block steps) .ne) s (Inner x h y sB 16) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = 16 - j ∧ j < 16 ∧ Inner x h y sB j s)
    (fun m s ⟨j, hm, hj, hs⟩ => WP.mono (byte_ok hB hj hs) fun s' ⟨hs', hz⟩ => ?_) _ s
    ⟨0, rfl, by decide, hs⟩
  subst hm
  by_cases hl : j + 1 = 16
  · exact .inl ⟨(VG.Proof.MdStream.Arm.eval_ne s').trans (by rw [hz, hl]; rfl), hl ▸ hs'⟩
  · exact .inr ⟨(VG.Proof.MdStream.Arm.eval_ne s').trans (by rw [hz, decide_eq_false hl]; rfl), _,
      by omega, j + 1, rfl, by omega, hs'⟩

end VG.Proof.Gcm.Arm
