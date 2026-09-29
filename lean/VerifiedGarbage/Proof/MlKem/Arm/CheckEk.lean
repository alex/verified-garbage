import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.EkCheck

/-!
# ML-KEM-768 on 32-bit ARM: `vg_mlkem768_check_ek`

Untrusted: everything here is checked by Lean. The loop counts the 12-bit
fields that are at least `q` (`badCount`); the key passes the check exactly
when there are none (`ekCheck768`, `badCount_eq_zero`).
-/

namespace VG.Proof.MlKem.Arm.CheckEk

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

/-! ## The loop body -/

/-- 1 if the field `F < 2¹²` is at least `q`, as `countBad` computes it. -/
def bad (F : BitVec 32) : BitVec 32 := (3328 - F) >>> 31

/-- The first field of the bytes `b₀`, `b₁`. -/
def fld0 (b₀ b₁ : Byte) : BitVec 32 := ((b₁.setWidth 32 <<< 28) >>> 20) + b₀.setWidth 32

/-- The second field of the bytes `b₁`, `b₂`. -/
def fld1 (b₁ b₂ : Byte) : BitVec 32 := (b₁.setWidth 32 >>> 4) + (b₂.setWidth 32 <<< 4)

theorem body_ok {s : State} {x c a : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = c)
    (h2 : s.gpr .r2 = a)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 1)) 1)
    (i2 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 2)) 1) :
    WP isa (.block checkEkBody) s fun s' =>
      s'.gpr .r0 = x + 3 ∧ s'.gpr .r1 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.gpr .r2 = a + bad (fld0 (s.mem (State.addr (x + BitVec.ofNat 32 0)))
          (s.mem (State.addr (x + BitVec.ofNat 32 1)))) +
        bad (fld1 (s.mem (State.addr (x + BitVec.ofNat 32 1))) (s.mem (State.addr (x + BitVec.ofNat 32 2)))) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [checkEkBody, countBad, bad, fld0, fld1, h0, h1, h2, i0, i1, i2, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-! ## The values -/

/-- 1 if `F` is at least `q`. -/
def badN (F : Nat) : Nat := if F < q then 0 else 1

theorem bad_toNat {F : BitVec 32} (h : F.toNat < 4096) : (bad F).toNat = badN F.toNat := by
  unfold bad badN
  rw [q_eq]
  split <;> bv_omega

theorem fld0_toNat (b₀ b₁ : Byte) : (fld0 b₀ b₁).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
  have h₀ := b₀.isLt
  have h₁ := b₁.isLt
  rw [fld0, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat,
    setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem fld1_toNat (b₁ b₂ : Byte) : (fld1 b₁ b₂).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
  have h₁ := b₁.isLt
  have h₂ := b₂.isLt
  rw [fld1, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, setWidth32_toNat,
    setWidth32_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- The fields of the first `i` groups that are at least `q`. -/
def badCount (E : List Byte) : Nat → Nat
  | 0 => 0
  | i + 1 => badCount E i + badN (field0 E i) + badN (field1 E i)

theorem badCount_le (E : List Byte) : ∀ i, badCount E i ≤ 2 * i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have := badCount_le E i
    simp only [badCount, badN]
    split <;> split <;> omega

theorem badN_le (F : Nat) : badN F ≤ 1 := by
  unfold badN; split <;> omega

theorem badN_eq_zero (F : Nat) : badN F = 0 ↔ F < q := by
  unfold badN; split <;> simp_all

theorem badCount_eq_zero (E : List Byte) :
    ∀ i, badCount E i = 0 ↔ ∀ g < i, field0 E g < q ∧ field1 E g < q
  | 0 => by simp [badCount]
  | i + 1 => by
    rw [badCount, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, badCount_eq_zero E i, badN_eq_zero,
      badN_eq_zero, Nat.forall_lt_succ_right, and_assoc]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev pk : BitVec 32 := s₀.gpr .r0
abbrev K : Addr := State.addr (pk s₀)
abbrev E : List Byte := bytesAt s₀.mem (K s₀) 1184

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨K s₀, 1184⟩]
  wr : s₀.wr = []
  fitK : (pk s₀).toNat + 1184 ≤ 2 ^ 32

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pk s₀ + BitVec.ofNat 32 (3 * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (1 * (384 - i))
  r2 : s.gpr .r2 = BitVec.ofNat 32 (badCount (E s₀) i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 384) {s : State} (h : Inv s₀ i s) :
    WP isa (.block checkEkBody) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 384) := by
  have fK := hp.fitK
  have eb : ∀ k < 3, State.addr (pk s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 k) =
      K s₀ + BitVec.ofNat 64 (3 * i + k) := fun k hk => addr_byte fK rfl (by omega)
  have hrw : s.rd ++ s.wr = [⟨K s₀, 1184⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have ib : ∀ k < 3, InRegions (s.rd ++ s.wr) (State.addr (pk s₀ + BitVec.ofNat 32 (3 * i) +
      BitVec.ofNat 32 k)) 1 := fun k hk => by
    rw [eb k hk, hrw]; exact inRegions_off (List.mem_singleton_self _) (by omega) (by omega)
  have rb : ∀ k < 3, s.mem (State.addr (pk s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 k)) =
      (E s₀).getD (3 * i + k) 0 := fun k hk => by
    rw [eb k hk, h.mem, bytesAt_getD _ _ (by omega)]
  refine WP.mono (body_ok h.r0 h.r1 h.r2 (ib 0 (by omega)) (ib 1 (by omega)) (ib 2 (by omega)))
    fun s' ⟨r0, r1, z, r2, m, rd, wr, sp, pres⟩ =>
    ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr),
      m.trans h.mem⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 3 i
  · rw [r1]; exact count_sub (k := 1) hi
  · rw [r2, rb 0 (by omega), rb 1 (by omega), rb 2 (by omega), Nat.add_zero]
    have l0 := ((E s₀).getD (3 * i) 0).isLt
    have l1 := ((E s₀).getD (3 * i + 1) 0).isLt
    have l2 := ((E s₀).getD (3 * i + 2) 0).isLt
    have c0 := bad_toNat (F := fld0 ((E s₀).getD (3 * i) 0) ((E s₀).getD (3 * i + 1) 0))
      (by rw [fld0_toNat]; omega)
    have c1 := bad_toNat (F := fld1 ((E s₀).getD (3 * i + 1) 0) ((E s₀).getD (3 * i + 2) 0))
      (by rw [fld1_toNat]; omega)
    rw [fld0_toNat] at c0
    rw [fld1_toNat] at c1
    have hb := badCount_le (E s₀) i
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, c0, c1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, badCount]
    simp only [field0, field1]
    have := badN_le (((E s₀).getD (3 * i) 0).toNat + 256 * (((E s₀).getD (3 * i + 1) 0).toNat % 16))
    have := badN_le (((E s₀).getD (3 * i + 1) 0).toNat / 16 + 16 * ((E s₀).getD (3 * i + 2) 0).toNat)
    omega
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The return value. -/
theorem ret_eq (n : Nat) (hn : n < 2 ^ 31) :
    (1 : BitVec 32) - ((0 : BitVec 32) - BitVec.ofNat 32 n) >>> 31 = if n = 0 then 1 else 0 := by
  by_cases h : n = 0
  · subst h; decide
  · rw [ite_eq_right h]
    bv_omega

theorem loop_ok {s₀ : State} (hp : Pre s₀) :
    WP isa checkEk s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      s'.gpr .r0 = if badCount (E s₀) 384 = 0 then 1 else 0 := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), ?_⟩
  refine WP.seq (wp_loop_ne (Inv s₀) (N := 384) (by decide) (fun i hi s h => step hp hi h)
    (fun s h => ?_) ?_)
  swap
  · refine ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg, badCount], rfl, rfl,
      rfl, fun r hr => ?_, rfl⟩
    simp only [State.setReg]
    rw [ite_eq_right, ite_eq_right]
    all_goals intro e; subst e; simp [preserved] at hr
  · have hb := badCount_le (E s₀) 384
    run_block [h.r2]
    refine ⟨fun r hr => ?_, h.sp, ret_eq _ (by omega)⟩
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [ite_false] <;> exact h.pres _ (by decide)

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.checkEkContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1184⟩]
  wr := []

theorem verified :
    Verified Arm.target Impl.MlKem.Arm.checkEk (Spec.MlKem.checkEkContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Taint.constantTime (A := VG.Arm.taint) (Taint.ofRegs [.r0])
    (fun s₁ s₂ _ _ hp => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h0⟩ := loop_ok hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    rw [setWidth_append32, h0]
    show (if badCount (E s) 384 = 0 then (1 : BitVec 32) else 0) =
      if ekCheck mlKem768 (E s) = true then 1 else 0
    have hE : (E s).length = 1184 := bytesAt_length _ _ _
    by_cases hc : ekCheck mlKem768 (E s) = true
    · rw [ite_eq_left ((badCount_eq_zero _ 384).mpr ((ekCheck768 _ hE).mp hc)), ite_eq_left hc]
    · rw [ite_eq_right (fun h => hc ((ekCheck768 _ hE).mpr ((badCount_eq_zero _ 384).mp h))),
        ite_eq_right hc]
  · sig_pub [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hp
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hp.2
  · refine ⟨satState, ?_⟩
    sig_pre [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact ⟨by decide, rfl, rfl, by decide⟩

end VG.Proof.MlKem.Arm.CheckEk
