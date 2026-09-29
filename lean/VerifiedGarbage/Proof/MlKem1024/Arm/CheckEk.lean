import VerifiedGarbage.Proof.MlKem.Arm.CheckEk
import VerifiedGarbage.Proof.MlKem.EkCheck1024
import VerifiedGarbage.Impl.MlKem1024.Arm.Poly
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_check_ek`

Untrusted: everything here is checked by Lean. The loop of
`vg_mlkem768_check_ek` (`Proof/MlKem/Arm/CheckEk.lean`, whose body and
counting this uses) over the 512 groups of a 1568-byte key: it counts the
12-bit fields that are at least `q` (`badCount`), and the key passes the
check exactly when there are none (`ekCheck1024`, `badCount_eq_zero`).
-/

namespace VG.Proof.MlKem1024.Arm.CheckEk

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
open VG.Proof.MlKem.Arm
open VG.Proof.MlKem.Arm.Add (ptr_succ)
open VG.Proof.MlKem.Arm.CheckEk (body_ok bad_toNat fld0_toNat fld1_toNat badCount badCount_le badN_le
  badCount_eq_zero ret_eq)

section
variable (s₀ : State)

abbrev pk : BitVec 32 := s₀.gpr .r0
abbrev K : Addr := State.addr (pk s₀)
abbrev E : List Byte := bytesAt s₀.mem (K s₀) 1568

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨K s₀, 1568⟩]
  wr : s₀.wr = []
  fitK : (pk s₀).toNat + 1568 ≤ 2 ^ 32

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pk s₀ + BitVec.ofNat 32 (3 * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (1 * (512 - i))
  r2 : s.gpr .r2 = BitVec.ofNat 32 (badCount (E s₀) i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 512) {s : State} (h : Inv s₀ i s) :
    WP isa (.block checkEkBody) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 512) := by
  have fK := hp.fitK
  have eb : ∀ k < 3, State.addr (pk s₀ + BitVec.ofNat 32 (3 * i) + BitVec.ofNat 32 k) =
      K s₀ + BitVec.ofNat 64 (3 * i + k) := fun k hk => addr_byte fK rfl (by omega)
  have hrw : s.rd ++ s.wr = [⟨K s₀, 1568⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
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
    have c0 := bad_toNat (F := CheckEk.fld0 ((E s₀).getD (3 * i) 0) ((E s₀).getD (3 * i + 1) 0))
      (by rw [fld0_toNat]; omega)
    have c1 := bad_toNat (F := CheckEk.fld1 ((E s₀).getD (3 * i + 1) 0) ((E s₀).getD (3 * i + 2) 0))
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

theorem loop_ok {s₀ : State} (hp : Pre s₀) :
    WP isa checkEk1024 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧
      s'.gpr .r0 = if badCount (E s₀) 512 = 0 then 1 else 0 := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, runBlock_cons.trans (by rfl), ?_⟩
  refine WP.seq (wp_loop_ne (Inv s₀) (N := 512) (by decide) (fun i hi s h => step hp hi h)
    (fun s h => ?_) ?_)
  swap
  · refine ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg, badCount], rfl, rfl,
      rfl, fun r hr => ?_, rfl⟩
    simp only [State.setReg]
    rw [ite_eq_right, ite_eq_right]
    all_goals intro e; subst e; simp [preserved] at hr
  · have hb := badCount_le (E s₀) 512
    run_block [h.r2]
    refine ⟨fun r hr => ?_, h.sp, ret_eq _ (by omega)⟩
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [ite_false] <;> exact h.pres _ (by decide)

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem1024.checkEkContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, Arm.abi, Arm.argRegs,
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
  rd := [⟨0x1000, 1568⟩]
  wr := []

theorem verified :
    Verified Arm.target checkEk1024 (Spec.MlKem1024.checkEkContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Taint.constantTime (A := VG.Arm.taint) (Taint.ofRegs [.r0])
    (fun s₁ s₂ _ _ hp => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h0⟩ := loop_ok hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    rw [setWidth_append32, h0]
    show (if badCount (E s) 512 = 0 then (1 : BitVec 32) else 0) =
      if ekCheck mlKem1024 (E s) = true then 1 else 0
    have hE : (E s).length = 1568 := bytesAt_length _ _ _
    by_cases hc : ekCheck mlKem1024 (E s) = true
    · rw [ite_eq_left ((badCount_eq_zero _ 512).mpr ((ekCheck1024 _ hE).mp hc)), ite_eq_left hc]
    · rw [ite_eq_right (fun h => hc ((ekCheck1024 _ hE).mpr ((badCount_eq_zero _ 512).mp h))),
        ite_eq_right hc]
  · sig_pub [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hp
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hp.2
  · refine ⟨satState, ?_⟩
    sig_pre [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact ⟨by decide, rfl, rfl, by decide⟩

end VG.Proof.MlKem1024.Arm.CheckEk
