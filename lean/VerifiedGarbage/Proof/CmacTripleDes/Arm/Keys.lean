import VerifiedGarbage.Proof.CmacTripleDes.Arm.Block
import VerifiedGarbage.Proof.CmacTripleDes.KeySchedule
import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit

/-!
# DES's key schedule on 32-bit ARM

Untrusted: everything here is checked by Lean.

`roundKeys` only moves bits of the key in `r0:r1` (its high and low words)
to the round keys' words it stores: the kernel checks it over the lane
domain (`roundKeys_check`), and `getLsbD_expandDesKey` says the bits are the
specification's.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.Arm
  VG.Proof.CmacTripleDes

/-- The round keys' words, at `r2`. -/
def kCfg : Cfg := { base := .r2, slots := 32, ext := .r2, exts := 0 }

/-- Bit `q` of word `w` (0 low, 1 high) of round key `j`: bit `rkSrc j (32 w + q)`
of the key. -/
def rkG (k q : Nat) : List Nat :=
  if q < (if k % 2 = 0 then 32 else 16) then [xAtom (rkSrc (k / 2) (32 * (k % 2) + q))] else []

theorem rkG_lo {j q : Nat} (hq : q < 32) : rkG (2 * j) q = [xAtom (rkSrc j q)] := by
  simp [rkG, hq, show 2 * j / 2 = j by omega]

theorem rkG_hi {j q : Nat} (hq : q < 16) : rkG (2 * j + 1) q = [xAtom (rkSrc j (32 + q))] := by
  simp [rkG, hq, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

theorem rkG_hi0 {j q : Nat} (hq : 16 ≤ q) : rkG (2 * j + 1) q = [] := by
  simp [rkG, show (2 * j + 1) % 2 = 1 by omega, show ¬ q < 16 by omega]

def kPost (e : Env (Nat × Nat)) : Bool := (List.range 32).all fun k => e.slot k == some (outWord (rkG k))

theorem roundKeys_check :
    check (lanes 32 6) kCfg (linExt 2) roundKeys (linEnv [(.r0, 0), (.r1, 1)]) kPost = true := by
  rw [roundKeys_eq]; decide +kernel

theorem rkG_lt : ∀ k < 32, ∀ q < 32, ∀ a ∈ rkG k q, a < 2 ^ 6 := by decide +kernel

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by decide +kernel

/-- The registers `roundKeys` writes. -/
def kWrites : List Reg := [.r6, .r7, .r8]

theorem roundKeys_kept : ([.r0, .r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12, .lr] : List Reg).all
    (fun r => roundKeys.all fun i => dstOf i != some r) = true := by
  rw [roundKeys_eq]; decide +kernel

/-- The round keys of the DES key in `r0:r1`, in `[r2 + 8 j]` and `[r2 + 8 j + 4]`. -/
theorem roundKeys_ok {s : State} (hok : Ok kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .r2) (2 * j + 1)) 32).setWidth 16 ++
          s'.mem.readW (wordAddr (s.gpr .r2) (2 * j)) 32 =
        (Spec.TripleDes.expandDesKey (s.gpr .r0 ++ s.gpr .r1)).getD j 0) ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .r2) (2 * j + 1)) 32) >>> 16 = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ kWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion kCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ roundKeys_check
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r0 else s.gpr .r1
  have hrel : Rel (LaneRel 6 (assign W (2 ^ 6))) kCfg (linExt 2) (linEnv [(.r0, 0), (.r1, 1)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun j a hj h => absurd hj (by simp [kCfg])),
      fun _ _ h => by cases h⟩
    simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
    split at h
    · rename_i hr
      simp only [beq_iff_eq] at hr; subst hr
      simp only [Option.some.injEq, exists_eq_left'] at h; subst h
      exact inWord_rel W (i := 0) (by decide)
    · split at h
      · rename_i _ hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel W (i := 1) (by decide)
      · simp at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  have hw : ∀ k < 32, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .r2) k) 32).getLsbD q = xorBits W (rkG k q) := by
    intro k hk q hq
    have h := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at h
    have := outWord_rel (rkG_lt k hk) (p.rel.slot k _ (by simp only [kCfg]; omega) h)
    rw [p.base] at this
    exact this q hq
  have hx : W 0 ++ W 1 = s.gpr .r0 ++ s.gpr .r1 := rfl
  refine ⟨s', hs', fun j hj => ?_, fun j hj => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_append, getLsbD_expandDesKey _ hj hq]
    have hs := rkSrc_lt j hj q hq
    by_cases h32 : q < 32
    · rw [ite_eq_left h32, hw (2 * j) (by omega) q h32, rkG_lo h32, xorBits_cons, xorBits_nil,
        Bool.xor_false, bit_xAtom W hs, hx]
    · rw [ite_eq_right h32, BitVec.getLsbD_setWidth, decide_eq_true (by omega : q - 32 < 16), Bool.true_and,
        hw (2 * j + 1) (by omega) (q - 32) (by omega), rkG_hi (by omega), show 32 + (q - 32) = q by omega,
        xorBits_cons, xorBits_nil, Bool.xor_false, bit_xAtom W hs, hx]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_ushiftRight]
    by_cases hq' : 16 + q < 32
    · rw [hw (2 * j + 1) (by omega) (16 + q) hq', rkG_hi0 (by omega)]
      simp
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp
  · have h := List.all_eq_true.mp roundKeys_kept r (by revert hr; cases r <;> decide)
    simp [h]

end VG.Proof.CmacTripleDes.Arm
