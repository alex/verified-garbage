import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.CmacTripleDes.KeySchedule
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.KeysLit

/-!
# DES's key schedule on AArch64

`roundKeys` only moves bits of the key in `x5` to the round keys it
stores: the kernel checks it over the lane domain (`roundKeys_check`), and
`getLsbD_expandDesKey` says the bits are the specification's.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64
  VG.Proof.CmacTripleDes

/-- The round keys' slots, at `x2`. -/
def kCfg : Cfg := { base := .x2, slots := 16, ext := .x2, exts := 0 }

/-- Bit `q` of round key `j`: bit `rkSrc j q` of the key (input word 0). -/
def rkG (j q : Nat) : List Nat := if q < 48 then [rkSrc j q] else []

def kPost (e : Env (Nat × Nat)) : Bool := (List.range 16).all fun j => e.slot j == some (outWord (rkG j))

theorem roundKeys_check : check (lanes 64 6) kCfg (linExt 1) roundKeys (linEnv [(.x5, 0)]) kPost = true := by
  rw [roundKeys_eq]; lit_decide

theorem rkG_lt : ∀ j < 16, ∀ q < 64, ∀ a ∈ rkG j q, a < 2 ^ 6 := by lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` writes. -/
def kWrites : List Reg := [.x6, .x7, .x11]

/-- Every register `roundKeys` writes is one of `kWrites`: checked once
for every instruction, rather than once for every other register. -/
theorem roundKeys_writes : roundKeys.all (fun i => (dstOf i).all kWrites.contains) = true := by
  rw [roundKeys_eq]; lit_decide

theorem roundKeys_kept {r : Reg} (hr : r ∉ kWrites) : roundKeys.all (fun i => dstOf i != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have h := List.all_eq_true.mp roundKeys_writes i hi
    cases hd : dstOf i with
    | none => rfl
    | some d =>
      rw [hd, Option.all_some] at h
      have hd' : d ∈ kWrites := by simpa using h
      have hne : d ≠ r := fun e => hr (e ▸ hd')
      simpa using hne

/-- The round keys of the DES key in `x5`, in `[x2 + 8 j]`. -/
theorem roundKeys_ok {s : State} (hok : Ok kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, s'.mem.readW (wordAddr (s.gpr .x2) j) 64 =
        ((Spec.TripleDes.expandDesKey (s.gpr .x5)).getD j 0).zeroExtend 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ kWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion kCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ roundKeys_check
  let W : Nat → BitVec 64 := fun _ => s.gpr .x5
  have hrel : Rel (LaneRel 6 (assign W (2 ^ 6))) kCfg (linExt 1) (linEnv [(.x5, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun j a hj h => absurd hj (by simp [kCfg])),
      fun _ _ h => by cases h⟩
    simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
    split at h
    · rename_i hr
      simp only [beq_iff_eq] at hr; subst hr
      simp only [Option.some.injEq, exists_eq_left'] at h; subst h
      exact inWord_rel W (i := 0) (by decide)
    · simp at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at h
    have hw : ∀ q < 64, (s'.mem.readW (wordAddr (s.gpr .x2) j) 64).getLsbD q = xorBits W (rkG j q) := by
      have := outWord_rel (rkG_lt j hj) (p.rel.slot j _ (by simp only [kCfg]; omega) h)
      rwa [p.base] at this
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [hw q hq, BitVec.getLsbD_setWidth, rkG]
    by_cases h48 : q < 48
    · rw [ite_eq_left h48, getLsbD_expandDesKey _ hj h48]
      have := rkSrc_lt j hj q h48
      simp [xorBits, bitOf, W, hq, Nat.mod_eq_of_lt this]
    · rw [ite_eq_right h48, BitVec.getLsbD_of_ge _ _ (by omega)]
      simp
  · have h := roundKeys_kept hr
    simp [h]

end VG.Proof.CmacTripleDes.AArch64
