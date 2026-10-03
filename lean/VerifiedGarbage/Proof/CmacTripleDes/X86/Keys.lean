import VerifiedGarbage.Proof.CmacTripleDes.X86.Block
import VerifiedGarbage.Proof.CmacTripleDes.KeySchedule
import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit

/-!
# DES's key schedule on x86 (32-bit)

Untrusted: everything here is checked by Lean.

`roundKeys` only moves bits of the key at `[esi]` (its high word, then its
low word) to the round keys' words it stores at `[edi]`: the kernel checks it
over the lane domain (`roundKeys_check`, `linear_ok`), and
`getLsbD_expandDesKey` says the bits are the specification's.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86
  VG.Proof.CmacTripleDes

/-- The round keys' words at `edi`, and the key's two words at `esi`. -/
def kCfg : Cfg := { base := .edi, slots := 32, ext := .esi, exts := 2 }

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

/-- Every round key's words. -/
def kOuts : List (Nat × (Nat → List Nat)) := (List.range 32).map fun k => (k, rkG k)

theorem roundKeys_check :
    check (lanes 32 6) kCfg (linExt 0) roundKeys (linEnv []) (linPost kCfg.slots 6 kOuts) = true := by
  rw [roundKeys_eq]; lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` keeps. -/
def kKept : List Reg := [.eax, .edx, .esi, .edi, .ebp, .esp]

theorem roundKeys_kept : kKept.all (fun r => roundKeys.all fun i => i.dst != some r) = true := by
  rw [roundKeys_eq]; lit_decide

/-- The DES key at `esi`: its high word, then its low word. -/
abbrev desKey (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .esi) 0) 32 ++ s.mem.readW (wordAddr (s.gpr .esi) 1) 32

/-- The round keys of the DES key at `esi`, in `[edi + 8 j]` and `[edi + 8 j + 4]`. -/
theorem roundKeys_ok {s : State} (hok : Ok kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .edi) (2 * j + 1)) 32).setWidth 16 ++
          s'.mem.readW (wordAddr (s.gpr .edi) (2 * j)) 32 =
        (Spec.TripleDes.expandDesKey (desKey s)).getD j 0) ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .edi) (2 * j + 1)) 32) >>> 16 = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kKept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion kCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.mem.readW (wordAddr (s.gpr .esi) 0) 32
    else s.mem.readW (wordAddr (s.gpr .esi) 1) 32
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok roundKeys_check hok W (fun j i h => by simp at h)
    (fun j hj => by
      simp only [kCfg] at hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
  have hw : ∀ k < 32, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .edi) k) 32).getLsbD q = xorBits W (rkG k q) :=
    fun k hk q hq => hout k (rkG k) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) q hq
  have hx : W 0 ++ W 1 = desKey s := rfl
  refine ⟨s', hs', fun j hj => ?_, fun j hj => ?_, rd, wr,
    fun r hr => keep _ (List.all_eq_true.mp roundKeys_kept r hr), fr⟩
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

end VG.Proof.CmacTripleDes.X86
