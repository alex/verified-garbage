import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)

def pairR (p : Addr) : Region := ⟨p,400⟩
def wordAddr (p : Addr) (i : Nat) : Addr := p+BitVec.ofNat 64 (16*i)

def PairAt (m : Mem) (p : Addr) (A B : Spec.Sha3.State) : Prop :=
  ∀ i < 25, m.read (wordAddr p i) 16 = ofVDwords A[i]! B[i]!

theorem pair_contains (p : Addr) {i : Nat} (hi : i < 25) :
    (pairR p).Contains (wordAddr p i) 16 := Offset.contains_base p (by omega) (by omega)

/-- Load two packed states into the same register layout used by the verified rounds. -/
theorem load_ok {s : State} {p : Addr} {r : Reg} {A B : Spec.Sha3.State}
    (hr : s.gpr r = p) (hp : PairAt s.mem p A B) (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.load r)) s fun s' =>
      VChg allV s s' ∧ Pairs s' A B := by
  unfold Impl.Sha3.AArch64.Neon.Pair.load
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k s' => VChg allV s s' ∧ ∀ i < k, s'.v (vreg i) = ofVDwords A[i]! B[i]!)
    (fun k s' hk ⟨hchg,hvals⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨VChg.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_ldrq (t := vreg k) (a := wordAddr p k) (by omega)
    (by rw [hchg.gpr,hr]; rfl)
    (by rw [hchg.rd,hchg.wr]; exact hin k hk)
    fun s'' h => WP.block_nil_iff.mpr ⟨(hchg.trans h.chg).mono (fun v _ => allV_mem v),?_⟩
  intro i hi
  by_cases he : i = k
  · subst i
    rw [h.v,hchg.mem,hp k hk]
  · rw [h.get (vreg i) (by rw [ne_eq,vreg_inj i (by omega) k (by omega)]; exact he)]
    exact hvals i (by omega)
end VG.Proof.Sha3.AArch64.Neon
