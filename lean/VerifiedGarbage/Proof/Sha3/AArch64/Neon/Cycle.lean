import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3 (piSrc rhoOff)

def dest (k : Nat) : Nat := cycle[k]!.1
def rotation (k : Nat) : Nat := cycle[k]!.2
def source (k : Nat) : Nat := if k = 0 then 1 else dest (k-1)
def Done (k i : Nat) : Prop := i ∈ (List.range k).map dest
instance (k i : Nat) : Decidable (Done k i) := inferInstanceAs (Decidable (i ∈ (List.range k).map dest))

theorem cycle_facts : ∀ k < 24,
    dest k < 25 ∧ source k < 25 ∧ 0 < rotation k ∧ rotation k < 64 ∧
    ¬ Done k (dest k) ∧ source (k+1) = dest k ∧
    piSrc (dest k%5) (dest k/5) = source k ∧ rhoOff (source k) = rotation k := by decide

theorem done_next (k i : Nat) : Done (k+1) i ↔ Done k i ∨ i = dest k := by
  simp only [Done,List.range_succ,List.map_append,List.map_singleton,List.mem_append,List.mem_singleton]

theorem done_all : ∀ i < 25, Done 24 i ↔ i ≠ 0 := by decide

/-- The cycle's destination and rotation are exactly pi and rho's coordinates. -/
theorem cycle_word (A : Spec.Sha3.State) {k : Nat} (hk : k < 24) :
    (Spec.Sha3.pi (Spec.Sha3.rho A))[dest k]! = (A[source k]!).rotateLeft (rotation k) := by
  obtain ⟨hd,hs,_,_,_,_,hp,hr⟩ := cycle_facts k hk
  have hpi := VG.Proof.Sha3.pi_get (Spec.Sha3.rho A)
    (x := dest k%5) (y := dest k/5) (by omega) (by omega)
  have hpiBang : (Spec.Sha3.pi (Spec.Sha3.rho A))[dest k%5+5*(dest k/5)]! =
      (Spec.Sha3.rho A)[piSrc (dest k%5) (dest k/5)]! := by
    rw [VG.Proof.Sha3.getElem!_eq _ (by omega),VG.Proof.Sha3.getElem!_eq _ (by simp only [piSrc]; omega)]
    exact hpi
  rw [show dest k%5+5*(dest k/5) = dest k by omega,hp] at hpiBang
  rw [hpiBang,VG.Proof.Sha3.getElem!_eq _ hs,VG.Proof.Sha3.rho_get A hs,
    hr,VG.Proof.Sha3.getElem!_eq A hs]

theorem cycle_zero (A : Spec.Sha3.State) :
    (Spec.Sha3.pi (Spec.Sha3.rho A))[0]! = A[0]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ (by decide),VG.Proof.Sha3.pi_get _ (x := 0) (y := 0) (by decide) (by decide),
    VG.Proof.Sha3.rho_get A (by decide),VG.Proof.Sha3.getElem!_eq A (by decide)]
  exact VG.Proof.Sha3.rotateLeft_zero _
end VG.Proof.Sha3.AArch64.Neon
