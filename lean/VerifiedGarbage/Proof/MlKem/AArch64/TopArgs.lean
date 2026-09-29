import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall

/-!
# ML-KEM-768 on AArch64: buffers of the top-level functions

Untrusted: everything here is checked by Lean. The top-level functions use
buffers at offsets of their arguments: bytes `[o, o + l)` of argument `b`
(`R A b o l`, with `A b` its pointer and `L b` its length). Two such buffers
are disjoint if they are in different arguments, which are disjoint, or
apart in the same one (`R.disj`); each lies within its argument (`R.sub`),
and so apart from the stack below the stack pointer (`R.stk`). These reduce
the region facts the calls need to arithmetic on the offsets.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64

/-- Bytes `[o, o + l)` of argument `b`. -/
abbrev R (A : Nat → Addr) (b o l : Nat) : Region := ⟨A b + BitVec.ofNat 64 o, l⟩

/-- The arguments' regions `⟨A b, L b⟩` (for `b < nb`) are pairwise
disjoint, at most 32 KiB, and apart from the 16 bytes below `sp`. -/
structure ArgsOk (A : Nat → Addr) (L : Nat → Nat) (nb : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → Region.Disjoint ⟨A b, L b⟩ ⟨A c, L c⟩
  len : ∀ b < nb, L b ≤ 32768
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, L b⟩

theorem R.sub {A : Nat → Addr} {b o l len : Nat} (h : o + l ≤ len) :
    Region.Sub (R A b o l) ⟨A b, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - A b).toNat ≤ (x - (A b + BitVec.ofNat 64 o)).toNat + o := by
    rw [show x - A b = (x - (A b + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o by bv_omega, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem sub_offset' {p : Addr} {k n len : Nat} (h : k + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 k, n⟩ ⟨p, len⟩ :=
  R.sub (A := fun _ => p) (b := 0) h

theorem R.sub2 {A : Nat → Addr} {b o l o' l' : Nat} (h₁ : o' ≤ o) (h₂ : o + l ≤ o' + l') :
    Region.Sub (R A b o l) (R A b o' l') := by
  have e : R A b o l = ⟨A b + BitVec.ofNat 64 o' + BitVec.ofNat 64 (o - o'), l⟩ := by
    simp only [R, ptr_add, Nat.add_sub_cancel' h₁]
  rw [e]; exact sub_offset' (by omega)

theorem R.disj {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : ArgsOk A L nb sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ L b₁)
    (f₂ : o₂ + l₂ ≤ L b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R A b₁ o₁ l₁).Disjoint (R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem R.stk {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : ArgsOk A L nb sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ L b) : Region.Disjoint ⟨sp - 16, 16⟩ (R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

theorem R.cov {A : Nat → Addr} {b o l len : Nat} {X : List Region} (hm : (⟨A b, len⟩ : Region) ∈ X)
    (f : o + l ≤ len) : Covers [R A b o l] X :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hm, o, rfl, f⟩

theorem in_R {A : Nat → Addr} {b o l : Nat} {X : List Region} (hc : Covers [R A b o l] X) {k n : Nat}
    (hk : k + n ≤ l) (hl : l < 2 ^ 64) : InRegions X (A b + BitVec.ofNat 64 (o + k)) n :=
  hc _ _ ⟨_, List.mem_singleton_self _, by rw [← ptr_add]; exact contains_off hk hl⟩

theorem R.contains {A : Nat → Addr} {b o l k n : Nat} (hk : k + n ≤ l) (hl : l < 2 ^ 64) :
    (R A b o l).Contains (A b + BitVec.ofNat 64 (o + k)) n := by
  rw [← ptr_add]; exact contains_off hk hl

end VG.Proof.MlKem.AArch64
