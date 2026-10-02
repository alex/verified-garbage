import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono

/-!
# ML-DSA key generation: what it may leak, piece by piece

Two seeds that `ML-DSA.KeyGen_internal` may leak the same of (`keyGenLeak`)
have the same `ρ`, and each `RejBoundedPoly` of `ExpandS` leaks the same from
both (`keyGenLeak_rho`, `keyGenLeak_rej`); and the seeds of the samplers as
bytes (`integerToBytes_one`, `integerToBytes_two`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

theorem integerToBytes_one (x : Nat) : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem integerToBytes_two {x : Nat} (hx : x < 256) : integerToBytes x 2 = [BitVec.ofNat 8 x, 0] := by
  simp only [integerToBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.div_eq_of_lt hx]
  rfl

theorem keyGenSeeds_rho_length (p : Params) (ξ : List Byte) : (keyGenSeeds p ξ).1.length = 32 := by
  simp [keyGenSeeds, H_length]

theorem leakBytes_inj : ∀ {a b : List Byte}, leakBytes a = leakBytes b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, y :: b, h => by
    simp only [leakBytes, List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]

theorem length_flatMap_pairs {α : Type} (f g : α → Nat) : ∀ l : List α, (l.flatMap fun z => [f z, g z]).length = 2 * l.length
  | [] => rfl
  | z :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_pairs f g l, List.length_cons]; simp; omega

theorem rejBoundedLeak_length (η : Nat) (ρ : List Byte) : (rejBoundedLeak η ρ).length = 2 * 1088 := by
  unfold rejBoundedLeak
  rw [length_flatMap_pairs, H_length]; rfl

theorem flatMap_range_inj {f g : Nat → List Nat} {L : Nat} (hf : ∀ r, (f r).length = L) (hg : ∀ r, (g r).length = L) :
    ∀ {n : Nat}, (List.range n).flatMap f = (List.range n).flatMap g → ∀ r < n, f r = g r
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, h, r, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
      List.flatMap_singleton] at h
    have hl : ((List.range n).flatMap f).length = ((List.range n).flatMap g).length := by
      simp only [List.length_flatMap, hf, hg]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    rcases (by omega : r < n ∨ r = n) with hr | rfl
    · exact flatMap_range_inj hf hg h1 r hr
    · exact h2

theorem keyGenLeak_split {p : Params} {ξ₁ ξ₂ : List Byte} (h : keyGenLeak p ξ₁ = keyGenLeak p ξ₂) :
    (keyGenSeeds p ξ₁).1 = (keyGenSeeds p ξ₂).1 ∧ ∀ r < p.ℓ + p.k,
      rejBoundedLeak p.η (seedS (keyGenSeeds p ξ₁).2.1 r) = rejBoundedLeak p.η (seedS (keyGenSeeds p ξ₂).2.1 r) := by
  unfold keyGenLeak at h
  have hl : (leakBytes (keyGenSeeds p ξ₁).1).length = (leakBytes (keyGenSeeds p ξ₂).1).length := by
    simp [leakBytes, keyGenSeeds_rho_length]
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨leakBytes_inj h1, flatMap_range_inj (fun _ => rejBoundedLeak_length _ _) (fun _ => rejBoundedLeak_length _ _) h2⟩

end VG.Proof.MlDsa.KeyGen
