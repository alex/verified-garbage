import VerifiedGarbage.Proof.Framework.Pratt
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Spec.X448

/-!
# The Ed448 field prime `2^448 - 2^224 - 1` is prime

A Pratt certificate (`Proof/Framework/Pratt.lean`), one theorem per prime of
the tree. Factors below `2^16` are prime by `norm_num`.
-/

namespace VG.Proof.Ed448

open VG.Proof.Pratt

theorem prime_196687 : Nat.Prime 196687 := by
  refine prime_of_cert 196687 3 18 [2, 3, 3, 7, 7, 223] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_1466449 : Nat.Prime 1466449 := by
  refine prime_of_cert 1466449 7 21 [2, 2, 2, 2, 3, 137, 223] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_2916841 : Nat.Prime 2916841 := by
  refine prime_of_cert 2916841 13 22 [2, 2, 2, 3, 5, 109, 223] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_6700417 : Nat.Prime 6700417 := by
  refine prime_of_cert 6700417 5 23 [2, 2, 2, 2, 2, 2, 2, 3, 17449] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_411743 : Nat.Prime 411743 := by
  refine prime_of_cert 411743 10 19 [2, 29, 31, 229] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_1609403 : Nat.Prime 1609403 := by
  refine prime_of_cert 1609403 2 21 [2, 23, 59, 593] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_3402277943 : Nat.Prime 3402277943 := by
  refine prime_of_cert 3402277943 5 32 [2, 7, 151, 1609403] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_1609403

theorem prime_1469495262398780123809 : Nat.Prime 1469495262398780123809 := by
  refine prime_of_cert 1469495262398780123809 17 71 [2, 2, 2, 2, 2, 3, 7, 7, 223, 411743, 3402277943] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_411743
  · exact prime_3402277943

theorem prime_189989 : Nat.Prime 189989 := by
  refine prime_of_cert 189989 2 18 [2, 2, 47497] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num

theorem prime_379979 : Nat.Prime 379979 := by
  refine prime_of_cert 379979 2 19 [2, 189989] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · norm_num
  · exact prime_189989

theorem prime_97859369123353 : Nat.Prime 97859369123353 := by
  refine prime_of_cert 97859369123353 5 47 [2, 2, 2, 3, 3, 67, 197, 271, 379979] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_379979

theorem prime_167773885276849215533569 : Nat.Prime 167773885276849215533569 := by
  refine prime_of_cert 167773885276849215533569 17 78 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 2531, 97859369123353] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_97859369123353

theorem prime_217003 : Nat.Prime 217003 := by
  refine prime_of_cert 217003 3 18 [2, 3, 59, 613] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_1764234391 : Nat.Prime 1764234391 := by
  refine prime_of_cert 1764234391 3 31 [2, 3, 5, 271, 217003] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_217003

theorem prime_34741861125639557 : Nat.Prime 34741861125639557 := by
  refine prime_of_cert 34741861125639557 13 55 [2, 2, 7, 7, 7, 31, 463, 1764234391] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_1764234391

theorem prime_36131535570665139281 : Nat.Prime 36131535570665139281 := by
  refine prime_of_cert 36131535570665139281 3 65 [2, 2, 2, 2, 5, 13, 34741861125639557] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_34741861125639557

theorem prime_596242599987116128415063 : Nat.Prime 596242599987116128415063 := by
  refine prime_of_cert 596242599987116128415063 5 79 [2, 37, 223, 36131535570665139281] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_36131535570665139281

theorem prime_36753053 : Nat.Prime 36753053 := by
  refine prime_of_cert 36753053 2 26 [2, 2, 7, 443, 2963] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_116989 : Nat.Prime 116989 := by
  refine prime_of_cert 116989 10 17 [2, 2, 3, 9749] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_1255525949 : Nat.Prime 1255525949 := by
  refine prime_of_cert 1255525949 2 31 [2, 2, 2683, 116989] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_116989

theorem prime_1335912079 : Nat.Prime 1335912079 := by
  refine prime_of_cert 1335912079 6 31 [2, 3, 19, 31, 61, 6197] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_32061889897 : Nat.Prime 32061889897 := by
  refine prime_of_cert 32061889897 10 35 [2, 2, 2, 3, 1335912079] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_1335912079

theorem prime_25136521679249 : Nat.Prime 25136521679249 := by
  refine prime_of_cert 25136521679249 3 45 [2, 2, 2, 2, 7, 7, 32061889897] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_32061889897

theorem prime_37414057161322375957408148834323969 : Nat.Prime 37414057161322375957408148834323969 := by
  refine prime_of_cert 37414057161322375957408148834323969 23 115 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 36753053, 1255525949, 25136521679249] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_36753053
  · exact prime_1255525949
  · exact prime_25136521679249

theorem prime_P : Nat.Prime 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 := by
  refine prime_of_cert 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439 7 448 [2, 641, 18287, 196687, 1466449, 2916841, 6700417, 1469495262398780123809, 167773885276849215533569, 596242599987116128415063, 37414057161322375957408148834323969] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_196687
  · exact prime_1466449
  · exact prime_2916841
  · exact prime_6700417
  · exact prime_1469495262398780123809
  · exact prime_167773885276849215533569
  · exact prime_596242599987116128415063
  · exact prime_37414057161322375957408148834323969

theorem prime_field : Nat.Prime Spec.X448.P := by
  rw [show Spec.X448.P = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439
    by decide +kernel]
  exact prime_P

instance fact_prime_field : Fact (Nat.Prime Spec.X448.P) := ⟨prime_field⟩

/-- The field prime, as the modulus of `ZMod PZ`. Irreducible, so that the
elaborator never unfolds `ZMod PZ` by evaluating `2^448 - 2^224 - 1`, whose
exponent exceeds `exponentiation.threshold`. The kernel unfolds it
(`decide +kernel`). -/
@[irreducible] def PZ : Nat := Spec.X448.P

theorem PZ_eq : PZ = Spec.X448.P := by unfold PZ; rfl

theorem prime_PZ : Nat.Prime PZ := by rw [PZ_eq]; exact prime_field

instance fact_prime_PZ : Fact (Nat.Prime PZ) := ⟨prime_PZ⟩

instance neZero_PZ : NeZero PZ := ⟨prime_PZ.ne_zero⟩

end VG.Proof.Ed448
