import VerifiedGarbage.Proof.Framework.Pratt
import Mathlib.Tactic.NormNum.Prime
import VerifiedGarbage.Spec.P256

/-!
# The P-256 field prime `p` and group order `n` are prime

Pratt certificates (`Proof/Framework/Pratt.lean`), one theorem per prime of
the trees, for `p` and for `n`. Factors below `2^16` are prime by `norm_num`.
-/

namespace VG.Proof.P256

open VG.Proof.Pratt

theorem prime_65537 : Nat.Prime 65537 := by
  refine prime_of_cert 65537 3 17 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] (by decide) (by decide +kernel) ?_
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
  · norm_num

theorem prime_490463 : Nat.Prime 490463 := by
  refine prime_of_cert 490463 14 19 [2, 7, 53, 661] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
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

theorem prime_66417393611 : Nat.Prime 66417393611 := by
  refine prime_of_cert 66417393611 6 36 [2, 5, 53, 173, 197, 3677] (by decide) (by decide +kernel) ?_
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

theorem prime_11290956913871 : Nat.Prime 11290956913871 := by
  refine prime_of_cert 11290956913871 13 44 [2, 5, 17, 66417393611] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_66417393611

theorem prime_204061199 : Nat.Prime 204061199 := by
  refine prime_of_cert 204061199 11 28 [2, 11, 23, 107, 3769] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_34282281433 : Nat.Prime 34282281433 := by
  refine prime_of_cert 34282281433 17 35 [2, 2, 2, 3, 7, 204061199] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_204061199

theorem prime_704251 : Nat.Prime 704251 := by
  refine prime_of_cert 704251 2 20 [2, 3, 3, 5, 5, 5, 313] (by decide) (by decide +kernel) ?_
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

theorem prime_78283 : Nat.Prime 78283 := by
  refine prime_of_cert 78283 3 17 [2, 3, 3, 4349] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_46076956964474543 : Nat.Prime 46076956964474543 := by
  refine prime_of_cert 46076956964474543 5 56 [2, 23, 18169, 78283, 704251] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_78283
  · exact prime_704251

theorem prime_774023187263532362759620327192479577272145303 : Nat.Prime 774023187263532362759620327192479577272145303 := by
  refine prime_of_cert 774023187263532362759620327192479577272145303 3 150 [2, 3, 3, 2411, 34282281433, 11290956913871, 46076956964474543] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_34282281433
  · exact prime_11290956913871
  · exact prime_46076956964474543

theorem prime_835945042244614951780389953367877943453916927241 : Nat.Prime 835945042244614951780389953367877943453916927241 := by
  refine prime_of_cert 835945042244614951780389953367877943453916927241 11 160 [2, 2, 2, 3, 3, 3, 5, 774023187263532362759620327192479577272145303] (by decide) (by decide +kernel) ?_
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
  · exact prime_774023187263532362759620327192479577272145303

theorem prime_115792089210356248762697446949407573530086143415290314195533631308867097853951 : Nat.Prime 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  refine prime_of_cert 115792089210356248762697446949407573530086143415290314195533631308867097853951 6 256 [2, 3, 5, 5, 17, 257, 641, 1531, 65537, 490463, 6700417, 835945042244614951780389953367877943453916927241] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_65537
  · exact prime_490463
  · exact prime_6700417
  · exact prime_835945042244614951780389953367877943453916927241

theorem prime_126241 : Nat.Prime 126241 := by
  refine prime_of_cert 126241 7 17 [2, 2, 2, 2, 2, 3, 5, 263] (by decide) (by decide +kernel) ?_
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
  · norm_num

theorem prime_104471 : Nat.Prime 104471 := by
  refine prime_of_cert 104471 11 17 [2, 5, 31, 337] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_3969899 : Nat.Prime 3969899 := by
  refine prime_of_cert 3969899 2 22 [2, 19, 104471] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · norm_num
  · norm_num
  · exact prime_104471

theorem prime_1002328039319 : Nat.Prime 1002328039319 := by
  refine prime_of_cert 1002328039319 19 40 [2, 126241, 3969899] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · norm_num
  · exact prime_126241
  · exact prime_3969899

theorem prime_9350987 : Nat.Prime 9350987 := by
  refine prime_of_cert 9350987 2 24 [2, 17, 229, 1201] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem prime_187019741 : Nat.Prime 187019741 := by
  refine prime_of_cert 187019741 2 28 [2, 2, 5, 9350987] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_9350987

theorem prime_311245691 : Nat.Prime 311245691 := by
  refine prime_of_cert 311245691 2 29 [2, 5, 7, 17, 29, 29, 311] (by decide) (by decide +kernel) ?_
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

theorem prime_622491383 : Nat.Prime 622491383 := by
  refine prime_of_cert 622491383 5 30 [2, 311245691] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · norm_num
  · exact prime_311245691

theorem prime_155317 : Nat.Prime 155317 := by
  refine prime_of_cert 155317 5 18 [2, 2, 3, 7, 43, 43] (by decide) (by decide +kernel) ?_
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

theorem prime_191039911 : Nat.Prime 191039911 := by
  refine prime_of_cert 191039911 3 28 [2, 3, 5, 41, 155317] (by decide) (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_155317

theorem prime_208150935158385979 : Nat.Prime 208150935158385979 := by
  refine prime_of_cert 208150935158385979 2 58 [2, 3, 11, 43, 127, 3023, 191039911] (by decide) (by decide +kernel) ?_
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
  · exact prime_191039911

theorem prime_2624747550333869278416773953 : Nat.Prime 2624747550333869278416773953 := by
  refine prime_of_cert 2624747550333869278416773953 7 92 [2, 2, 2, 2, 2, 2, 3, 3, 1297, 16879, 208150935158385979] (by decide) (by decide +kernel) ?_
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
  · norm_num
  · exact prime_208150935158385979

theorem prime_115792089210356248762697446949407573529996955224135760342422259061068512044369 : Nat.Prime 115792089210356248762697446949407573529996955224135760342422259061068512044369 := by
  refine prime_of_cert 115792089210356248762697446949407573529996955224135760342422259061068512044369 7 256 [2, 2, 2, 2, 3, 71, 131, 373, 3407, 17449, 38189, 187019741, 622491383, 1002328039319, 2624747550333869278416773953] (by decide) (by decide +kernel) ?_
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
  · exact prime_187019741
  · exact prime_622491383
  · exact prime_1002328039319
  · exact prime_2624747550333869278416773953

theorem p_prime : Nat.Prime Spec.P256.p := by
  rw [show Spec.P256.p =
    115792089210356248762697446949407573530086143415290314195533631308867097853951 by decide]
  exact prime_115792089210356248762697446949407573530086143415290314195533631308867097853951

instance fact_p_prime : Fact (Nat.Prime Spec.P256.p) := ⟨p_prime⟩

theorem n_prime : Nat.Prime Spec.P256.n :=
  prime_115792089210356248762697446949407573529996955224135760342422259061068512044369

instance fact_n_prime : Fact (Nat.Prime Spec.P256.n) := ⟨n_prime⟩

end VG.Proof.P256
