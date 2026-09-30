import VerifiedGarbage.Proof.Ed25519.X86.Arith
import VerifiedGarbage.Impl.Ed25519.X86.MulAdd

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulTerms_value (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) = colv m x (prodTerms 256 288 k) +
      (if k < 8 then wv m x (320 + 4 * k) else 0) := by
  simp only [scalarMulTerms, colv, List.map_append, List.sum_append]
  split <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, tval]

theorem num_extend8 (f : Nat → Nat) : num (fun k => if k < 8 then f k else 0) 16 = num f 8 := by
  rw [num_16]
  have h0 : num (fun k => if 8 + k < 8 then f (8 + k) else 0) 8 = 0 := by
    have he : (fun k => if 8 + k < 8 then f (8 + k) else 0) = (fun _ => 0) := by
      funext k; rw [ite_eq_right (by omega_using [])]
    rw [he]; rfl
  rw [h0, Nat.mul_zero, Nat.add_zero]
  exact num_congr fun k hk => ite_eq_left hk

theorem scalarMulTerms_num (m : Mem) (x : BitVec 32) :
    num (fun k => colv m x (scalarMulTerms k)) 16 = fe m x 256 * fe m x 288 + fe m x 320 := by
  simp only [scalarMulTerms_value]
  rw [num_add, num_extend8]
  have hp : num (fun k => colv m x (prodTerms 256 288 k)) 16 = fe m x 256 * fe m x 288 := by
    simp only [colv, prodTerms, List.map_map]
    exact prod_identity (fun i => wv m x (256 + 4 * i)) (fun i => wv m x (288 + 4 * i))
  rw [hp]; rfl

theorem scalarMulTerms_bound (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) < 2 ^ 68 := by
  rw [scalarMulTerms_value]
  have hl : (prodTerms 256 288 k).length ≤ 8 := by
    simp only [prodTerms, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  have hp := colv_le_len (m := m) (x := x) (B := 2 ^ 64) (ts := prodTerms 256 288 k) fun t ht => by
    simp only [prodTerms, List.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact wv_mul_le _ _ _ _
  have hm := Nat.mul_le_mul_right (2 ^ 64) hl
  have hw := wv_lt m x (320 + 4 * k)
  split <;> omega_using [hp, hm, hw]

theorem scalarMulTerms_reads {k : Nat} (hk : k < 16) {t : Term} (ht : t ∈ scalarMulTerms k)
    {d : Nat} (hd : d ∈ treads t) : d + 4 ≤ 8192 ∧ 128 + 4 * k ≤ d := by
  simp only [scalarMulTerms, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at ht
    obtain ⟨i, ⟨hi, _, hki⟩, rfl⟩ := ht
    simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> constructor <;> omega_using [hk, hi, hki]
  · split at ht
    · simp only [List.mem_singleton] at ht; subst ht
      simp only [treads, List.mem_singleton] at hd; subst hd
      constructor <;> omega_using [hk]
    · simp only [List.not_mem_nil] at ht

theorem scalarWideMul_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarWideMul) s fun t => Keep s t ∧ Frame [sub x 128 64] s.mem t.mem ∧
      num (fun k => wv t.mem x (128 + 4 * k)) 16 = fe s.mem x 256 * fe s.mem x 288 + fe s.mem x 320 := by
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (cols_ok (ku.ctx hc) scalarMulTerms 16 (by decide)
    (fun k hk t ht d hd => let h := scalarMulTerms_reads hk ht hd; ⟨h.1, Or.inr h.2⟩)
    (fun k _ => scalarMulTerms_bound _ _ k) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  rw [au, Nat.zero_add, scalarMulTerms_num, mu] at et
  have hA := fe_lt s.mem x 256
  have hB := fe_lt s.mem x 288
  have hC := fe_lt s.mem x 320
  have hab := Nat.mul_le_mul (Nat.le_pred_of_lt hA) (Nat.le_pred_of_lt hB)
  change fe s.mem x 256 * fe s.mem x 288 ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) at hab
  have hz : acc t = 0 := by
    change _ + (2 ^ 256 * 2 ^ 256) * acc t = _ at et
    omega_using [et, hab, hC]
  rw [hz, Nat.mul_zero, Nat.add_zero] at et
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, et⟩
end VG.Proof.Ed25519.X86
