import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Proof.Scrypt.Memory

/-!
# scrypt: facts about the specification of the whole function

Untrusted: everything here is checked by Lean. Target-independent facts
for the proofs of `vg_scrypt`: the parameters `valid` admits, the blocks of
step 1 in memory (`bytesAt_chunks`, `chunk_bytesAt`), the indices each
scryptROMix leaks, recovered from the list the contract declares
(`indices_eq`), and `scrypt` from its three steps (`scrypt_eq`).
-/

namespace VG.Proof.Scrypt.Whole

open VG.Spec.Scrypt
open VG.Proof.Scrypt.Memory (bytesAt_add bytesAt_length)

/-! ## The parameters -/

/-- A positive number with no bit in common with its predecessor is a power of
two. -/
theorem isPowerOfTwo_of_and : ∀ n : Nat, 0 < n → n &&& (n - 1) = 0 → n.isPowerOfTwo
  | n, hn, h => by
    induction n using Nat.strongRecOn with
    | _ n ih =>
      obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
      · -- `n = 2 m`: `2 m &&& (2 m - 1) = 2 (m &&& (m - 1))`.
        have hm : 0 < m := by omega
        have e : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
        have h' : m &&& (m - 1) = 0 := by
          apply Nat.eq_of_testBit_eq
          intro i
          have := congrArg (fun x => x.testBit (i + 1)) h
          rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_succ, Nat.testBit_succ,
            show 2 * m / 2 = m by omega, show (2 * m - 1) / 2 = m - 1 by omega] at this
          rw [Nat.testBit_and, Nat.zero_testBit, this]
        obtain ⟨k, hk⟩ := ih m (by omega) hm h'
        exact ⟨k + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
      · -- `n = 2 m + 1`: `n &&& (n - 1) = 2 m`, so `m = 0`.
        have h' : m = 0 := by
          apply Nat.eq_of_testBit_eq
          intro i
          have := congrArg (fun x => x.testBit (i + 1)) h
          simp only [Nat.add_sub_cancel] at this
          rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_succ, Nat.testBit_succ,
            show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega, Bool.and_self] at this
          rw [Nat.zero_testBit, this]
        exact ⟨0, by omega⟩

theorem valid_pow {N r p dk : Nat} (h : valid N r p dk) : N.isPowerOfTwo :=
  isPowerOfTwo_of_and N (by have := h.1; omega) h.2.1

theorem valid_r {N r p dk : Nat} (h : valid N r p dk) : 0 < r := by
  have h₁ := h.1
  have h₃ := h.2.2.1
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp at h₃; omega
  · exact hr

/-! ## Indices -/

theorem mixLoop_snd_length (r N : Nat) (v : List (List Byte)) :
    ∀ (n : Nat) (x : List Byte), (mixLoop r N v n x).2.length = n
  | 0, _ => rfl
  | n + 1, x => by
    rw [Proof.Scrypt.mixLoop_succ_snd, List.length_cons, mixLoop_snd_length r N v n]

theorem roMixIndices_length (r N : Nat) (b : List Byte) : (roMixIndices r N b).length = N := by
  rw [Proof.Scrypt.roMixIndices_eq, mixLoop_snd_length]

/-- The `i`th part of `N` elements of `l.flatMap f`, if each `f a` has `N`. -/
theorem flatMap_chunk {α β : Type} (f : α → List β) {N : Nat} (hf : ∀ a, (f a).length = N) :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), ((l.flatMap f).drop (N * i)).take N = f l[i]
  | a :: l, 0, _ => by
    rw [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.take_left' (hf a)]; rfl
  | a :: l, i + 1, hi => by
    rw [List.flatMap_cons, Nat.mul_succ, Nat.add_comm, ← List.drop_drop, List.drop_left' (hf a)]
    exact flatMap_chunk f hf l i (by simp at hi; omega)

/-- The indices each scryptROMix leaks, from the list of all of them. -/
theorem indices_eq {r N : Nat} {l₁ l₂ : List (List Byte)}
    (h : l₁.flatMap (roMixIndices r N) = l₂.flatMap (roMixIndices r N)) {i : Nat}
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    roMixIndices r N l₁[i] = roMixIndices r N l₂[i] := by
  rw [← flatMap_chunk _ (roMixIndices_length r N) l₁ i h₁, h,
    flatMap_chunk _ (roMixIndices_length r N) l₂ i h₂]

/-! ## The blocks in memory -/

/-- The `n k` bytes at `p` as `k` parts of `n`. -/
theorem bytesAt_chunks (m : Mem) (p : Addr) (n : Nat) :
    ∀ k, bytesAt m p (n * k) =
      (List.range k).flatMap fun i => bytesAt m (p + BitVec.ofNat 64 (n * i)) n
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, bytesAt_add, bytesAt_chunks m p n k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- Part `i` of `n` bytes of the bytes at `p`. -/
theorem chunk_bytesAt (m : Mem) (p : Addr) {n i k : Nat} (h : n * i + n ≤ k) :
    ((bytesAt m p k).drop (n * i)).take n = bytesAt m (p + BitVec.ofNat 64 (n * i)) n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = n * i + n + j := ⟨k - (n * i + n), by omega⟩
  rw [bytesAt_add, bytesAt_add, List.append_assoc, List.drop_left' (bytesAt_length _ _ _),
    List.take_left' (bytesAt_length _ _ _)]

/-- The blocks of step 1, if PBKDF2 wrote `B` to `p`. -/
theorem blocks_getElem {pw s : List Byte} {r p : Nat} {m : Mem} {b : Addr}
    (h : Spec.Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r) = some (bytesAt m b (p * 128 * r)))
    {i : Nat} (hi : i < (blocks pw s r p).length) :
    (blocks pw s r p)[i] = bytesAt m (b + BitVec.ofNat 64 (128 * r * i)) (128 * r) := by
  simp only [blocks, h, Option.getD_some, List.getElem_map, List.getElem_range]
  exact chunk_bytesAt m b (by
    simp only [blocks, List.length_map, List.length_range] at hi
    have : 128 * r * i + 128 * r ≤ 128 * r * p := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    rw [show p * 128 * r = 128 * r * p by rw [Nat.mul_comm, Nat.mul_comm p, Nat.mul_assoc, Nat.mul_left_comm]]
    exact this)

theorem blocks_length (pw s : List Byte) (r p : Nat) : (blocks pw s r p).length = p := by
  simp [blocks]

/-! ## The whole function -/

/-- `scrypt` from its three steps. -/
theorem scrypt_eq {pw s : List Byte} {N r p dk : Nat} {B out : List Byte} (hv : valid N r p dk)
    (h₁ : Spec.Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r) = some B)
    (h₂ : Spec.Pbkdf2.pbkdf2HmacSha256 pw
      ((List.range p).flatMap fun i => roMix r N ((B.drop (128 * r * i)).take (128 * r))) 1 dk = some out) :
    scrypt pw s N r p dk = some out := by
  simp only [scrypt, hv, ite_true, h₁]
  exact h₂

end VG.Proof.Scrypt.Whole
