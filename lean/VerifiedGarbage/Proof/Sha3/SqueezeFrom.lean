import VerifiedGarbage.Proof.Sha3.Stream

/-!
# The SHA-3 sponge: output squeezed from an offset

Untrusted: everything here is checked by Lean. `squeezeFrom` byte by byte,
and after permutations.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3

theorem length_squeezeFrom {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (pos d : Nat) :
    (squeezeFrom rate S pos d).length = d := by
  rw [squeezeFrom, List.length_take, List.length_drop, length_squeezeBlocks hr']
  have h1 := Nat.div_add_mod (pos + d + rate - 1) rate
  have h2 := Nat.mod_lt (pos + d + rate - 1) hr
  omega

/-- Byte `i` of the output from `pos` on is byte `(pos + i) mod r` of the
state after `⌊(pos + i) / r⌋` permutations. -/
theorem squeezeFrom_getElem {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State)
    {pos d i : Nat} (hi : i < d) :
    (squeezeFrom rate S pos d)[i]'(by rw [length_squeezeFrom hr hr']; exact hi) =
      byteOf (iterF ((pos + i) / rate) S) ((pos + i) % rate) := by
  simp only [squeezeFrom]
  rw [List.getElem_take, List.getElem_drop, getElem_squeezeBlocks hr hr']

theorem iterF_iterF (a k : Nat) (S : State) : iterF a (iterF k S) = iterF (a + k) S := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [iterF_succ, ih, Nat.succ_add, iterF_succ]

/-- The output from position `p` of the state after `k` permutations is the
output from position `rate * k + p` of the original state. -/
theorem squeezeFrom_iterF {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (k p d : Nat) :
    squeezeFrom rate (iterF k S) p d = squeezeFrom rate S (rate * k + p) d := by
  apply List.ext_getElem
  · rw [length_squeezeFrom hr hr', length_squeezeFrom hr hr']
  · intro i h1 _
    rw [length_squeezeFrom hr hr'] at h1
    rw [squeezeFrom_getElem hr hr' _ h1, squeezeFrom_getElem hr hr' _ h1, iterF_iterF,
      Nat.add_assoc, Nat.mul_add_div hr, Nat.mul_add_mod, Nat.add_comm k]

end VG.Proof.Sha3
