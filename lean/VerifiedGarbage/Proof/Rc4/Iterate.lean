import VerifiedGarbage.Proof.Rc4.Stream

/-!
# The stream, byte by byte

`stepN c n` is the context after `n` steps from `c`, and `ks c n` the `n`-th
keystream byte. `update` XORs the input with these bytes and ends in
`stepN` of its length (`update_bytes`).
-/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- The context after `n` steps. -/
def stepN (c : Context) : Nat → Context
  | 0 => c
  | n + 1 => (step (stepN c n)).1

/-- Keystream byte `n`. -/
def ks (c : Context) (n : Nat) : Byte := (step (stepN c n)).2

theorem stepN_succ' (c : Context) (n : Nat) : stepN c (n + 1) = stepN (step c).1 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stepN] at ih ⊢; rw [ih]

theorem ks_succ (c : Context) (n : Nat) : ks c (n + 1) = ks (step c).1 n := by
  simp only [ks, stepN_succ']

theorem update_fst (c : Context) (bs : List Byte) : (update c bs).1 = stepN c bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp only [update, List.length_cons, stepN_succ', ih]

/-- Bytes that are the input XORed with the keystream are `update`'s output. -/
theorem update_bytes (c : Context) (m m' : Mem) (d : Addr) (n : Nat)
    (h : ∀ k < n, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k) ^^^ ks c k) :
    bytesAt m' d n = (update c (bytesAt m d n)).2 := by
  induction n generalizing c d with
  | zero => rfl
  | succ n ih =>
    rw [bytes_cons, bytes_cons]
    simp only [update]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih (step c).1 (d + 1#64) fun k hk => by
      have := h (k + 1) (by omega)
      rw [ks_succ] at this
      rw [show d + 1#64 + BitVec.ofNat 64 k = d + BitVec.ofNat 64 (k + 1) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
      exact this]
    rfl

end VG.Proof.Rc4
