import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Spec.ChaCha20Poly1305

/-!
# Facts about the ChaCha20-Poly1305 specification

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20Poly1305

open VG.Proof.ChaCha20 (ctr CState keystream_getD length_keystream length_serialize)
open VG.Spec.ChaCha20 (Word initState keystream serialize block chacha20Block wordLE)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

/-- A 32-bit little-endian read, byte by byte. -/
theorem readW32 (m : Mem) (a : Addr) :
    m.readW a 32 = (m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 : a + 1 + 1 = a + 2 := by bv_omega
  have e3 : a + 2 + 1 = a + 3 := by bv_omega
  simp only [Mem.readW, Mem.read, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, e1, e3]
  have : i - 8 - 8 - 8 < 8 := by omega
  simp [this, hi]

/-- Word `j` of the bytes in memory is the 32-bit word there. -/
theorem wordLE_bytesAt (m : Mem) (p : Addr) {n j : Nat} (h : 4 * j + 4 ≤ n) :
    wordLE (Spec.ChaCha20.bytesAt m p n) j = m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  have g : ∀ k < n, (Spec.ChaCha20.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
    intro k hk; simp [Spec.ChaCha20.bytesAt, hk]
  rw [wordLE, g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), readW32]
  have e : ∀ k, p + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (4 * j + k) := by
    intro k; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show (3 : Addr) = BitVec.ofNat 64 3 from rfl, show (2 : Addr) = BitVec.ofNat 64 2 from rfl,
    show (1 : Addr) = BitVec.ofNat 64 1 from rfl, e, e, e, BitVec.append_assoc, BitVec.append_assoc]

/-- Advancing the counter of an initial state. -/
theorem ctr_initState (key nonce : List Byte) (c : Word) (j : Nat) :
    ctr (initState key c nonce) j = initState key (c + BitVec.ofNat 32 j) nonce := by
  apply Vector.ext
  intro i hi
  simp only [ctr, Vector.getElem_set, initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem zipWith_take {α : Type} (f : α → α → α) (l l' : List α) :
    List.zipWith f l (l'.take l.length) = List.zipWith f l l' := by
  apply List.ext_getElem
  · simp
  · intro k h₁ h₂; simp

/-- ChaCha20 encryption is XORing the keystream of the initial state. -/
theorem encrypt_eq (key nonce : List Byte) (c : Word) (m : List Byte) :
    Spec.ChaCha20.encrypt key c nonce m =
      List.zipWith (· ^^^ ·) m (keystream (initState key c nonce) m.length) := by
  have e : ∀ j, serialize (block ((initState key c nonce).set 12 ((initState key c nonce)[12] +
      BitVec.ofNat 32 j))) = chacha20Block key (c + BitVec.ofNat 32 j) nonce := by
    intro j
    rw [show (initState key c nonce).set 12 ((initState key c nonce)[12] + BitVec.ofNat 32 j) =
      ctr (initState key c nonce) j from rfl, ctr_initState]
    rfl
  simp only [keystream, e, zipWith_take]
  rfl

end VG.Proof.ChaCha20Poly1305
