import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyArith

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Impl.Aes.X86.AesNi (rc)

/-- A broadcast supplies the same schedule temporary to every lane. -/
theorem broadcast_dword (x : BitVec 32) {j : Nat} (hj : j < 4) :
    dword (ofDwords x x x x) j = x := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact dword_ofDwords_0 _ _ _ _
  · exact dword_ofDwords_1 _ _ _ _
  · exact dword_ofDwords_2 _ _ _ _
  · exact dword_ofDwords_3 _ _ _ _

/-- Prefix XOR implements four consecutive recurrence words. -/
theorem kv_recurrence (f : Nat → BitVec 32) (B N : Nat) (a t : BitVec 128) (T : BitVec 32)
    (ha : ∀ j < 4, dword a j = f (B + j))
    (ht : ∀ j < 4, dword t j = T)
    (hr : ∀ j < 4, f (N + j) = f (B + j) ^^^ if j = 0 then T else f (N + j - 1)) :
    ∀ j < 4, dword (kv a t) j = f (N + j) := by
  have h0 : f N = f B ^^^ T := by simpa only [Nat.add_zero, ite_true] using hr 0 (by decide)
  have h1 : f (N + 1) = f (B + 1) ^^^ f N := by simpa using hr 1 (by decide)
  have h2 : f (N + 2) = f (B + 2) ^^^ f (N + 1) := by simpa using hr 2 (by decide)
  have h3 : f (N + 3) = f (B + 3) ^^^ f (N + 2) := by simpa using hr 3 (by decide)
  have a0 : dword a 0 = f B := by simpa only [Nat.add_zero] using ha 0 (by decide)
  obtain ⟨v0, v1, v2, v3⟩ := dword_kv a t
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [v0, a0, ht 0 (by decide)]
    simpa only [Nat.add_zero] using h0.symm
  · rw [v1, ha 1 (by decide), a0, ht 1 (by decide), Nat.add_zero, ← h0, ← h1]
  · rw [v2, ha 2 (by decide), ha 1 (by decide), a0, ht 2 (by decide),
      Nat.add_zero, ← h0, ← h1, ← h2]
  · rw [v3, ha 3 (by decide), ha 2 (by decide), ha 1 (by decide), a0,
      ht 3 (by decide), Nat.add_zero, ← h0, ← h1, ← h2, ← h3]

/-- AES-128 generates the next four schedule words. -/
theorem key128_next {m : Mem} {kp : Addr} (k : Nat) (a : BitVec 128)
    (ha : ∀ j < 4, dword a j = W m kp 4 (4 * k + j)) :
    ∀ j < 4,
      dword (kv a (shufDwords (aesKeygenAssist a (rc (k + 1))) 0xff)) j =
        W m kp 4 (4 * (k + 1) + j) := by
  apply kv_recurrence (W m kp 4) (4 * k) (4 * (k + 1)) a _
    ((sub32 (W m kp 4 (4 * k + 3))).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32) ha
  · intro j hj
    rw [shuf_ff, broadcast_dword _ hj, kga3, ha 3 (by decide)]
  · intro j hj
    rw [W_ge (by decide) (by omega)]
    rw [show 4 * (k + 1) + j - 4 = 4 * k + j by omega]
    by_cases h : j = 0
    · subst j
      simp only [temp32, show (4 * (k + 1)) % 4 = 0 by omega, ite_true,
        show (4 * (k + 1)) / 4 = k + 1 by omega,
        show 4 * (k + 1) - 1 = 4 * k + 3 by omega, Nat.add_zero]
    · have hmod : (4 * (k + 1) + j) % 4 = j := by omega
      simp only [temp32, hmod, h, ite_false, show ¬ (4 > 6 ∧ j = 4) by omega]

/-- AES-192 generates the next four schedule words. -/
theorem key192_first {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = W m kp 6 (6 * k + j))
    (hb : ∀ j < 2, dword b j = W m kp 6 (6 * k + 4 + j)) :
    ∀ j < 4,
      dword (kv a (shufDwords (aesKeygenAssist b (rc (k + 1))) 0x55)) j =
        W m kp 6 (6 * (k + 1) + j) := by
  apply kv_recurrence (W m kp 6) (6 * k) (6 * (k + 1)) a _
    ((sub32 (W m kp 6 (6 * k + 5))).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32) ha
  · intro j hj
    rw [shuf_55, broadcast_dword _ hj, kga1, hb 1 (by decide)]
  · intro j hj
    rw [W_ge (by decide) (by omega)]
    rw [show 6 * (k + 1) + j - 6 = 6 * k + j by omega]
    by_cases h : j = 0
    · subst j
      simp only [temp32, show (6 * (k + 1)) % 6 = 0 by omega, ite_true,
        show (6 * (k + 1)) / 6 = k + 1 by omega,
        show 6 * (k + 1) - 1 = 6 * k + 5 by omega, Nat.add_zero]
    · have hmod : (6 * (k + 1) + j) % 6 = j := by omega
      simp only [temp32, hmod, h, ite_false, show ¬ (6 > 6 ∧ j = 4) by omega]

/-- AES-256 generates the next four schedule words. -/
theorem key256_first {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = W m kp 8 (8 * k + j))
    (hb : ∀ j < 4, dword b j = W m kp 8 (8 * k + 4 + j)) :
    ∀ j < 4,
      dword (kv a (shufDwords (aesKeygenAssist b (rc (k + 1))) 0xff)) j =
        W m kp 8 (8 * (k + 1) + j) := by
  apply kv_recurrence (W m kp 8) (8 * k) (8 * (k + 1)) a _
    ((sub32 (W m kp 8 (8 * k + 7))).rotateRight 8 ^^^ (rc (k + 1)).setWidth 32) ha
  · intro j hj
    rw [shuf_ff, broadcast_dword _ hj, kga3, hb 3 (by decide)]
  · intro j hj
    rw [W_ge (by decide) (by omega)]
    rw [show 8 * (k + 1) + j - 8 = 8 * k + j by omega]
    by_cases h : j = 0
    · subst j
      simp only [temp32, show (8 * (k + 1)) % 8 = 0 by omega, ite_true,
        show (8 * (k + 1)) / 8 = k + 1 by omega,
        show 8 * (k + 1) - 1 = 8 * k + 7 by omega, Nat.add_zero]
    · have hmod : (8 * (k + 1) + j) % 8 = j := by omega
      simp only [temp32, hmod, h, ite_false, show ¬ (8 > 6 ∧ j = 4) by omega]

/-- AES-192's trailing pair continues the four newly generated words. -/
theorem key192_second {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = W m kp 6 (6 * (k + 1) + j))
    (hb : ∀ j < 2, dword b j = W m kp 6 (6 * k + 4 + j)) :
    ∀ j < 2, dword (kb b (shufDwords a 0xff)) j = W m kp 6 (6 * (k + 1) + 4 + j) := by
  obtain ⟨v0, v1⟩ := dword_kb b (shufDwords a 0xff)
  have t0 : dword (shufDwords a 0xff) 0 = W m kp 6 (6 * (k + 1) + 3) := by
    rw [shuf_ff, broadcast_dword _ (by decide), ha 3 (by decide)]
  have t1 : dword (shufDwords a 0xff) 1 = W m kp 6 (6 * (k + 1) + 3) := by
    rw [shuf_ff, broadcast_dword _ (by decide), ha 3 (by decide)]
  have h0 : W m kp 6 (6 * (k + 1) + 4) =
      W m kp 6 (6 * k + 4) ^^^ W m kp 6 (6 * (k + 1) + 3) := by
    rw [W_ge (by decide) (by omega)]
    rw [show 6 * (k + 1) + 4 - 6 = 6 * k + 4 by omega,
      show 6 * (k + 1) + 4 - 1 = 6 * (k + 1) + 3 by omega]
    simp only [temp32, show (6 * (k + 1) + 4) % 6 = 4 by omega]
    rfl
  have h1 : W m kp 6 (6 * (k + 1) + 4 + 1) =
      W m kp 6 (6 * k + 4 + 1) ^^^ W m kp 6 (6 * (k + 1) + 4) := by
    rw [W_ge (by decide) (by omega)]
    rw [show 6 * (k + 1) + 4 + 1 - 6 = 6 * k + 4 + 1 by omega,
      show 6 * (k + 1) + 4 + 1 - 1 = 6 * (k + 1) + 4 by omega]
    simp only [temp32, show (6 * (k + 1) + 4 + 1) % 6 = 5 by omega]
    rfl
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · rw [v0, hb 0 (by decide), t0]
    simpa only [Nat.add_zero] using h0.symm
  · rw [v1, hb 1 (by decide), hb 0 (by decide), t1]
    simp only [Nat.add_zero]
    rw [← h0, ← h1]

/-- AES-256's alternating half-group uses the unrotated substitution. -/
theorem key256_second {m : Mem} {kp : Addr} (k : Nat) (a b : BitVec 128)
    (ha : ∀ j < 4, dword a j = W m kp 8 (8 * (k + 1) + j))
    (hb : ∀ j < 4, dword b j = W m kp 8 (8 * k + 4 + j)) :
    ∀ j < 4, dword (kv b (shufDwords (aesKeygenAssist a 0) 0xaa)) j =
      W m kp 8 (8 * (k + 1) + 4 + j) := by
  apply kv_recurrence (W m kp 8) (8 * k + 4) (8 * (k + 1) + 4) b _
    (sub32 (W m kp 8 (8 * (k + 1) + 3))) hb
  · intro j hj
    rw [shuf_aa, broadcast_dword _ hj, kga2, ha 3 (by decide)]
  · intro j hj
    rw [W_ge (by decide) (by omega)]
    rw [show 8 * (k + 1) + 4 + j - 8 = 8 * k + 4 + j by omega]
    have hmod : (8 * (k + 1) + 4 + j) % 8 = 4 + j := by omega
    by_cases h : j = 0
    · subst j
      simp only [temp32, hmod, Nat.add_zero, show ¬ (4 = 0) by decide, ite_false,
        show 8 > 6 ∧ 4 = 4 by decide, and_self, ite_true,
        show 8 * (k + 1) + 4 - 1 = 8 * (k + 1) + 3 by omega]
    · simp only [temp32, hmod, show ¬ (4 + j = 0) by omega,
        show ¬ (8 > 6 ∧ 4 + j = 4) by omega, h, ite_false]

end VG.Proof.Aes.X86.AesNi
