import VerifiedGarbage.Proof.Cmac.Spec

/-!
# Streaming AES-CMAC: lemmas about the state

What every target's `vg_cmac_aes_absorb` and `vg_cmac_aes_finish` need of the
streaming state (`Spec.Cmac.Repr`), whatever the ISA:

* `held n`, the number of bytes a state for a message of `n` bytes holds
  back: none for the empty message, else 1 to 16.
* `repr_fill`: absorbing `d` that fits in the block being held back
  (`d.length ≤ 16 - held n`) only appends `d` to the bytes held back.
* `repr_chain`: absorbing more chains the block held back, completed with
  the first `16 - held n` bytes of `d`, and then the whole blocks of the
  rest of `d` but its last 1 to 16 bytes, which it holds back.
* `repr_finish`: the chaining value and the bytes held back are what
  `vg_cmac_aes_finalize` takes, and its result is the MAC.
-/

namespace VG.Proof.Cmac.Stream

open VG Spec.Cmac

/-! ## Lengths -/

/-- The number of bytes held back for a message of `n` bytes. -/
def held (n : Nat) : Nat := n - chainedLen 16 n

theorem held_zero : held 0 = 0 := rfl

theorem held_pos {n : Nat} (h : 0 < n) : held n = (n - 1) % 16 + 1 := by
  unfold held chainedLen; omega

theorem held_le (n : Nat) : held n ≤ 16 := by unfold held chainedLen; omega

theorem chainedLen_add_held (n : Nat) : chainedLen 16 n + held n = n := by
  unfold held chainedLen; omega

theorem chainedLen_mod (n : Nat) : chainedLen 16 n % 16 = 0 := by unfold chainedLen; omega

theorem chainedLen_fill {n l : Nat} (h : l ≤ 16 - held n) : chainedLen 16 (n + l) = chainedLen 16 n := by
  unfold held chainedLen at *; omega

theorem held_fill {n l : Nat} (h : l ≤ 16 - held n) : held (n + l) = held n + l := by
  unfold held chainedLen at *; omega

/-- The number of whole blocks of `d` chained after the block held back is
completed with the first `16 - held n` bytes of `d`. -/
def nblocks (n l : Nat) : Nat := (l - (16 - held n) - 1) / 16

theorem chainedLen_chain {n l : Nat} (h : 16 - held n < l) :
    chainedLen 16 (n + l) = chainedLen 16 n + 16 + 16 * nblocks n l := by
  unfold nblocks held chainedLen at *; omega

theorem held_chain {n l : Nat} (h : 16 - held n < l) :
    held (n + l) = l - (16 - held n) - 16 * nblocks n l := by
  unfold nblocks held chainedLen at *; omega

theorem held_chain_pos {n l : Nat} (h : 16 - held n < l) :
    0 < l - (16 - held n) - 16 * nblocks n l ∧ l - (16 - held n) - 16 * nblocks n l ≤ 16 := by
  unfold nblocks; omega

/-! ## Blocks -/

theorem blocks_append {xs ys : List Byte} (hx : xs.length % 16 = 0) :
    blocks 16 (xs ++ ys) = blocks 16 xs ++ blocks 16 ys := by
  obtain ⟨q, hq⟩ : ∃ q, xs.length = 16 * q := ⟨xs.length / 16, by omega⟩
  simp only [blocks, List.length_append, hq,
    show (16 * q + ys.length) / 16 = q + ys.length / 16 by omega,
    Nat.mul_div_cancel_left _ (by decide : 0 < 16), List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.mul_add, List.drop_append, hq]
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem blocks_single {x : List Byte} (hx : x.length = 16) : blocks 16 x = [x] := by
  simp [blocks, hx, List.take_of_length_le]

theorem blocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    blocksAt m p 16 n = blocks 16 (Spec.Aes.bytesAt m p (16 * n)) := by
  simp only [blocksAt, blocks, bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro k h₁ h₂
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Aes.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

/-- The bytes at `p + a` are those at `p` from the `a`-th on. -/
theorem bytesAt_offset (m : Mem) (p : Addr) {a b n : Nat} (h : a + b ≤ n) :
    Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b = ((Spec.Aes.bytesAt m p n).drop a).take b := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro k h₁ h₂
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h₁
  simp [Spec.Aes.bytesAt, BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Aes.bytesAt m p (a + b) =
      Spec.Aes.bytesAt m p a ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Aes.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-! ## The state -/

/-- The key schedule and the subkeys at `p` are those of `key`, as `Repr`
requires. -/
def KeyAt (mem : Mem) (p : Addr) (key : List Byte) : Prop :=
  let ks := subkeys (aes key) 16
  (key.length = 16 ∨ key.length = 24 ∨ key.length = 32) ∧
    Spec.Aes.bytesAt mem p (16 * (Spec.Aes.rounds (key.length / 4) + 1)) = Spec.Aes.expandKey key ∧
    Spec.Aes.bytesAt mem (p + 240) 32 = ks.1 ++ ks.2

theorem rounds_le {key : List Byte} (h : key.length = 16 ∨ key.length = 24 ∨ key.length = 32) :
    16 * (Spec.Aes.rounds (key.length / 4) + 1) ≤ 240 := by
  simp only [Spec.Aes.rounds]; omega

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `KeyAt` depends only on the first 272 bytes. -/
theorem KeyAt.congr {m m' : Mem} {p : Addr} {key : List Byte} (hk : KeyAt m p key)
    (h : ∀ i < 272, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : KeyAt m' p key := by
  obtain ⟨hl, hs, hsk⟩ := hk
  have hR := rounds_le hl
  refine ⟨hl, ?_, ?_⟩
  · rw [bytesAt_congr fun i hi => h i (by omega), hs]
  · rw [show p + 240 = p + BitVec.ofNat 64 240 from rfl,
      bytesAt_congr (m := m) fun i hi => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact hsk

theorem repr_iff (mem : Mem) (p : Addr) (key msg : List Byte) :
    Spec.Cmac.Repr mem p key msg ↔ KeyAt mem p key ∧
      Spec.Aes.bytesAt mem (p + 272) 16 =
        chain (aes key) (zeros 16) (blocks 16 (msg.take (chainedLen 16 msg.length))) ∧
      Spec.Aes.bytesAt mem (p + 288) (held msg.length) = msg.drop (chainedLen 16 msg.length) := by
  simp only [Spec.Cmac.Repr, KeyAt, held, and_assoc]

theorem length_take_chained (msg : List Byte) :
    (msg.take (chainedLen 16 msg.length)).length = chainedLen 16 msg.length := by
  have := chainedLen_add_held msg.length
  simp only [List.length_take]; omega

/-- Absorbing `d` that fits in the block held back. -/
theorem repr_fill {m m' : Mem} {p : Addr} {key msg d : List Byte} (hr : Spec.Cmac.Repr m p key msg)
    (hk : ∀ i < 272, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hl : d.length ≤ 16 - held msg.length)
    (hc : Spec.Aes.bytesAt m' (p + 272) 16 = Spec.Aes.bytesAt m (p + 272) 16)
    (hh : Spec.Aes.bytesAt m' (p + 288) (held msg.length + d.length) =
      Spec.Aes.bytesAt m (p + 288) (held msg.length) ++ d) :
    Spec.Cmac.Repr m' p key (msg ++ d) := by
  rw [repr_iff] at hr ⊢
  obtain ⟨hk', hc', hh'⟩ := hr
  have hn := chainedLen_add_held msg.length
  rw [List.length_append, chainedLen_fill hl, held_fill hl]
  refine ⟨hk'.congr hk, ?_, ?_⟩
  · rw [hc, hc', List.take_append_of_le_length (by omega)]
  · rw [hh, hh', List.drop_append_of_le_length (by omega)]

/-- Absorbing `d` that does not fit in the block held back. -/
theorem repr_chain {m m' : Mem} {p : Addr} {key msg d : List Byte} (hr : Spec.Cmac.Repr m p key msg)
    (hk : ∀ i < 272, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hl : 16 - held msg.length < d.length)
    (hc : Spec.Aes.bytesAt m' (p + 272) 16 =
      Spec.Cmac.chain (aes key) (Spec.Aes.bytesAt m (p + 272) 16)
        ([Spec.Aes.bytesAt m (p + 288) (held msg.length) ++ d.take (16 - held msg.length)] ++
          blocks 16 ((d.drop (16 - held msg.length)).take (16 * nblocks msg.length d.length))))
    (hh : Spec.Aes.bytesAt m' (p + 288) (d.length - (16 - held msg.length) - 16 * nblocks msg.length d.length) =
      (d.drop (16 - held msg.length)).drop (16 * nblocks msg.length d.length)) :
    Spec.Cmac.Repr m' p key (msg ++ d) := by
  rw [repr_iff] at hr ⊢
  obtain ⟨hk', hc', hh'⟩ := hr
  have hn := chainedLen_add_held msg.length
  have hm := chainedLen_mod msg.length
  have hp := held_chain_pos hl
  have hle := held_le msg.length
  rw [List.length_append, chainedLen_chain hl, held_chain hl]
  generalize hcd : chainedLen 16 msg.length = c at *
  generalize hhd : held msg.length = h at *
  generalize hnb : nblocks msg.length d.length = nb at *
  have hdc : (msg.drop c).length = h := by simp; omega
  refine ⟨hk'.congr hk, ?_, ?_⟩
  · have e : (msg ++ d).take (c + 16 + 16 * nb) =
        msg.take c ++ ((msg.drop c ++ d.take (16 - h)) ++ (d.drop (16 - h)).take (16 * nb)) := by
      rw [List.take_append, List.take_of_length_le (by omega),
        show c + 16 + 16 * nb - msg.length = (16 - h) + 16 * nb by omega, List.take_add]
      simp only [List.append_assoc]
      rw [← List.append_assoc (List.take c msg), List.take_append_drop]
    have hx : (msg.drop c ++ d.take (16 - h)).length = 16 := by simp; omega
    rw [hc, hc', hh', e, blocks_append (by rw [List.length_take]; omega),
      blocks_append (by rw [hx]), blocks_single hx, chain_append, chain_append, chain_append]
  · have e : (msg ++ d).drop (c + 16 + 16 * nb) = (d.drop (16 - h)).drop (16 * nb) := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
      congr 1; omega
    rw [hh, e]

/-- The MAC is `macFull`'s, which has 16 bytes. -/
theorem aesCmac_eq (key msg : List Byte) : aesCmac key 16 msg = macFull (aes key) 16 msg := by
  simp only [aesCmac, mac]
  apply List.take_of_length_le
  simp only [macFull, chain_append, chain_single, aes, aesWith_length, Nat.le_refl]

/-- What `vg_cmac_aes_finalize` takes of a state that represents `msg`. -/
theorem repr_finish {m : Mem} {p : Addr} {key msg : List Byte} (hr : Spec.Cmac.Repr m p key msg) :
    let c := chainedLen 16 msg.length
    (msg.take c).length % 16 = 0 ∧ (msg.take c = [] ∨ 0 < held msg.length) ∧
      Spec.Aes.bytesAt m (p + 272) 16 = Spec.Cmac.chain (aes key) (zeros 16) (blocks 16 (msg.take c)) ∧
      msg.take c ++ Spec.Aes.bytesAt m (p + 288) (held msg.length) = msg := by
  rw [repr_iff] at hr
  obtain ⟨_, hc, hh⟩ := hr
  have hn := chainedLen_add_held msg.length
  refine ⟨by rw [length_take_chained]; exact chainedLen_mod _, ?_, hc, by rw [hh, List.take_append_drop]⟩
  by_cases h0 : msg.length = 0
  · exact .inl (by simp [List.eq_nil_of_length_eq_zero h0])
  · exact .inr (by rw [held_pos (by omega)]; omega)

end VG.Proof.Cmac.Stream
