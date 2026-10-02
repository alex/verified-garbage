import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The streaming state of ChaCha20

Untrusted: everything here is checked by Lean. What the implementations of
`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply` on every
target need of the streaming state (`keyAt`, `leftAt`, `restAt`), stated on
memory byte by byte, so that each target's proof only describes the bytes its
code writes:

* `restAt_getD`: the keystream left, byte by byte;
* `restAt_of_bytes`, `keyAt_of_bytes`: a state whose first 64 bytes are the
  constants, a key and a nonce, and with `64 × (2³² − c)` bytes left,
  represents the whole keystream of that key and nonce (`init`,
  `set_nonce`);
* `apply_data`, `apply_rest`: what `apply` does, in three steps: the bytes
  left in the buffered block (`h` of them), then whole blocks from the
  16-word state (`nb` of them), then the first `t` bytes of one more block,
  which becomes the buffered block.
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (Word stateAt keystream keystreamOf serialize block bytesAt keyAt leftAt
  restAt wordLE chacha20Block initState constants)

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_getD (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem length_restAt (m : Mem) (p : Addr) : (restAt m p).length = leftAt m p := by
  simp only [restAt, List.length_append, length_bytesAt, length_keystream]
  omega

/-- The keystream left, byte by byte: the last `n % 64` bytes of the
buffered block, then the blocks of the 16-word state. -/
theorem restAt_getD (m : Mem) (p : Addr) {k : Nat} (hk : k < leftAt m p) :
    (restAt m p).getD k 0 =
      if k < leftAt m p % 64 then m (p + BitVec.ofNat 64 (128 - leftAt m p % 64 + k))
      else (serialize (block (ctr (stateAt m p) ((k - leftAt m p % 64) / 64)))).getD
        ((k - leftAt m p % 64) % 64) 0 := by
  have hn := Nat.mod_lt (leftAt m p) (by decide : 64 > 0)
  simp only [restAt, List.getD_eq_getElem?_getD]
  split
  · rename_i h
    rw [List.getElem?_append_left (by rw [length_bytesAt]; exact h), ← List.getD_eq_getElem?_getD,
      bytesAt_getD _ _ h, Offset.add_add]
  · rename_i h
    rw [List.getElem?_append_right (by rw [length_bytesAt]; omega), length_bytesAt,
      ← List.getD_eq_getElem?_getD, keystream_getD _ (by omega), List.getD_eq_getElem?_getD]

/-! ## Words and bytes -/

/-- Two words with the same bytes are equal. -/
theorem word_ext {x y : Word} (h : ∀ i < 4, x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) :
    x = y := by
  ext j hj
  have := congrArg (·.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega, decide_true,
    Bool.true_and] at this
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  simpa [BitVec.getLsbD_eq_getElem hj] using this

/-- Byte `i` of a little-endian word of a byte string. -/
theorem wordLE_byte (bs : List Byte) (j : Nat) {i : Nat} (hi : i < 4) :
    (wordLE bs j).extractLsb' (8 * i) 8 = bs.getD (4 * j + i) 0 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordLE, Nat.add_zero]
    generalize bs.getD (4 * j + 3) 0 = a
    generalize bs.getD (4 * j + 2) 0 = b
    generalize bs.getD (4 * j + 1) 0 = c
    generalize bs.getD (4 * j) 0 = d
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    repeat' split
    all_goals first | (exfalso; omega) | (rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega)

/-- Word `j` of the 16-word state in memory, from its bytes. -/
theorem stateAt_getElem (m : Mem) (p : Addr) {j : Nat} (hj : j < 16) {bs : List Byte}
    (h : ∀ i < 4, m (p + BitVec.ofNat 64 (4 * j + i)) = bs.getD (4 * j + i) 0) :
    (stateAt m p)[j] = wordLE bs j := by
  simp only [stateAt, Vector.getElem_ofFn]
  refine word_ext fun i hi => ?_
  rw [wordLE_byte _ _ hi, ← h i hi, ← Offset.add_add, Mem.readW_byte m (p + BitVec.ofNat 64 (4 * j)) hi]

/-- A byte of the key, from the state's words 4–11. -/
theorem key_byte (m : Mem) (p : Addr) {i : Nat} (hi : i < 32) :
    m (p + 16 + BitVec.ofNat 64 i) =
      ((stateAt m p)[4 + i / 4]'(by omega)).extractLsb' (8 * (i % 4)) 8 := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show (p + 16 : Addr) = p + BitVec.ofNat 64 16 from rfl, Offset.add_add,
    show 16 + i = 4 * (4 + i / 4) + i % 4 by omega]

/-- The key is words 4–11 of the 16-word state. -/
theorem keyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i (hi : 4 ≤ i ∧ i < 12), (stateAt m' p)[i]'(by omega) = (stateAt m p)[i]'(by omega)) :
    keyAt m' p = keyAt m p := by
  simp only [keyAt, bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [key_byte m' p hi, key_byte m p hi, h _ ⟨by omega, by omega⟩]

/-- Advancing the counter keeps the key. -/
theorem keyAt_of_ctr {m m' : Mem} {p : Addr} {j : Nat} (h : stateAt m' p = ctr (stateAt m p) j) :
    keyAt m' p = keyAt m p :=
  keyAt_congr fun i hi => by
    rw [h]; simp only [ctr, Vector.getElem_set, show ¬ (12 = i) from by omega, ↓reduceIte]

/-- A state whose first 136 bytes are unchanged represents the same key and
keystream. -/
theorem stream_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 136, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    keyAt m' p = keyAt m p ∧ restAt m' p = restAt m p ∧ leftAt m' p = leftAt m p := by
  have hb : ∀ a n, a + n ≤ 136 → bytesAt m' (p + BitVec.ofNat 64 a) n = bytesAt m (p + BitVec.ofNat 64 a) n :=
    fun a n hn => List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      simpa only [Offset.add_add] using h (a + i) (by omega)
  have hw : ∀ a w, a + w / 8 ≤ 136 → m'.readW (p + BitVec.ofNat 64 a) w = m.readW (p + BitVec.ofNat 64 a) w :=
    fun a w hn => Mem.readW_congr fun i hi => by
      simpa only [Offset.add_add] using h (a + i) (by omega)
  have hl : leftAt m' p = leftAt m p := by
    simp only [leftAt]; rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, hw _ _ (by decide)]
  have hs : stateAt m' p = stateAt m p := by
    apply Vector.ext; intro i hi
    simp only [stateAt, Vector.getElem_ofFn]
    exact hw _ _ (by omega)
  refine ⟨by simp only [keyAt]; exact hb 16 32 (by decide), ?_, hl⟩
  simp only [restAt, hl, hs]
  rw [hb _ _ (by omega)]

/-! ## Starting a keystream -/

/-- The bytes of the constants `"expand 32-byte k"`, little-endian. -/
def sigma : List Byte :=
  [0x65, 0x78, 0x70, 0x61, 0x6e, 0x64, 0x20, 0x33, 0x32, 0x2d, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6b]

theorem getD_append_left {xs ys : List Byte} {n : Nat} (h : n < xs.length) (d : Byte) :
    (xs ++ ys).getD n d = xs.getD n d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {xs ys : List Byte} {n : Nat} (h : xs.length ≤ n) (d : Byte) :
    (xs ++ ys).getD n d = ys.getD (n - xs.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem wordLE_append_left {xs ys : List Byte} {i : Nat} (h : 4 * i + 4 ≤ xs.length) :
    wordLE (xs ++ ys) i = wordLE xs i := by
  simp only [wordLE, getD_append_left (show 4 * i + 3 < xs.length by omega),
    getD_append_left (show 4 * i + 2 < xs.length by omega),
    getD_append_left (show 4 * i + 1 < xs.length by omega),
    getD_append_left (show 4 * i < xs.length by omega)]

theorem wordLE_append_right {xs ys : List Byte} {a i : Nat} (hl : xs.length = 4 * a) (h : a ≤ i) :
    wordLE (xs ++ ys) i = wordLE ys (i - a) := by
  simp only [wordLE, getD_append_right (show xs.length ≤ 4 * i + 3 by omega),
    getD_append_right (show xs.length ≤ 4 * i + 2 by omega),
    getD_append_right (show xs.length ≤ 4 * i + 1 by omega),
    getD_append_right (show xs.length ≤ 4 * i by omega), hl,
    show 4 * i + 3 - 4 * a = 4 * (i - a) + 3 by omega, show 4 * i + 2 - 4 * a = 4 * (i - a) + 2 by omega,
    show 4 * i + 1 - 4 * a = 4 * (i - a) + 1 by omega, show 4 * i - 4 * a = 4 * (i - a) by omega]

theorem wordLE_drop (xs : List Byte) (i : Nat) : wordLE (xs.drop 4) i = wordLE xs (i + 1) := by
  simp only [wordLE, List.getD_eq_getElem?_getD, List.getElem?_drop,
    show 4 + (4 * i + 3) = 4 * (i + 1) + 3 by omega, show 4 + (4 * i + 2) = 4 * (i + 1) + 2 by omega,
    show 4 + (4 * i + 1) = 4 * (i + 1) + 1 by omega, show 4 + 4 * i = 4 * (i + 1) by omega]

theorem sigma_words : ∀ i < 4, wordLE sigma i = constants.getD i 0 := by decide

theorem length_sigma : sigma.length = 16 := rfl

/-- A state whose 16-word state is the constants, the key `key` and the
nonce `nonce`, byte by byte, and with `64 × (2³² − c)` bytes left (`c` the
initial block counter, the first word of the nonce), represents the whole
keystream of `key` and `nonce`. -/
theorem restAt_of_bytes {m : Mem} {p : Addr} {key nonce : List Byte} (hk : key.length = 32)
    (hb : ∀ i < 64, m (p + BitVec.ofNat 64 i) = (sigma ++ key ++ nonce).getD i 0)
    (hl : leftAt m p = 64 * (2 ^ 32 - (wordLE nonce 0).toNat)) :
    restAt m p = keystreamOf key nonce := by
  have hc := (wordLE nonce 0).isLt
  have hw : ∀ i (hi : i < 16), (stateAt m p)[i] = wordLE (sigma ++ key ++ nonce) i :=
    fun i hi => stateAt_getElem m p hi fun r hr => hb _ (by omega)
  have l48 : (sigma ++ key).length = 4 * 12 := by rw [List.length_append, length_sigma, hk]
  have l16 : sigma.length = 4 * 4 := length_sigma
  have hS : ∀ j : Nat, (stateAt m p).set 12 ((stateAt m p)[12] + BitVec.ofNat 32 j) =
      initState key (wordLE nonce 0 + BitVec.ofNat 32 j) (nonce.drop 4) := by
    intro j
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_set, initState, Vector.getElem_ofFn]
    by_cases e : i = 12
    · subst e
      simp only [↓reduceIte, show ¬ (12 < 4) by decide, show ¬ (12 < 12) by decide, hw 12 hi,
        wordLE_append_right l48 (Nat.le_refl 12)]
    · rw [hw i hi]
      by_cases h4 : i < 4
      · simp only [show ¬ (12 = i) by omega, h4, ↓reduceIte]
        rw [wordLE_append_left (xs := sigma ++ key) (by rw [l48]; omega),
          wordLE_append_left (by rw [length_sigma]; omega), sigma_words i h4]
      by_cases h12 : i < 12
      · simp only [show ¬ (12 = i) by omega, h4, h12, ↓reduceIte]
        rw [wordLE_append_left (xs := sigma ++ key) (by rw [l48]; omega),
          wordLE_append_right l16 (by omega)]
      · simp only [show ¬ (12 = i) by omega, h4, h12, e, ↓reduceIte]
        rw [wordLE_append_right l48 (by omega), wordLE_drop]
        congr 1; omega
  have h12 : (stateAt m p)[12] = wordLE nonce 0 := by
    rw [hw 12 (by decide), wordLE_append_right l48 (Nat.le_refl 12)]
  have hmod : leftAt m p % 64 = 0 := by rw [hl]; omega
  simp only [restAt, hmod, keystreamOf, keystream]
  have e0 : bytesAt m (p + BitVec.ofNat 64 (128 - 0)) 0 = [] := List.map_nil
  generalize hN : 2 ^ 32 - (wordLE nonce 0).toNat = N at hl
  have e1 : 64 * (leftAt m p / 64) = 64 * N := by rw [hl]; omega
  have e2 : (64 * N + 63) / 64 = N := by omega
  rw [e0, List.nil_append, e1, e2, List.take_of_length_le (by
    rw [length_flatMap_const _ (n := 64) (fun _ => length_serialize _), List.length_range])]
  simp only [hS, chacha20Block]

/-- The key of a state whose key bytes are `key`. -/
theorem keyAt_of_bytes {m : Mem} {p : Addr} {key : List Byte} (hk : key.length = 32)
    (hb : ∀ i < 32, m (p + BitVec.ofNat 64 (16 + i)) = key.getD i 0) : keyAt m p = key := by
  apply List.ext_getElem
  · simp [keyAt, length_bytesAt, hk]
  · intro i h₁ h₂
    simp only [keyAt, bytesAt, List.getElem_map, List.getElem_range]
    rw [show (p + 16 : Addr) = p + BitVec.ofNat 64 16 from rfl, Offset.add_add,
      hb i (by simpa [keyAt, length_bytesAt] using h₁), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h₂, Option.getD_some]

/-- `restAt_of_bytes` and `keyAt_of_bytes` from the three parts of the
16-word state: the constants, the key and the nonce. -/
theorem stream_of_parts {m : Mem} {p : Addr} {key nonce : List Byte} (hk : key.length = 32)
    (hσ : ∀ i < 16, m (p + BitVec.ofNat 64 i) = sigma.getD i 0)
    (hK : ∀ i < 32, m (p + BitVec.ofNat 64 (16 + i)) = key.getD i 0)
    (hN : ∀ i < 16, m (p + BitVec.ofNat 64 (48 + i)) = nonce.getD i 0)
    (hl : leftAt m p = 64 * (2 ^ 32 - (wordLE nonce 0).toNat)) :
    keyAt m p = key ∧ restAt m p = keystreamOf key nonce := by
  refine ⟨keyAt_of_bytes hk hK, restAt_of_bytes hk (fun i hi => ?_) hl⟩
  have l48 : (sigma ++ key).length = 48 := by rw [List.length_append, length_sigma, hk]
  by_cases h₁ : i < 48
  · rw [getD_append_left (by rw [l48]; exact h₁)]
    by_cases h₂ : i < 16
    · rw [getD_append_left (by rw [length_sigma]; exact h₂), hσ i h₂]
    · rw [getD_append_right (by rw [length_sigma]; omega), length_sigma, ← hK (i - 16) (by omega),
        show 16 + (i - 16) = i by omega]
  · rw [getD_append_right (by rw [l48]; omega), l48, ← hN (i - 48) (by omega),
      show 48 + (i - 48) = i by omega]

/-- Byte `j` of a little-endian 64-bit word. -/
theorem readW64_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- The bytes of memory from its 64-bit words. -/
theorem byte_of_words64 {m : Mem} {p : Addr} {W : Nat → BitVec 64} {a b : Nat}
    (h : ∀ k, a ≤ k → k < b → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = W k) {i : Nat}
    (h₁ : 8 * a ≤ i) (h₂ : i < 8 * b) :
    m (p + BitVec.ofNat 64 i) = (W (i / 8)).extractLsb' (8 * (i % 8)) 8 := by
  rw [← h (i / 8) (by omega) (by omega), readW64_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 8 * (i / 8) + i % 8 = i by omega]

/-- The bytes of memory from its 32-bit words. -/
theorem byte_of_words32 {m : Mem} {p : Addr} {W : Nat → BitVec 32} {a b : Nat}
    (h : ∀ k, a ≤ k → k < b → m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = W k) {i : Nat}
    (h₁ : 4 * a ≤ i) (h₂ : i < 4 * b) :
    m (p + BitVec.ofNat 64 i) = (W (i / 4)).extractLsb' (8 * (i % 4)) 8 := by
  rw [← h (i / 4) (by omega) (by omega), ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 4 * (i / 4) + i % 4 = i by omega]

/-- The first word of a nonce in memory. -/
theorem wordLE_bytesAt (m : Mem) (p : Addr) {n : Nat} (hn : 4 ≤ n) :
    wordLE (bytesAt m p n) 0 = m.readW p 32 :=
  word_ext fun i hi => by
    rw [wordLE_byte _ _ hi, Nat.mul_zero, Nat.zero_add, bytesAt_getD _ _ (by omega), Mem.readW_byte m p hi]

/-- The low half of a 64-bit word. -/
theorem readW64_setWidth (m : Mem) (a : Addr) : (m.readW a 64).setWidth 32 = m.readW a 32 := by
  refine word_ext fun i hi => ?_
  rw [← Mem.readW_byte m a hi, ← readW64_byte m a (by omega)]
  ext j hj
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  omega

/-- A 16-word state with the same bytes. -/
theorem stateAt_congr {m m' : Mem} {p q : Addr}
    (h : ∀ i < 64, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : stateAt m' q = stateAt m p := by
  apply Vector.ext; intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  refine word_ext fun i hi => ?_
  rw [← Mem.readW_byte m' _ hi, ← Mem.readW_byte m _ hi, Offset.add_add, Offset.add_add, h _ (by omega)]

theorem getElem_eq_getD' (l : List Byte) {i : Nat} (h : i < l.length) : l[i] = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- XORing a keystream into data in memory, byte by byte (the converse of
`bytesAt_xor`). -/
theorem xor_getD {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {j : Nat} (hj : j < n) :
    m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) ^^^ ks.getD j 0 := by
  have := congrArg (·.getD j 0) h
  rw [bytesAt_getD _ _ hj] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem
    (by rw [length_bytesAt]; exact hj), List.getElem?_eq_getElem (by rw [hks]; exact hj)]
  simp only [Option.getD_some]
  rw [getElem_eq_getD' _ (by rw [length_bytesAt]; exact hj), bytesAt_getD _ _ hj,
    getElem_eq_getD' _ (show j < ks.length by omega)]

/-- Reading a word after writing one elsewhere, at offsets from `p`. -/
theorem readW_writeW_ofNat (m : Mem) (p : Addr) {w w' : Nat} (v : BitVec w') {d e : Nat}
    (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d) (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64)
    (hw : w / 8 < 2 ^ 64) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) w = m.readW (p + BitVec.ofNat 64 d) w :=
  Mem.readW_writeW_sep (Offset.sep p h hd he) hw

/-- A byte outside a write, at offsets from `p`. -/
theorem byte_writeW_ofNat (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {i e : Nat}
    (h : i + 1 ≤ e ∨ e + w / 8 ≤ i) (hi : i + 1 ≤ 2 ^ 64) (he : e + w / 8 ≤ 2 ^ 64) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  Mem.write_apply (Offset.sep p h hi he _ (by simp))

/-! ## Applying the keystream -/

section Apply

variable (m : Mem) (p : Addr) (len : Nat)

/-- The bytes left in the buffered block. -/
abbrev bufLeft : Nat := leftAt m p % 64
/-- How many of them are used. -/
abbrev headLen : Nat := min (bufLeft m p) len
/-- How many whole blocks follow. -/
abbrev blocksOf : Nat := (len - headLen m p len) / 64
/-- How many bytes of one more block follow. -/
abbrev tailLen : Nat := (len - headLen m p len) % 64

end Apply

theorem ite_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem getD_take (l : List Byte) {n k : Nat} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem blk_congr {S : CState} {a b c d : Nat} (h₁ : a = b) (h₂ : c = d) :
    (serialize (block (ctr S a))).getD c 0 = (serialize (block (ctr S b))).getD d 0 := by
  subst h₁ h₂; rfl

theorem getElem_eq_getD (l : List Byte) {i : Nat} (h : i < l.length) : l[i] = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The data after `apply`, byte by byte: the bytes left in the buffered
block, then the blocks of the 16-word state (whole ones, and the first bytes
of the last), XORed into it. -/
theorem apply_data {m m' : Mem} {p d : Addr} {len : Nat} (hlen : len ≤ leftAt m p)
    (hD : ∀ k < len, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k) ^^^
      (if k < headLen m p len then m (p + BitVec.ofNat 64 (128 - bufLeft m p + k))
      else (serialize (block (ctr (stateAt m p) ((k - headLen m p len) / 64)))).getD
        ((k - headLen m p len) % 64) 0)) :
    bytesAt m' d len = List.zipWith (· ^^^ ·) (bytesAt m d len) ((restAt m p).take len) := by
  refine bytesAt_xor (by rw [List.length_take, length_restAt]; omega) fun k hk => ?_
  rw [hD k hk]
  refine congrArg (_ ^^^ ·) ?_
  have hh : headLen m p len = min (leftAt m p % 64) len := rfl
  have hb : bufLeft m p = leftAt m p % 64 := rfl
  rw [getD_take _ hk, restAt_getD _ _ (by omega)]
  by_cases h : k < headLen m p len
  · rw [ite_pos h, ite_pos (by omega)]
  · rw [ite_neg h, ite_neg (by omega), show headLen m p len = leftAt m p % 64 by omega]

/-- The keystream left after `apply`: the counter advanced past the blocks
used, and, if a block was started (`tailLen ≠ 0`), that block buffered;
`left` decreased by the length. -/
theorem apply_rest {m m' : Mem} {p : Addr} {len : Nat} (hlen : len ≤ leftAt m p)
    (hL : leftAt m' p = leftAt m p - len)
    (hS : stateAt m' p = ctr (stateAt m p) (blocksOf m p len + if tailLen m p len = 0 then 0 else 1))
    (hB : ∀ i < 64, m' (p + BitVec.ofNat 64 (64 + i)) = if tailLen m p len = 0 then m (p + BitVec.ofNat 64 (64 + i))
      else (serialize (block (ctr (stateAt m p) (blocksOf m p len)))).getD i 0) :
    restAt m' p = (restAt m p).drop len := by
  apply List.ext_getElem
  · rw [length_restAt, List.length_drop, length_restAt, hL]
  intro i h₁ _
  rw [length_restAt, hL] at h₁
  rw [List.getElem_drop, getElem_eq_getD, getElem_eq_getD,
    restAt_getD _ _ (by omega), restAt_getD _ _ (by omega), hL, hS, ctr_ctr]
  generalize hn : leftAt m p = n at *
  have hbl : bufLeft m p = n % 64 := by simp only [bufLeft, hn]
  have hh : headLen m p len = min (n % 64) len := by simp only [headLen, hbl]
  have hnb : blocksOf m p len = (len - min (n % 64) len) / 64 := by simp only [blocksOf, hh]
  have ht : tailLen m p len = (len - min (n % 64) len) % 64 := by simp only [tailLen, hh]
  rw [hnb, ht] at hB ⊢
  by_cases t0 : (len - min (n % 64) len) % 64 = 0
  · simp only [t0, ite_true, Nat.add_zero] at hB ⊢
    by_cases hlo : len ≤ n % 64
    · have e1 : (n - len) % 64 = n % 64 - len := by omega
      have e2 : (len - min (n % 64) len) / 64 = 0 := by omega
      rw [e1, e2]
      by_cases hi : i < n % 64 - len
      · rw [ite_pos hi, ite_pos (by omega)]
        have := hB (64 - (n % 64 - len) + i) (by omega)
        rw [show 64 + (64 - (n % 64 - len) + i) = 128 - (n % 64 - len) + i by omega] at this
        rw [this, show 128 - n % 64 + (len + i) = 128 - (n % 64 - len) + i by omega]
      · rw [ite_neg hi, ite_neg (by omega)]
        exact blk_congr (by omega) (by omega)
    · have e1 : (n - len) % 64 = 0 := by omega
      rw [e1, ite_neg (by omega), ite_neg (by omega)]
      exact blk_congr (by omega) (by omega)
  · simp only [t0, ite_false] at hB ⊢
    have e1 : (n - len) % 64 = 64 - (len - n % 64) % 64 := by omega
    rw [e1]
    by_cases hi : i < 64 - (len - n % 64) % 64
    · rw [ite_pos hi, ite_neg (by omega)]
      have := hB ((len - n % 64) % 64 + i) (by omega)
      rw [show 64 + ((len - n % 64) % 64 + i) = 128 - (64 - (len - n % 64) % 64) + i by omega]
        at this
      rw [this]
      exact blk_congr (by omega) (by omega)
    · rw [ite_neg hi, ite_neg (by omega)]
      exact blk_congr (by omega) (by omega)

end VG.Proof.ChaCha20
