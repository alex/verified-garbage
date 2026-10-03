import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# Short Weierstrass curves on x86-64: numbers as words, bits and bytes

The facts about the numbers of the working space (`wordsVal`, little-endian
words) that the code moving them needs: their bits, and the bytes of memory
they are made of; a number given word by word (`setConst`) or as the `or` of
its words (whether it is zero); their big-endian encodings (`Spec.Weierstrass.ofBytes`,
`Spec.Weierstrass.toBytes`) through byte-reversed words; and when memory that changed only in
one range keeps another range.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Proof.Mont.X86_64

/-! ## Bits -/

/-- Bit `64 j + b` of a number is bit `b` of its word `j`. -/
theorem testBit_wordsVal (m : Mem) (base : Addr) : ∀ (a n j b : Nat), j < n → b < 64 →
    (wordsVal m base a n).testBit (64 * j + b) = (word m base (a + 8 * j)).toNat.testBit b
  | _, 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a, n + 1, j, b, hj, hb => by
    rw [wordsVal, Nat.add_comm (word m base a).toNat,
      Nat.testBit_two_pow_mul_add _ (word m base a).isLt]
    rcases j with _ | j
    · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      exact ite_eq_left hb
    · rw [ite_eq_right (show ¬64 * (j + 1) + b < 64 by omega), show 64 * (j + 1) + b - 64 = 64 * j + b by omega,
        testBit_wordsVal m base (a + 8) n j b (by omega) hb, show a + 8 + 8 * j = a + 8 * (j + 1) by omega]

/-- Byte `8 j + r` of memory at `p` is byte `r` of the word at `p + 8 j`. -/
theorem byte_word (m : Mem) (p : Addr) (j : Nat) {r : Nat} (hr : r < 8) :
    m (p + BitVec.ofNat 64 (8 * j + r)) = (m.readW (p + BitVec.ofNat 64 (8 * j)) 64).extractLsb' (8 * r) 8 := by
  rw [show (m.readW (p + BitVec.ofNat 64 (8 * j)) 64) = m.read (p + BitVec.ofNat 64 (8 * j)) 8 from rfl,
    Mem.extractLsb'_read _ _ hr, Offset.add_add]

/-- Bit `b` of byte `i` of the working space at `a` is bit `8 i + b` of the
number there. -/
theorem testBit_byte (m : Mem) (base : Addr) {a n i b : Nat} (hi : i < 8 * n) (hb : b < 8) :
    (m (off base (a + i))).getLsbD b = (wordsVal m base a n).testBit (8 * i + b) := by
  have e := byte_word m (off base a) (i / 8) (r := i % 8) (Nat.mod_lt _ (by decide))
  rw [Offset.add_add, Offset.add_add, show a + (8 * (i / 8) + i % 8) = a + i by omega] at e
  rw [e, show 8 * i + b = 64 * (i / 8) + (8 * (i % 8) + b) by omega,
    testBit_wordsVal m base a n (i / 8) _ (by omega) (by omega), BitVec.getLsbD_extractLsb',
    decide_eq_true hb, Bool.true_and, BitVec.testBit_toNat]

/-! ## Numbers given word by word -/

/-- The words of `x`, word by word, are `x`. -/
theorem wordsVal_of_shifts (m : Mem) (base : Addr) : ∀ (o n x : Nat), x < 2 ^ (64 * n) →
    (∀ j < n, word m base (o + 8 * j) = BitVec.ofNat 64 (x >>> (64 * j))) → wordsVal m base o n = x
  | _, 0, x, hx, _ => by simp only [Nat.mul_zero, Nat.pow_zero] at hx; simp only [wordsVal]; omega
  | o, n + 1, x, hx, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftRight_zero] at h0
    have hr := wordsVal_of_shifts m base (o + 8) n (x >>> 64) (by
        rw [Nat.shiftRight_eq_div_pow]
        rw [pow64_succ] at hx
        exact Nat.div_lt_of_lt_mul hx) fun j hj => by
      rw [show o + 8 + 8 * j = o + 8 * (j + 1) by omega, h (j + 1) (by omega), ← Nat.shiftRight_add,
        show 64 + 64 * j = 64 * (j + 1) by omega]
    rw [wordsVal, hr, h0, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_add_div x _

/-- A number is zero iff its words are. -/
theorem wordsVal_eq_zero_iff (m : Mem) (base : Addr) : ∀ (a n : Nat),
    wordsVal m base a n = 0 ↔ ∀ j < n, word m base (a + 8 * j) = 0
  | _, 0 => ⟨fun _ _ hj => absurd hj (Nat.not_lt_zero _), fun _ => rfl⟩
  | a, n + 1 => by
    rw [wordsVal]
    constructor
    · intro h j hj
      rcases j with _ | j
      · rw [Nat.mul_zero, Nat.add_zero]; exact BitVec.eq_of_toNat_eq (by show _ = 0; omega)
      · rw [show a + 8 * (j + 1) = a + 8 + 8 * j by omega]
        exact (Nat.eq_zero_of_add_eq_zero_left h |> fun h' => by
          rcases Nat.mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' (by decide)
          · exact (wordsVal_eq_zero_iff m base (a + 8) n).mp h'' j (by omega))
    · intro h
      have h0 := h 0 (by omega)
      rw [Nat.mul_zero, Nat.add_zero] at h0
      rw [h0, (wordsVal_eq_zero_iff m base (a + 8) n).mpr fun j hj => by
        rw [show a + 8 + 8 * j = a + 8 * (j + 1) by omega]; exact h (j + 1) (by omega)]
      rfl

/-! ## Memory that changed elsewhere -/

/-- A byte of a range apart from the one at offsets `[o, o + len)` of `base`,
which alone changed. -/
theorem keep_of_disjoint {base p : Addr} {o len k : Nat} {m m' : Mem} (h : Outside base o len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨off base o, len⟩) (ho : o + len ≤ 2 ^ 64) {i : Nat} (hi : i < k)
    (hk : k ≤ 2 ^ 64) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := by
  refine h _ ?_
  by_cases h' : o ≤ ofs base (p + BitVec.ofNat 64 i) ∧ ofs base (p + BitVec.ofNat 64 i) < o + len
  · refine absurd ?_ (hd _ (Offset.contains_base p (d := i) (n := 1) (k := k) (by omega) (by omega)))
    show (p + BitVec.ofNat 64 i - (base + BitVec.ofNat 64 o)).toNat + 1 ≤ len
    have := (Offset.lt_iff (p + BitVec.ofNat 64 i) base ho).mpr h'
    omega
  · omega

/-- The same, for a range that alone changed at `q`. -/
theorem keep_of_disjoint' {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) {i : Nat} (hi : i < k)
    (hk : k ≤ 2 ^ 64) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  keep_of_disjoint (base := q) (o := 0) h (by rw [off, BitVec.add_zero]; exact hd) (by omega) hi hk

/-- A word of a range whose bytes are kept. -/
theorem readW_keep {m m' : Mem} {p : Addr} {d : Nat}
    (h : ∀ i < 8, m' (p + BitVec.ofNat 64 (d + i)) = m (p + BitVec.ofNat 64 (d + i))) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_congr fun i hi => by rw [Offset.add_add, h i hi]

/-! ## Big-endian encodings -/


open VG.Spec.Ecdsa (bytesAt)

theorem ofBytes_foldl (l : List Byte) (a : Nat) :
    l.foldl (fun acc b => 256 * acc + b.toNat) a = a * 256 ^ l.length + Spec.Weierstrass.ofBytes l := by
  induction l generalizing a with
  | nil => show a = a * 1 + 0; rw [Nat.mul_one, Nat.add_zero]
  | cons x xs ih =>
    have e : Spec.Weierstrass.ofBytes (x :: xs) = x.toNat * 256 ^ xs.length + Spec.Weierstrass.ofBytes xs :=
      (ih (256 * 0 + x.toNat)).trans (by rw [Nat.mul_zero, Nat.zero_add])
    rw [List.foldl_cons, ih, e, List.length_cons, Nat.pow_succ, Nat.add_mul, Nat.add_assoc,
      Nat.mul_comm (256 ^ xs.length) 256, ← Nat.mul_assoc, Nat.mul_comm a 256]

theorem ofBytes_append (l₁ l₂ : List Byte) :
    Spec.Weierstrass.ofBytes (l₁ ++ l₂) = Spec.Weierstrass.ofBytes l₁ * 256 ^ l₂.length + Spec.Weierstrass.ofBytes l₂ := by
  rw [Spec.Weierstrass.ofBytes, List.foldl_append, ofBytes_foldl]; rfl

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show m _ = m _
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem getElem_bytesAt (m : Mem) (p : Addr) {n k : Nat} (h : k < (bytesAt m p n).length) :
    (bytesAt m p n)[k] = m (p + BitVec.ofNat 64 k) := by
  simp only [bytesAt, List.getElem_map, List.getElem_range]

theorem getElem_toBytes (len x : Nat) {k : Nat} (h : k < (Spec.Weierstrass.toBytes len x).length) :
    (Spec.Weierstrass.toBytes len x)[k] = BitVec.ofNat 8 (x >>> (8 * (len - 1 - k))) := by
  simp only [Spec.Weierstrass.toBytes, List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]

theorem length_toBytes (len x : Nat) : (Spec.Weierstrass.toBytes len x).length = len := by
  simp only [Spec.Weierstrass.toBytes, List.length_map, List.length_reverse, List.length_range]

theorem shl8_or (x : Nat) (y : Byte) : x <<< 8 ||| y.toNat = x * 256 + y.toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- A byte-reversed word is the eight bytes big-endian. -/
theorem bswap64_ofBytes (m : Mem) (q : Addr) :
    (bswap64 (m.readW q 64)).toNat = Spec.Weierstrass.ofBytes (bytesAt m q 8) := by
  have e2 : q + 1 + 1 = q + BitVec.ofNat 64 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : q + BitVec.ofNat 64 2 + 1 = q + BitVec.ofNat 64 3 := by rw [BitVec.add_assoc]; rfl
  have e4 : q + BitVec.ofNat 64 3 + 1 = q + BitVec.ofNat 64 4 := by rw [BitVec.add_assoc]; rfl
  have e5 : q + BitVec.ofNat 64 4 + 1 = q + BitVec.ofNat 64 5 := by rw [BitVec.add_assoc]; rfl
  have e6 : q + BitVec.ofNat 64 5 + 1 = q + BitVec.ofNat 64 6 := by rw [BitVec.add_assoc]; rfl
  have e7 : q + BitVec.ofNat 64 6 + 1 = q + BitVec.ofNat 64 7 := by rw [BitVec.add_assoc]; rfl
  rw [bswap64_readW, e2, e3, e4, e5, e6, e7,
    show bytesAt m q 8 = [m (q + BitVec.ofNat 64 0), m (q + BitVec.ofNat 64 1), m (q + BitVec.ofNat 64 2),
      m (q + BitVec.ofNat 64 3), m (q + BitVec.ofNat 64 4), m (q + BitVec.ofNat 64 5),
      m (q + BitVec.ofNat 64 6), m (q + BitVec.ofNat 64 7)] from rfl,
    show q + BitVec.ofNat 64 0 = q from BitVec.add_zero q,
    show q + BitVec.ofNat 64 1 = q + 1 from rfl]
  simp only [BitVec.toNat_append, shl8_or, Spec.Weierstrass.ofBytes, List.foldl_cons, List.foldl_nil]
  omega

/-- The words `j` of a number, each the byte reversal of the word at
`p + 8 (k - 1 - j)`, are the `8 k` bytes at `p` big-endian. -/
theorem wordsVal_eq_ofBytes (m m' : Mem) (base p : Addr) : ∀ (o k : Nat),
    (∀ j < k, word m base (o + 8 * j) = bswap64 (m'.readW (p + BitVec.ofNat 64 (8 * (k - 1 - j))) 64)) →
    wordsVal m base o k = Spec.Weierstrass.ofBytes (bytesAt m' p (8 * k))
  | _, 0, _ => rfl
  | o, k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero] at h0
    rw [wordsVal, wordsVal_eq_ofBytes m m' base p (o + 8) k fun j hj => by
        rw [show o + 8 + 8 * j = o + 8 * (j + 1) by omega, h (j + 1) (by omega),
          show k + 1 - 1 - (j + 1) = k - 1 - j by omega],
      show 8 * (k + 1) = 8 * k + 8 by omega, bytesAt_add, ofBytes_append, length_bytesAt,
      ← bswap64_ofBytes, h0, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]
    omega

/-- The bit `i < 64` of a byte-reversed word. -/
theorem getLsbD_bswap64 (w : BitVec 64) {i : Nat} (hi : i < 64) :
    (bswap64 w).getLsbD i = w.getLsbD (8 * (7 - i / 8) + i % 8) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [bswap64, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- The `8 n` bytes at `q`, the word `j` of each is the byte reversal of the
masked word `j` of a number, are the number big-endian, or zeros. -/
theorem bytesAt_eq_toBytes (m m₀ : Mem) (base q : Addr) {a n : Nat} (c : Bool)
    (h : ∀ j < n, m.readW (q + BitVec.ofNat 64 (8 * (n - 1 - j))) 64 =
      bswap64 (word m₀ base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) :
    bytesAt m q (8 * n) =
      if c then Spec.Weierstrass.toBytes (8 * n) (wordsVal m₀ base a n) else List.replicate (8 * n) 0 := by
  have hb : ∀ k (hk : k < 8 * n), m (q + BitVec.ofNat 64 k) =
      (bswap64 (word m₀ base (a + 8 * (n - 1 - k / 8)) &&& (if c then BitVec.allOnes 64 else 0))).extractLsb'
        (8 * (k % 8)) 8 := fun k hk => by
    have e := byte_word m q (k / 8) (r := k % 8) (Nat.mod_lt _ (by decide))
    rw [show 8 * (k / 8) + k % 8 = k by omega,
      show 8 * (k / 8) = 8 * (n - 1 - (n - 1 - k / 8)) by omega, h _ (by omega)] at e
    exact e
  cases c
  · simp only [Bool.false_eq_true, ite_false] at hb ⊢
    refine List.ext_getElem (by rw [length_bytesAt, List.length_replicate]) fun k h₁ _ => ?_
    rw [length_bytesAt] at h₁
    rw [getElem_bytesAt, List.getElem_replicate, hb k h₁]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : 8 * (k % 8) + i < 64 := by omega
    have z : ∀ {w} j, (0 : BitVec w).getLsbD j = false := fun _ => BitVec.getLsbD_zero
    simp only [BitVec.getLsbD_extractLsb', getLsbD_bswap64 _ this, BitVec.getLsbD_and, z, Bool.and_false]
  · simp only [ite_true, BitVec.and_allOnes] at hb ⊢
    refine List.ext_getElem (by rw [length_bytesAt, length_toBytes]) fun k h₁ _ => ?_
    rw [length_bytesAt] at h₁
    rw [getElem_bytesAt, getElem_toBytes, hb k h₁]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and, Bool.true_and,
      getLsbD_bswap64 _ (by omega), Nat.testBit_shiftRight,
      show 8 * (8 * n - 1 - k) + i = 64 * (n - 1 - k / 8) + (8 * (7 - (8 * (k % 8) + i) / 8) + (8 * (k % 8) + i) % 8)
        by omega,
      testBit_wordsVal _ _ _ _ _ _ (by omega) (by omega), BitVec.testBit_toNat]

end VG.Proof.Weierstrass.X86_64
