import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.Ladder
import Mathlib.Tactic.SplitIfs

/-!
# X25519: byte strings, numbers and words

The encodings of RFC 7748 §5 as little-endian numbers of byte strings
(`leNum`) and byte strings of numbers (`leBytes`), and in memory as 64-bit or
32-bit words: the decoded u-coordinate is the number of its bytes modulo
`2²⁵⁵`, each bit of the decoded scalar a bit of one of its bytes (or fixed by
the clamping), and the encoded result the bytes of its value.
-/

namespace VG.Proof.X25519

open VG.Spec.X25519

/-- The little-endian number of a byte string. -/
def leNum : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNum bs

/-- The `n` least significant bytes of `x`, in little-endian order. -/
def leBytes (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

theorem leNum_append (a b : List Byte) : leNum (a ++ b) = leNum a + 256 ^ a.length * leNum b := by
  induction a with
  | nil => simp [leNum]
  | cons x xs ih =>
    simp only [List.cons_append, leNum, ih, List.length_cons, Nat.pow_succ, Nat.mul_add,
      Nat.add_assoc, Nat.mul_comm _ 256, Nat.mul_assoc]

theorem leNum_lt (a : List Byte) : leNum a < 256 ^ a.length := by
  induction a with
  | nil => simp [leNum]
  | cons x xs ih =>
    simp only [leNum, List.length_cons, Nat.pow_succ]
    have := x.isLt
    omega

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    show m _ = m _
    congr 1
    rw [BitVec.add_assoc, Nat.succ_eq_add_one, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 i)]
    rfl

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show m _ = m _
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem leNum_bytesAt_read (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p n) = (m.read p n).toNat := by
  induction n generalizing p with
  | zero => simp [bytesAt, leNum, Mem.read]
  | succ n ih =>
    rw [bytesAt_succ, leNum, ih, Mem.read, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

theorem leNum_bytesAt_64 (m : Mem) (p : Addr) : leNum (bytesAt m p 8) = (m.readW p 64).toNat := by
  rw [leNum_bytesAt_read]
  simp [Mem.readW]

theorem leNum_bytesAt_32bit (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [leNum_bytesAt_read]
  simp [Mem.readW]

/-- A number stored as four little-endian 64-bit words. -/
theorem leNum_bytesAt_words64 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 32) = (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat +
      2 ^ 128 * (m.readW (p + 16) 64).toNat + 2 ^ 192 * (m.readW (p + 24) 64).toNat := by
  rw [show 32 = 8 + (8 + (8 + 8)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add, leNum_append,
    leNum_append, leNum_append, length_bytesAt, length_bytesAt, length_bytesAt, leNum_bytesAt_64,
    leNum_bytesAt_64, leNum_bytesAt_64, leNum_bytesAt_64, BitVec.add_assoc, BitVec.add_assoc,
    BitVec.add_assoc]
  show (m.readW p 64).toNat + 256 ^ 8 * ((m.readW (p + 8) 64).toNat +
    256 ^ 8 * ((m.readW (p + 16) 64).toNat + 256 ^ 8 * (m.readW (p + 24) 64).toNat)) = _
  omega

/-- A number stored as eight little-endian 32-bit words. -/
theorem leNum_bytesAt_words32 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 32) = (m.readW p 32).toNat + 2 ^ 32 * (m.readW (p + 4) 32).toNat +
      2 ^ 64 * (m.readW (p + 8) 32).toNat + 2 ^ 96 * (m.readW (p + 12) 32).toNat +
      2 ^ 128 * (m.readW (p + 16) 32).toNat + 2 ^ 160 * (m.readW (p + 20) 32).toNat +
      2 ^ 192 * (m.readW (p + 24) 32).toNat + 2 ^ 224 * (m.readW (p + 28) 32).toNat := by
  rw [show bytesAt m p 32 = bytesAt m p (4 + (4 + (4 + (4 + (4 + (4 + (4 + 4))))))) from rfl]
  simp only [bytesAt_add, leNum_append, length_bytesAt, leNum_bytesAt_32bit, BitVec.add_assoc]
  show (m.readW p 32).toNat + 256 ^ 4 * ((m.readW (p + 4) 32).toNat +
    256 ^ 4 * ((m.readW (p + 8) 32).toNat + 256 ^ 4 * ((m.readW (p + 12) 32).toNat +
    256 ^ 4 * ((m.readW (p + 16) 32).toNat + 256 ^ 4 * ((m.readW (p + 20) 32).toNat +
    256 ^ 4 * ((m.readW (p + 24) 32).toNat + 256 ^ 4 * (m.readW (p + 28) 32).toNat)))))) = _
  omega

/-! ## Numbers as bytes -/

theorem leBytes_add (a b x : Nat) :
    leBytes (a + b) x = leBytes a x ++ leBytes b (x / 256 ^ a) := by
  simp only [leBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem leBytes_mod (n x : Nat) : leBytes n (x % 256 ^ n) = leBytes n x := by
  simp only [leBytes]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 256 ^ n = 256 ^ i * 256 ^ (n - i) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  rw [show (2 : Nat) ^ 8 = 256 from rfl]
  exact ⟨256 ^ (n - i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩

theorem leBytes_succ (n x : Nat) : leBytes (n + 1) x = BitVec.ofNat 8 x :: leBytes n (x / 256) := by
  rw [Nat.add_comm, leBytes_add, Nat.pow_one]; simp [leBytes]

theorem bytesAt_leBytes (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n = leBytes n (m.read p n).toNat := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have e : (m.read p (n + 1)).toNat = (m.read (p + 1) n).toNat * 256 + (m p).toNat := by
      rw [Mem.read, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
        Nat.shiftLeft_eq]
    rw [bytesAt_succ, leBytes_succ, ih, e]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have := (m p).isLt
      omega
    · congr 1
      have := (m p).isLt
      omega

theorem bytesAt_leBytes_64 (m : Mem) (p : Addr) :
    bytesAt m p 8 = leBytes 8 (m.readW p 64).toNat := by
  rw [bytesAt_leBytes]; simp [Mem.readW]

/-- Four little-endian 64-bit words in memory are the 32 bytes of `x`, if they
are its four 64-bit digits. -/
theorem bytesAt_leBytes_words64 (m : Mem) (p : Addr) (x : Nat)
    (h₀ : (m.readW p 64).toNat = x % 2 ^ 64)
    (h₁ : (m.readW (p + 8) 64).toNat = x / 2 ^ 64 % 2 ^ 64)
    (h₂ : (m.readW (p + 16) 64).toNat = x / 2 ^ 128 % 2 ^ 64)
    (h₃ : (m.readW (p + 24) 64).toNat = x / 2 ^ 192 % 2 ^ 64) :
    bytesAt m p 32 = leBytes 32 x := by
  have e := leNum_bytesAt_words64 m p
  rw [leNum_bytesAt_read, h₀, h₁, h₂, h₃] at e
  rw [bytesAt_leBytes, e, ← leBytes_mod 32 x]
  congr 1
  omega

/-- Eight little-endian 32-bit words in memory are the 32 bytes of `x`, if they
are its eight 32-bit digits. -/
theorem bytesAt_leBytes_words32 (m : Mem) (p : Addr) (x : Nat)
    (h : ∀ j < 8, (m.readW (p + BitVec.ofNat 64 (4 * j)) 32).toNat = x / 2 ^ (32 * j) % 2 ^ 32) :
    bytesAt m p 32 = leBytes 32 x := by
  have e := leNum_bytesAt_words32 m p
  have h0 : (m.readW p 32).toNat = x % 2 ^ 32 := by simpa using h 0 (by omega)
  have h1 : (m.readW (p + 4) 32).toNat = x / 2 ^ 32 % 2 ^ 32 := h 1 (by omega)
  have h2 : (m.readW (p + 8) 32).toNat = x / 2 ^ 64 % 2 ^ 32 := h 2 (by omega)
  have h3 : (m.readW (p + 12) 32).toNat = x / 2 ^ 96 % 2 ^ 32 := h 3 (by omega)
  have h4 : (m.readW (p + 16) 32).toNat = x / 2 ^ 128 % 2 ^ 32 := h 4 (by omega)
  have h5 : (m.readW (p + 20) 32).toNat = x / 2 ^ 160 % 2 ^ 32 := h 5 (by omega)
  have h6 : (m.readW (p + 24) 32).toNat = x / 2 ^ 192 % 2 ^ 32 := h 6 (by omega)
  have h7 : (m.readW (p + 28) 32).toNat = x / 2 ^ 224 % 2 ^ 32 := h 7 (by omega)
  rw [leNum_bytesAt_read, h0, h1, h2, h3, h4, h5, h6, h7] at e
  rw [bytesAt_leBytes, e, ← leBytes_mod 32 x]
  congr 1
  omega

/-! ## The encodings of RFC 7748 -/

theorem leNum_take_succ (l : List Byte) (n : Nat) :
    leNum (l.take (n + 1)) = leNum (l.take n) + 256 ^ n * (l.getD n 0).toNat := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD]
  rcases h : l[n]? with _ | b
  · simp
  · have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
    rw [leNum_append, List.length_take, Nat.min_eq_left (by omega)]
    simp [leNum]

theorem decodeLittleEndian_eq (l : List Byte) : decodeLittleEndian l = leNum (l.take 32) := by
  suffices h : ∀ n, ((List.range n).map fun i => (l.getD i 0).toNat <<< (8 * i)).sum =
      leNum (l.take n) from h 32
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, leNum_take_succ]
    simp only [Nat.shiftLeft_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.mul_comm 8, Nat.pow_mul]
    congr 1
    rw [Nat.mul_comm, ← Nat.pow_mul, Nat.mul_comm n, Nat.pow_mul]

/-- `encodeUCoordinate` is the 32 bytes of the value. -/
theorem encodeUCoordinate_eq (x : Fe) : encodeUCoordinate x = leBytes 32 x.val := by
  simp only [encodeUCoordinate, leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem take_32 {l : List Byte} (h : l.length = 32) : l.take 32 = l :=
  List.take_of_length_le (by omega)

/-- The decoded u-coordinate is the number of its 32 bytes modulo `2²⁵⁵`. -/
theorem decodeUCoordinate_eq {l : List Byte} (h : l.length = 32) :
    decodeUCoordinate l = leNum l % 2 ^ 255 := by
  obtain ⟨l₀, b, rfl⟩ : ∃ l₀ b, l = l₀ ++ [b] := by
    obtain ⟨l₀, b, e⟩ := List.eq_nil_or_concat l |>.resolve_left (by intro e; simp [e] at h)
    exact ⟨l₀, b, by rw [e, List.concat_eq_append]⟩
  have h₀ : l₀.length = 31 := by simpa using h
  rw [decodeUCoordinate, decodeLittleEndian_eq]
  rw [show (l₀ ++ [b]).getD 31 0 = b by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h₀]; rfl]
  rw [List.set_append_right _ _ (by omega), h₀, List.take_of_length_le (by simp [h₀]),
    leNum_append, leNum_append, h₀]
  simp only [Nat.sub_self, List.set_cons_zero, leNum, BitVec.toNat_and]
  have hl := leNum_lt l₀
  rw [h₀] at hl
  have hb := b.isLt
  rw [show (127 : BitVec 8).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A bit of a little-endian number is that bit of one of its bytes. -/
theorem leNum_bit (l : List Byte) (t : Nat) :
    (leNum l >>> t) &&& 1 = ((l.getD (t / 8) 0).toNat >>> (t % 8)) &&& 1 := by
  induction l generalizing t with
  | nil => simp [leNum]
  | cons b bs ih =>
    simp only [leNum, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
    have hb := b.isLt
    rcases Nat.lt_or_ge t 8 with ht | ht
    · rw [Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, List.getD_cons_zero]
      rw [show 256 = 2 ^ t * 2 ^ (8 - t) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]]
      rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
      rw [show 2 ^ (8 - t) = 2 * 2 ^ (8 - t - 1) by rw [← Nat.pow_succ']; congr 1; omega]
      rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · have e := ih (t - 8)
      simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at e
      rw [show t / 8 = (t - 8) / 8 + 1 by omega, List.getD_cons_succ,
        show t % 8 = (t - 8) % 8 by omega, ← e]
      rw [show t = 8 + (t - 8) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
      rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt hb, Nat.zero_add]
      simp

/-- The bits of a byte masked with `248`. -/
theorem bit_and_248 : ∀ x < 256, ∀ r < 8,
    ((x &&& 248) >>> r) &&& 1 = if r < 3 then 0 else (x >>> r) &&& 1 := by decide +kernel

/-- The bits of a byte masked with `127` and then 64 set. -/
theorem bit_and_or_64 : ∀ x < 256, ∀ r < 7,
    (((x &&& 127) ||| 64) >>> r) &&& 1 = if r = 6 then 1 else (x >>> r) &&& 1 := by decide +kernel

theorem getD_set (l : List Byte) {i : Nat} (j : Nat) (a : Byte) (hi : i < l.length) :
    (l.set i a).getD j 0 = if i = j then a else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h
  · subst h; simp only [Option.getD_some]
  · rfl

/-- The bits `0, …, 254` of the decoded scalar: those of its bytes, but for the
clamped ones (bits 0–2 are 0, bit 254 is 1). -/
theorem scalar_bit {kb : List Byte} (h : kb.length = 32) {t : Nat} (ht : t < 255) :
    bit (decodeScalar25519 kb) t =
      if t < 3 then 0 else if t = 254 then 1 else ((kb.getD (t / 8) 0).toNat >>> (t % 8)) &&& 1 := by
  simp only [decodeScalar25519, bit, decodeLittleEndian_eq]
  rw [List.take_of_length_le (by simp [h]), leNum_bit,
    getD_set _ _ _ (by simp [h]), getD_set _ _ _ (by simp [h]), getD_set _ _ _ (by simp [h])]
  rcases Nat.lt_or_ge t 8 with h8 | h8
  · rw [show t / 8 = 0 by omega, show t % 8 = t by omega]
    simp (disch := omega) only [ite_true, ite_eq_left, ite_eq_right]
    rw [BitVec.toNat_and, show (248 : BitVec 8).toNat = 248 from rfl,
      bit_and_248 _ (kb.getD 0 0).isLt _ h8]
  · by_cases h31 : t / 8 = 31
    · rw [h31]
      simp (disch := omega) only [ite_true, ite_eq_right]
      rw [BitVec.toNat_or, BitVec.toNat_and, show (127 : BitVec 8).toNat = 127 from rfl,
        show (64 : BitVec 8).toNat = 64 from rfl, bit_and_or_64 _ (kb.getD 31 0).isLt _ (by omega)]
      split_ifs <;> first | rfl | omega
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.X25519
