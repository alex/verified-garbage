import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The SHA-3 sponge: facts about the specification

The state byte by byte, how the streaming representation `Repr` evolves as
bytes are absorbed one at a time, how padding is absorbed, and the output of
`squeeze` byte by byte, independently of any target.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3

/-! ## States byte by byte -/

/-- Byte `j` of a state (`(toBytes A)[j]`, for `j < 200`). -/
def byteOf (A : State) (j : Nat) : Byte := A[j / 8]!.extractLsb' (8 * (j % 8)) 8

theorem byteOf_eq (A : State) {i k : Nat} (hi : i < 25) (hk : k < 8) :
    byteOf A (8 * i + k) = A[i].extractLsb' (8 * k) 8 := by
  simp only [byteOf, show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega,
    getElem!_pos A i hi]

theorem byteOf_eq' (A : State) {j : Nat} (hj : j < 200) :
    byteOf A j = A[j / 8].extractLsb' (8 * (j % 8)) 8 := by
  rw [← byteOf_eq A (by omega) (by omega), show 8 * (j / 8) + j % 8 = j by omega]

theorem ext_bytes {A B : State} (h : ∀ j < 200, byteOf A j = byteOf B j) : A = B := by
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have := congrArg (fun x : Byte => x.getLsbD (b % 8)) (h (8 * i + b / 8) (by omega))
  simp only [byteOf_eq A hi (show b / 8 < 8 by omega), byteOf_eq B hi (show b / 8 < 8 by omega),
    BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega, decide_true, Bool.true_and,
    show 8 * (b / 8) + b % 8 = b by omega] at this
  exact this

theorem byteOf_stateAt (m : Mem) (p : Addr) {j : Nat} (hj : j < 200) :
    byteOf (stateAt m p) j = m (p + BitVec.ofNat 64 j) := by
  rw [byteOf_eq' _ hj]
  simp only [stateAt, Vector.getElem_ofFn, Mem.readW]
  rw [show (m.read (p + BitVec.ofNat 64 (8 * (j / 8))) (64 / 8)).setWidth 64
      = m.read (p + BitVec.ofNat 64 (8 * (j / 8))) 8 from BitVec.setWidth_eq _,
    Mem.extractLsb'_read m _ (show j % 8 < 8 by omega)]
  congr 1
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (j / 8) + j % 8 = j by omega]

theorem extractLsb'_append_lo {n : Nat} (x : BitVec n) (y : Byte) :
    (x ++ y).extractLsb' 0 8 = y := by
  ext i hi
  simp [BitVec.getLsbD_append, hi]

theorem extractLsb'_append_hi {n : Nat} (x : BitVec n) (y : Byte) {s : Nat} (hs : 8 ≤ s) :
    (x ++ y).extractLsb' s 8 = x.extractLsb' (s - 8) 8 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, show ¬ s + i < 8 by omega,
    ite_false]
  congr 1; omega

theorem extractLsb'_byte (y : Byte) : y.extractLsb' 0 8 = y := by
  ext i hi; simp

theorem extractLsb'_laneOfBytes (b : Nat → Byte) {k : Nat} (hk : k < 8) :
    (laneOfBytes b).extractLsb' (8 * k) 8 = b k := by
  unfold laneOfBytes
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega) only [extractLsb'_append_hi, extractLsb'_append_lo,
    extractLsb'_byte, Nat.reduceMul, Nat.reduceSub]

theorem byteOf_xorBytes (A : State) (bs : List Byte) {j : Nat} (hj : j < 200) :
    byteOf (xorBytes A bs) j = byteOf A j ^^^ bs.getD j 0 := by
  rw [byteOf_eq' _ hj, byteOf_eq' _ hj]
  simp only [xorBytes, Vector.getElem_ofFn, BitVec.extractLsb'_xor,
    extractLsb'_laneOfBytes _ (show j % 8 < 8 by omega), show 8 * (j / 8) + j % 8 = j by omega,
    Fin.getElem_fin]

theorem length_flatMap8 {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length = 8)
    (L : List α) : (L.flatMap f).length = 8 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, hf, ih, List.length_cons]
    omega

theorem getElem_flatMap8 {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length = 8) :
    ∀ (L : List α) {j : Nat} (hj : j < (L.flatMap f).length),
      (L.flatMap f)[j] = (f (L[j / 8]'(by rw [length_flatMap8 f hf] at hj; omega)))[j % 8]'(by
          rw [hf]; omega)
  | [], _, hj => by simp at hj
  | a :: L, j, hj => by
    simp only [List.flatMap_cons]
    by_cases h : j < 8
    · rw [List.getElem_append_left (by rw [hf]; exact h)]
      simp only [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, List.getElem_cons_zero]
    · rw [List.getElem_append_right (by rw [hf]; omega)]
      simp only [hf]
      rw [getElem_flatMap8 f hf L]
      simp only [show j / 8 = (j - 8) / 8 + 1 by omega, show (j - 8) % 8 = j % 8 by omega,
        List.getElem_cons_succ]

theorem length_toBytes (A : State) : (toBytes A).length = 200 := by
  rw [toBytes, length_flatMap8 _ (fun _ => by simp)]
  simp

theorem toBytes_getElem (A : State) {j : Nat} (hj : j < 200) :
    (toBytes A)[j]'(by rw [length_toBytes]; exact hj) = byteOf A j := by
  unfold toBytes
  rw [getElem_flatMap8 _ (fun _ => by simp)]
  simp only [List.getElem_map, List.getElem_range, Vector.getElem_toList]
  exact (byteOf_eq' A hj).symm

theorem getD_snoc (L : List Byte) (b : Byte) (i : Nat) :
    (L ++ [b]).getD i 0 = if i = L.length then b else L.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_singleton]
  split
  · simp only [show i ≠ L.length by omega, ↓reduceIte]
  · split
    · simp only [show i = L.length by omega, ↓reduceIte]; rfl
    · simp only [show i ≠ L.length by omega, ↓reduceIte, List.getElem?_eq_none (show L.length ≤ i by omega)]

theorem getD_append_replicate (L : List Byte) (n i : Nat) :
    (L ++ List.replicate n 0).getD i 0 = L.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    split <;> rfl

theorem xorBytes_nil (A : State) : xorBytes A [] = A :=
  ext_bytes fun j hj => by
    rw [byteOf_xorBytes _ _ hj, List.getD_nil]; exact BitVec.xor_zero

/-- `A` with the byte `b` XORed into byte `j`. -/
def xorByte (A : State) (j : Nat) (b : Byte) : State := xorBytes A (List.replicate j 0 ++ [b])

theorem byteOf_xorByte (A : State) (j : Nat) (b : Byte) {i : Nat} (hi : i < 200) :
    byteOf (xorByte A j b) i = if i = j then byteOf A i ^^^ b else byteOf A i := by
  rw [xorByte, byteOf_xorBytes _ _ hi, getD_snoc, List.length_replicate]
  have h := getD_append_replicate [] j i
  rw [List.nil_append, List.getD_nil] at h
  split
  · rfl
  · rw [h]; exact BitVec.xor_zero

/-- A state in memory whose bytes change only at byte `j`, by XORing `b`
into it. -/
theorem stateAt_xorByte {m m' : Mem} {p : Addr} {j : Nat} (hj : j < 200) {b : Byte}
    (hj' : m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) ^^^ b)
    (ho : ∀ i < 200, i ≠ j → m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    stateAt m' p = xorByte (stateAt m p) j b :=
  ext_bytes fun i hi => by
    have _ := hj
    rw [byteOf_xorByte _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi]
    split
    · subst i; exact hj'
    · exact ho i hi (by assumption)

theorem stateAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 200, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    stateAt m' p = stateAt m p :=
  ext_bytes fun i hi => by rw [byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi]; exact h i hi

/-! ## Absorbing -/

/-- The state after absorbing the first `k` blocks of `P`. -/
def absorbN (rate : Nat) (P : List Byte) (k : Nat) : State :=
  (List.range k).foldl (fun S i => keccakF (xorBytes S (block rate P i))) zero

theorem absorb_eq (rate : Nat) (P : List Byte) : absorb rate P = absorbN rate P (P.length / rate) :=
  rfl

theorem absorbN_succ (rate : Nat) (P : List Byte) (k : Nat) :
    absorbN rate P (k + 1) = keccakF (xorBytes (absorbN rate P k) (block rate P k)) := by
  simp only [absorbN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem block_append {rate : Nat} {P : List Byte} (Q : List Byte) {i : Nat}
    (h : rate * i + rate ≤ P.length) : block rate (P ++ Q) i = block rate P i := by
  simp only [block]
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem absorbN_append {rate : Nat} {P : List Byte} (Q : List Byte) :
    ∀ {k : Nat}, rate * k ≤ P.length → absorbN rate (P ++ Q) k = absorbN rate P k := by
  intro k
  induction k with
  | zero => intro _; simp only [absorbN, List.range_zero, List.foldl_nil]
  | succ k ih =>
    intro h
    rw [Nat.mul_succ] at h
    rw [absorbN_succ, absorbN_succ, ih (by omega), block_append Q h]

theorem xorBytes_snoc (A : State) (L : List Byte) (b : Byte) :
    xorBytes A (L ++ [b]) = xorByte (xorBytes A L) L.length b :=
  ext_bytes fun j hj => by
    rw [byteOf_xorByte _ _ _ hj, byteOf_xorBytes _ _ hj, byteOf_xorBytes _ _ hj, getD_snoc]
    split
    · subst j
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_refl _)]
      exact (congrArg (· ^^^ b) BitVec.xor_zero).symm
    · rfl

theorem xorBytes_append_replicate (A : State) (L : List Byte) (n : Nat) :
    xorBytes A (L ++ List.replicate n 0) = xorBytes A L :=
  ext_bytes fun j hj => by
    rw [byteOf_xorBytes _ _ hj, byteOf_xorBytes _ _ hj, getD_append_replicate]

theorem xorByte_xorByte (A : State) (j : Nat) (b c : Byte) :
    xorByte (xorByte A j b) j c = xorByte A j (b ^^^ c) :=
  ext_bytes fun i hi => by
    rw [byteOf_xorByte _ _ _ hi, byteOf_xorByte _ _ _ hi, byteOf_xorByte _ _ _ hi]
    split
    · exact BitVec.xor_assoc _ _ _
    · rfl

/-- The length of a message as whole blocks and a remainder. -/
theorem length_split {rate : Nat} (hr : 0 < rate) (msg : List Byte) :
    rate * (msg.length / rate) + msg.length % rate = msg.length ∧ msg.length % rate < rate ∧
      (msg.drop (rate * (msg.length / rate))).length = msg.length % rate := by
  have h1 := Nat.div_add_mod msg.length rate
  have h2 := Nat.mod_lt msg.length hr
  refine ⟨h1, h2, ?_⟩
  rw [List.length_drop]
  omega

/-- The state that represents `msg` (`Repr`). -/
def Rep (rate : Nat) (msg : List Byte) : State :=
  xorBytes (absorb rate msg) (msg.drop (rate * (msg.length / rate)))

theorem repr_iff {mem : Mem} {p : Addr} {rate : Nat} {msg : List Byte} :
    Repr mem p rate msg ↔ stateAt mem p = Rep rate msg := Iff.rfl

theorem rep_nil (rate : Nat) : Rep rate [] = zero := by
  rw [Rep, List.drop_nil, xorBytes_nil, absorb, List.length_nil, Nat.zero_div]
  rfl

/-- Absorbing one byte: it is XORed into the state at the position in the
block, and the state is permuted if that completes the block. -/
theorem rep_snoc {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (msg : List Byte) (b : Byte) :
    Rep rate (msg ++ [b]) =
      if msg.length % rate + 1 = rate then keccakF (xorByte (Rep rate msg) (msg.length % rate) b)
      else xorByte (Rep rate msg) (msg.length % rate) b := by
  have _ := hr'
  obtain ⟨h1, h2, h3⟩ := length_split hr msg
  have hl : (msg ++ [b]).length = msg.length + 1 := by simp
  simp only [Rep, hl]
  rw [← h3, ← xorBytes_snoc]
  generalize hq : msg.length / rate = q at h1 h3 ⊢
  have ha : absorbN rate msg q = absorb rate msg := by rw [absorb_eq, hq]
  split
  · have hq' : (msg.length + 1) / rate = q + 1 :=
      Nat.div_eq_of_lt_le (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
        (by rw [Nat.succ_mul, Nat.succ_mul, Nat.mul_comm]; omega)
    rw [hq', List.drop_eq_nil_of_le (by rw [hl, Nat.mul_succ]; omega), xorBytes_nil, absorb_eq,
      hl, hq', absorbN_succ, absorbN_append _ (by omega), block, ha,
      List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]
  · have hq' : (msg.length + 1) / rate = q :=
      Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega)
        (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
    rw [hq', absorb_eq, hl, hq', absorbN_append _ (by omega), ha,
      List.drop_append_of_le_length (by omega)]

/-- `A` with the bytes `bs` XORed into it from byte `j` on. -/
def xorAt (A : State) (j : Nat) (bs : List Byte) : State :=
  (List.range bs.length).foldl (fun S d => xorByte S (j + d) (bs.getD d 0)) A

theorem foldl_range_congr {α : Type} {f g : α → Nat → α} (A : α) :
    ∀ n, (∀ S d, d < n → f S d = g S d) → (List.range n).foldl f A = (List.range n).foldl g A
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_append, foldl_range_congr A n
      (fun S d hd => h S d (by omega)), List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil, h _ n (by omega)]

/-- Induction on a list from its end. -/
theorem snoc_induction {P : List Byte → Prop} (h0 : P []) (hs : ∀ bs b, P bs → P (bs ++ [b])) :
    ∀ bs, P bs := by
  intro bs
  rw [← List.reverse_reverse bs]
  induction bs.reverse with
  | nil => exact h0
  | cons b l ih => rw [List.reverse_cons]; exact hs _ _ ih

theorem xorAt_snoc (A : State) (j : Nat) (bs : List Byte) (b : Byte) :
    xorAt A j (bs ++ [b]) = xorByte (xorAt A j bs) (j + bs.length) b := by
  unfold xorAt
  rw [List.length_append, List.length_singleton, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, getD_snoc, ite_eq_left rfl,
    foldl_range_congr A bs.length fun S d hd => by rw [getD_snoc, ite_eq_right (by omega)]]

theorem xorAt_single (A : State) (j : Nat) (b : Byte) : xorAt A j [b] = xorByte A j b := by
  simp [xorAt]

theorem byteOf_xorAt (A : State) (j : Nat) (bs : List Byte) {i : Nat} (hi : i < 200) :
    byteOf (xorAt A j bs) i =
      if j ≤ i ∧ i < j + bs.length then byteOf A i ^^^ bs.getD (i - j) 0 else byteOf A i := by
  induction bs using snoc_induction generalizing i with
  | h0 => simp [xorAt]
  | hs bs b ih =>
    rw [xorAt_snoc, byteOf_xorByte _ _ _ hi, List.length_append, List.length_singleton]
    by_cases e : i = j + bs.length
    · subst e
      rw [ite_eq_left rfl, ih hi, ite_eq_right (by omega), ite_eq_left (by omega), getD_snoc,
        ite_eq_left (by omega)]
    · rw [ite_eq_right e, ih hi]
      by_cases c : j ≤ i ∧ i < j + bs.length
      · rw [ite_eq_left c, ite_eq_left (by omega), getD_snoc, ite_eq_right (by omega)]
      · rw [ite_eq_right c, ite_eq_right (by omega)]

/-- Absorbing bytes that fit in the block: they are XORed into the state
from the position in the block, and the state is permuted if they complete
it. -/
theorem rep_append {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (msg : List Byte) :
    ∀ (bs : List Byte), 0 < bs.length → msg.length % rate + bs.length ≤ rate →
      Rep rate (msg ++ bs) =
        if msg.length % rate + bs.length = rate then keccakF (xorAt (Rep rate msg) (msg.length % rate) bs)
        else xorAt (Rep rate msg) (msg.length % rate) bs := by
  intro bs
  induction bs using snoc_induction with
  | h0 => intro h; simp at h
  | hs bs b ih =>
    intro _ hfit
    simp only [List.length_append, List.length_singleton] at hfit ⊢
    rw [← List.append_assoc, rep_snoc hr hr']
    have hl : (msg ++ bs).length % rate = msg.length % rate + bs.length := by
      rw [List.length_append]
      have := Nat.div_add_mod msg.length rate
      rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hl]
    by_cases h0 : bs = []
    · subst h0
      simp only [List.length_nil, Nat.add_zero, Nat.zero_add, List.append_nil, List.nil_append,
        xorAt_single]
    · have hb : 0 < bs.length := List.length_pos_iff.mpr h0
      rw [ih hb (by omega), ite_eq_right (show ¬ (msg.length % rate + bs.length = rate) by omega),
        xorAt_snoc, Nat.add_assoc]

/-- The padding: the suffix XORed into the byte at the position in the
block, `0x80` into the last byte of the block, and the state permuted. -/
theorem absorb_pad {rate : Nat} (hr : 1 < rate) (hr' : rate ≤ 200) (suffix : Byte) (msg : List Byte) :
    absorb rate (pad rate suffix msg) =
      keccakF (xorByte (xorByte (Rep rate msg) (msg.length % rate) suffix) (rate - 1) 0x80) := by
  have _ := hr'
  obtain ⟨h1, h2, h3⟩ := length_split (rate := rate) (by omega) msg
  have hp : (padding rate suffix msg.length).length = rate - msg.length % rate := by
    simp only [padding]
    split
    · simp only [List.length_singleton]; omega
    · simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
      omega
  have hl : (pad rate suffix msg).length = msg.length + (rate - msg.length % rate) := by
    simp only [pad, List.length_append, hp]
  simp only [Rep]
  generalize hq : msg.length / rate = q at h1 h3 ⊢
  have ha : absorbN rate msg q = absorb rate msg := by rw [absorb_eq, hq]
  have hq' : (pad rate suffix msg).length / rate = q + 1 := by
    rw [hl]
    exact Nat.div_eq_of_lt_le (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
      (by rw [Nat.succ_mul, Nat.succ_mul, Nat.mul_comm]; omega)
  rw [absorb_eq, hq', absorbN_succ, pad, absorbN_append _ (by omega), ha, block,
    List.drop_append_of_le_length (by omega),
    List.take_of_length_le (by rw [List.length_append, hp]; omega)]
  refine congrArg keccakF ?_
  generalize List.drop (rate * q) msg = L at h3 ⊢
  generalize absorb rate msg = A
  simp only [padding]
  split
  · rw [xorBytes_snoc, h3, show rate - 1 = msg.length % rate by omega, xorByte_xorByte]
  · rw [List.cons_append, ← List.singleton_append, ← List.append_assoc, ← List.append_assoc,
      xorBytes_snoc, xorBytes_append_replicate, xorBytes_snoc, h3]
    simp only [List.length_append, List.length_singleton, List.length_replicate, h3]
    rw [show msg.length % rate + 1 + (rate - msg.length % rate - 2) = rate - 1 by omega]

/-! ## Squeezing -/

/-- The state after `k` permutations. -/
def iterF (k : Nat) (S : State) : State := Nat.repeat keccakF k S

theorem iterF_succ (k : Nat) (S : State) : iterF (k + 1) S = keccakF (iterF k S) := rfl

theorem iterF_keccakF (k : Nat) (S : State) : iterF k (keccakF S) = iterF (k + 1) S := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterF_succ, ih, iterF_succ (k + 1)]

theorem length_squeezeBlocks {rate : Nat} (hr' : rate ≤ 200) (n : Nat) :
    ∀ S : State, (squeezeBlocks rate S n).length = rate * n := by
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro S
    simp only [squeezeBlocks, List.length_append, List.length_take, length_toBytes, ih]
    rw [Nat.mul_succ]
    omega

theorem getElem_squeezeBlocks {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (n : Nat) :
    ∀ (S : State) {i : Nat} (hi : i < (squeezeBlocks rate S n).length),
      (squeezeBlocks rate S n)[i] = byteOf (iterF (i / rate) S) (i % rate) := by
  induction n with
  | zero => intro _ _ hi; simp [squeezeBlocks] at hi
  | succ n ih =>
    intro S i hi
    simp only [squeezeBlocks]
    have ht : ((toBytes S).take rate).length = rate := by
      rw [List.length_take, length_toBytes]; omega
    by_cases h : i < rate
    · rw [List.getElem_append_left (by rw [ht]; exact h), List.getElem_take, toBytes_getElem _ (by omega),
        Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rw [List.getElem_append_right (by rw [ht]; omega)]
      simp only [ht]
      have hl := length_squeezeBlocks hr' (n + 1) S
      rw [Nat.mul_succ] at hl
      have e1 : (i - rate) / rate + 1 = i / rate := (Nat.div_eq_sub_div hr (by omega)).symm
      have e2 : (i - rate) % rate = i % rate := (Nat.mod_eq_sub_mod (by omega)).symm
      have hi' : i - rate < (squeezeBlocks rate (keccakF S) n).length := by
        rw [length_squeezeBlocks hr']; omega
      rw [ih (keccakF S) hi', iterF_keccakF, e1, e2]

theorem length_squeeze {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (d : Nat) :
    (squeeze rate S d).length = d := by
  rw [squeeze, List.length_take, length_squeezeBlocks hr']
  have h1 := Nat.div_add_mod (d + rate - 1) rate
  have h2 := Nat.mod_lt (d + rate - 1) hr
  omega

/-- Byte `i` of the output is byte `i mod r` of the state after `⌊i / r⌋`
permutations. -/
theorem squeeze_getElem {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) {d i : Nat}
    (hi : i < d) :
    (squeeze rate S d)[i]'(by rw [length_squeeze hr hr']; exact hi) =
      byteOf (iterF (i / rate) S) (i % rate) := by
  simp only [squeeze]
  rw [List.getElem_take, getElem_squeezeBlocks hr hr']

end VG.Proof.Sha3

section

/-!
# The SHA-3 sponge: output squeezed from an offset

`squeezeFrom` byte by byte, and after permutations.
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

end
