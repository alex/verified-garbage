import VerifiedGarbage.Proof.Poly1305.Spec
import Mathlib.Tactic.Conv

/-!
# Poly1305: the streaming state, for every target

Untrusted: everything here is checked by Lean. Counters, bytes written to
memory, and a message with its last bytes buffered (`Buffered`) as its whole
blocks and the rest.
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (bytesAt Repr Buffered)

/-! ## Counters -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-! ## Bytes in memory -/

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      bv_omega
    simp only [this, h, ↓reduceIte]

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- `m` with the bytes `xs` written from `q` on. -/
def writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Mem :=
  fun a => if (a - q).toNat < xs.length then xs.getD (a - q).toNat 0 else m a

theorem writeBytes_nil (m : Mem) (q : Addr) : writeBytes m q [] = m := by
  funext a; simp [writeBytes]

theorem writeBytes_snoc (m : Mem) (q : Addr) (xs : List Byte) (b : Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q (xs ++ [b]) = (writeBytes m q xs).writeW (q + BitVec.ofNat 64 xs.length) b := by
  funext a
  rw [writeW8_apply]
  simp only [writeBytes, List.length_append, List.length_singleton]
  by_cases ha : a = q + BitVec.ofNat 64 xs.length
  · subst ha
    rw [show q + BitVec.ofNat 64 xs.length - q = BitVec.ofNat 64 xs.length by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    simp [List.getD_eq_getElem?_getD]
  · have hne : (a - q).toNat ≠ xs.length := by
      intro h'
      apply ha
      have : a - q = BitVec.ofNat 64 xs.length :=
        BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])
      bv_omega
    simp only [ha, ite_false]
    by_cases hl : (a - q).toNat < xs.length
    · simp only [show (a - q).toNat < xs.length + 1 by omega, hl, ite_true]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
    · simp only [show ¬ (a - q).toNat < xs.length + 1 by omega, hl, ite_false]

/-- The bytes before `q` (within `2⁶⁴ - |xs|`) are unchanged. -/
theorem writeBytes_before (m : Mem) (q : Addr) (xs : List Byte) {i d : Nat} (hi : i < d)
    (h : d + xs.length < 2 ^ 64) :
    writeBytes m (q + BitVec.ofNat 64 d) xs (q + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  split
  · rename_i hc
    rw [show q + BitVec.ofNat 64 i - (q + BitVec.ofNat 64 d) = BitVec.ofNat 64 i - BitVec.ofNat 64 d by
      bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (a := d) (by omega), show 2 ^ 64 - d + i = 2 ^ 64 - (d - i) by omega,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega
  · rfl

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j by
      simp only [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

theorem writeBytes_frame (m : Mem) (q : Addr) (xs : List Byte) {R : Region} (hR : R.Contains q xs.length) :
    Frame [R] m (writeBytes m q xs) := by
  intro x hx
  simp only [writeBytes]
  split
  · rename_i h; exact absurd (hR.byte h) (hx R (List.mem_singleton_self _))
  · rfl

/-! ## Whole blocks and the rest -/

theorem take_whole {a b : List Byte} (ha : a.length % 16 = 0) (hb : b.length < 16) :
    (a ++ b).take (16 * ((a ++ b).length / 16)) = a := by
  rw [show 16 * ((a ++ b).length / 16) = a.length by simp only [List.length_append]; omega,
    List.take_left' rfl]

theorem drop_whole {a b : List Byte} (ha : a.length % 16 = 0) (hb : b.length < 16) :
    (a ++ b).drop (16 * ((a ++ b).length / 16)) = b := by
  rw [show 16 * ((a ++ b).length / 16) = a.length by simp only [List.length_append]; omega,
    List.drop_left' rfl]

/-- A message with its last bytes buffered: its whole blocks, which the
state represents as `Repr` does, and the buffered bytes. -/
theorem Buffered.split {m : Mem} {st : Addr} {key msg : List Byte} (h : Buffered m st key msg) :
    ∃ w b, msg = w ++ b ∧ Repr m st key w ∧ b.length = msg.length % 16 ∧
      bytesAt m (st + 56) (msg.length % 16) = b :=
  ⟨_, _, (List.take_append_drop _ _).symm, h.1, by simp only [List.length_drop]; omega, h.2⟩

theorem Buffered.of {m : Mem} {st : Addr} {key w b : List Byte} (hr : Repr m st key w) (hb : b.length < 16)
    (hbuf : bytesAt m (st + 56) b.length = b) : Buffered m st key (w ++ b) := by
  have hw := hr.1
  refine ⟨by rw [take_whole hw hb]; exact hr, ?_⟩
  rw [drop_whole hw hb, show (w ++ b).length % 16 = b.length by simp only [List.length_append]; omega]
  exact hbuf

/-- A message of whole blocks, with nothing buffered. -/
theorem Repr.buffered {m : Mem} {st : Addr} {key msg : List Byte} (h : Repr m st key msg) :
    Buffered m st key msg := by
  have e := Buffered.of (b := []) h (by simp) rfl
  rwa [List.append_nil] at e

end VG.Proof.Poly1305
