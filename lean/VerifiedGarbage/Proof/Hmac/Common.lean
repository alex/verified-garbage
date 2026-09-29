import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Spec.Hmac

/-!
# HMAC-SHA-256: lemmas shared by every target

Untrusted: everything here is checked by Lean. Bytes copied between memory
regions and read back, hash values written and read, and the streaming states
`init` and `finalize` leave, about memory alone: every target's proof uses
them, so they import no target's ISA or proofs.
-/

namespace VG.Proof.Hmac.Common
open VG
open VG.Proof.Sha256.Stream (writeBytes write_eq_writeBytes writeBytes_append writeBytes_nil
  compressList_append repr_nil repr_append_block)
open VG.Spec.Sha256 (bytesAt stateAt Repr H0 HashValue Word)
open VG.Spec.Hmac (xorPad opad)

/-! ## Bytes -/

private theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem extractLsb'_read (m : Mem) (a : Addr) {n j : Nat} (hj : j < n) :
    (m.read a n).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    simp only [Mem.read]
    cases j with
    | zero =>
      rw [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      simp [hi]
    | succ j =>
      rw [show a + BitVec.ofNat 64 (j + 1) = a + 1 + BitVec.ofNat 64 j by bv_omega,
        ← ih (a := a + 1) (by omega)]
      ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append,
        show ¬ (8 * (j + 1) + i < 8) by omega, ite_false]
      congr 1; omega

/-- Writing a word read from memory writes its bytes. -/
theorem writeW_readW (m m' : Mem) (d s : Addr) (n : Nat) :
    m.writeW d (m'.readW s (8 * n)) = writeBytes m d (bytesAt m' s n) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => extractLsb'_read _ _ (List.mem_range.mp hj)

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_writeBytes_sep (m : Mem) {p q : Addr} {n : Nat} (xs : List Byte)
    (h : Mem.Sep p n q xs.length) (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q xs) p n = bytesAt m p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes]
  split
  · exact absurd ‹_› (h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hi))
  · rfl

/-- One more word copied from `A` to `B`. -/
theorem copy_mem (m : Mem) (A B : Addr) (n w : Nat)
    (hsep : Mem.Sep A (w * n + w) B (w * n + w)) (hlt : w * n + w < 2 ^ 64) :
    (writeBytes m B (bytesAt m A (w * n))).writeW (B + BitVec.ofNat 64 (w * n))
      ((writeBytes m B (bytesAt m A (w * n))).readW (A + BitVec.ofNat 64 (w * n)) (8 * w)) =
      writeBytes m B (bytesAt m A (w * n + w)) := by
  rw [writeW_readW, bytesAt_writeBytes_sep]
  · rw [bytesAt_add]
    have := writeBytes_append m B (bytesAt m A (w * n)) (bytesAt m (A + BitVec.ofNat 64 (w * n)) w)
      (by simp [bytesAt]; omega)
    simpa [bytesAt] using this
  · intro x hx hy
    simp only [bytesAt, List.length_map, List.length_range] at hy
    apply hsep x _ (by omega)
    rw [show x - A = (x - (A + BitVec.ofNat 64 (w * n))) + BitVec.ofNat 64 (w * n) by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (w * n))).toNat + w * n) (2 ^ 64)
    omega
  · omega

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

theorem read_congr₂ {m m' : Mem} {a b : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)) : m.read a n = m'.read b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega)
    rwa [show a + BitVec.ofNat 64 (i + 1) = a + 1 + BitVec.ofNat 64 i by bv_omega,
      show b + BitVec.ofNat 64 (i + 1) = b + 1 + BitVec.ofNat 64 i by bv_omega] at this

/-- A hash value is determined by its 32 bytes. -/
theorem stateAt_eq_of_bytes {m m' : Mem} {p q : Addr}
    (h : ∀ i < 32, m (p + BitVec.ofNat 64 i) = m' (q + BitVec.ofNat 64 i)) : stateAt m p = stateAt m' q := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Mem.readW]
  congr 1
  refine read_congr₂ fun i hi => ?_
  have := h (4 * j + i) (by omega)
  rwa [show p + BitVec.ofNat 64 (4 * j + i) = p + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 i by
      simp only [BitVec.ofNat_add, BitVec.add_assoc],
    show q + BitVec.ofNat 64 (4 * j + i) = q + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 i by
      simp only [BitVec.ofNat_add, BitVec.add_assoc]] at this

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length)
    (hl : xs.length < 2 ^ 64) : writeBytes m q xs (q + BitVec.ofNat 64 i) = xs.getD i 0 := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q (show i < 2 ^ 64 by omega), hi, ite_true]

theorem writeBytes_other (m : Mem) (q : Addr) (xs : List Byte) {x : Addr}
    (hx : ¬ (x - q).toNat < xs.length) : writeBytes m q xs x = m x := by
  simp only [writeBytes, hx, ite_false]

theorem bytesAt_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [writeBytes_at _ _ _ h₂ hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- A byte written right after `j` bytes. -/
theorem bytesAt_snoc (m : Mem) (p : Addr) {j : Nat} (hj : j + 1 < 2 ^ 64) (x : Byte) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 j) x) p (j + 1) = bytesAt m p j ++ [x] := by
  rw [bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [Mem.writeW]
    refine Mem.write_apply ?_
    rw [show p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 j) = BitVec.ofNat 64 i - BitVec.ofNat 64 j by bv_omega,
      BitVec.toNat_sub, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    omega
  · have e : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 - (p + BitVec.ofNat 64 j) = 0 := by bv_omega
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, Mem.writeW, Mem.write, e,
]
    simp

/-! ## Hash values

Those of `Proof/Sha256/StateMem.lean`. -/

export VG.Proof.Sha256.StateMem (word_sep readW_writeW_word stateAt_eq writeState stateAt_writeState)

/-! ## Streaming states -/

theorem blockAt_eq {m : Mem} {p : Addr} {xs : List Byte} (h : bytesAt m p 64 = xs) :
    Spec.Sha256.blockAt m p = Spec.Sha256.parseBlock fun k => xs.getD k 0 :=
  Proof.Sha256.Stream.parseBlock_congr fun _ hk => by
    subst h; exact (bytesAt_getD' _ _ hk).symm

/-- A state with `H⁽⁰⁾` and a full buffer `xs`, compressed, represents `xs`. -/
theorem repr_block {m m' : Mem} {p : Addr} {xs : List Byte} (hst : stateAt m p = H0)
    (hb : bytesAt m (p + 32) 64 = xs) (hx : xs.length = 64)
    (hs : stateAt m' p = Spec.Sha256.compress (stateAt m p) (Spec.Sha256.blockAt m (p + 32))) :
    Repr m' p xs := by
  have := repr_append_block (mem' := m') (xs := xs) (repr_nil hst) (by simp [hx])
    (by rw [hs, blockAt_eq hb]; simp)
  simpa using this

theorem xorPad_length (k : List Byte) (p : Byte) : (xorPad k p).length = k.length := by
  simp [xorPad]

/-- A state holding the outer hash value and a 32-byte digest represents
`(K₀ ⊕ opad) ‖ digest`. -/
theorem repr_outer {k0 d : List Byte} (hk : k0.length = 64) (hd : d.length = 32) {m : Mem} {p : Addr}
    (hst : stateAt m p = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1)
    (hb : bytesAt m (p + 32) 32 = d) : Repr m p (xorPad k0 opad ++ d) := by
  have hl : (xorPad k0 opad ++ d).length = 96 := by simp [xorPad_length, hk, hd]
  refine ⟨?_, ?_⟩
  · rw [hl, show 96 / 64 = 1 from rfl, compressList_append (by rw [xorPad_length, hk]), hst]
  · rw [hl, show 96 % 64 = 32 from rfl, show 64 * (96 / 64) = 64 from rfl,
      List.drop_left' (by rw [xorPad_length, hk]), hb]

end VG.Proof.Hmac.Common
