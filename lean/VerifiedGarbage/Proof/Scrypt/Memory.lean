import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt: memory lemmas

Addresses and regions, bytes of memory (`Spec.Scrypt.bytesAt`) read and
written, words copied, and the exclusive-or of words, which the proofs of
every target share, so that none imports another target's proof.
-/

namespace VG.Proof.Scrypt.Memory

open VG.Spec.Scrypt (bytesAt blk)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append write_eq_writeBytes)

/-! ## Addresses -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem add_ofNat (a : Addr) (o j : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem toNat_add_ofNat (a : Addr) {o : Nat} (h : a.toNat + o < 2 ^ 64) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o := by
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt h]

/-- `[a + o, a + o + n)` lies in `[a, a + len)`. -/
theorem contains_off {a : Addr} {len o n : Nat} (h : o + n ≤ len) (ho : o < 2 ^ 64) :
    (⟨a, len⟩ : Region).Contains (a + BitVec.ofNat 64 o) n := by
  simp only [Region.Contains]
  rw [show a + BitVec.ofNat 64 o - a = BitVec.ofNat 64 o by rw [BitVec.add_comm, BitVec.add_sub_cancel], toNat_ofNat_lt ho]; omega

/-- `[a + o, a + o + n)` is a sub-region of `[a, a + len)`. -/
theorem sub_off {a : Addr} {len o n : Nat} (h : o + n ≤ len) (ho : o < 2 ^ 64) :
    Region.Sub ⟨a + BitVec.ofNat 64 o, n⟩ ⟨a, len⟩ := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have : (x - a).toNat ≤ (x - (a + BitVec.ofNat 64 o)).toNat + o := by
    rw [show x - a = (x - (a + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o by rw [← BitVec.sub_sub, BitVec.sub_add_cancel],
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-- Two parts `[a + o₁, a + o₁ + n₁)` and `[a + o₂, a + o₂ + n₂)` of one
region that do not overlap. -/
theorem disj_off (a : Addr) {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ < 2 ^ 64) (h₂ : o₂ < 2 ^ 64) (h₁' : o₁ + n₁ ≤ 2 ^ 64) (h₂' : o₂ + n₂ ≤ 2 ^ 64) :
    Region.Disjoint ⟨a + BitVec.ofNat 64 o₁, n₁⟩ ⟨a + BitVec.ofNat 64 o₂, n₂⟩ := by
  intro x hx hy
  simp only [Region.Contains] at hx hy
  have t₁ : (BitVec.ofNat 64 o₁).toNat = o₁ := toNat_ofNat_lt h₁
  have t₂ : (BitVec.ofNat 64 o₂).toNat = o₂ := toNat_ofNat_lt h₂
  bv_omega

theorem InRegions.of_mem {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

theorem InRegions.right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem InRegions.left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions rd a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩

/-! ## Bytes -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    bytesAt m p n = bytesAt m' p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Mem.sub_ofNat_toNat q (show i < 2 ^ 64 by omega), h₂, ite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem bytesAt_writeBytes_sep (m : Mem) {p q : Addr} {n : Nat} (xs : List Byte)
    (h : Region.Disjoint ⟨p, n⟩ ⟨q, xs.length⟩) (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q xs) p n = bytesAt m p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes]
  split
  · exact absurd ‹_› (h _ (by simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat p (by omega)]; exact hi))
  · rfl

/-- The `64 n` bytes at `p` as `n` blocks of 64. -/
theorem bytesAt_blocks (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (64 * n) = (List.range n).flatMap fun i => bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, bytesAt_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- Block `i` of the bytes at `p`. -/
theorem blk_bytesAt (m : Mem) (p : Addr) {n i : Nat} (h : 64 * i + 64 ≤ n) :
    blk (bytesAt m p n) i = bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * i + 64 + k := ⟨n - (64 * i + 64), by omega⟩
  rw [blk, bytesAt_add, bytesAt_add, List.append_assoc, List.drop_left' (bytesAt_length _ _ _),
    List.take_left' (bytesAt_length _ _ _)]

/-! ## Words -/

/-- Writing a word read from memory writes its bytes. -/
theorem writeW_readW (m m' : Mem) (d s : Addr) (n : Nat) :
    m.writeW d (m'.readW s (8 * n)) = writeBytes m d (bytesAt m' s n) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

/-- One more word of `w` bytes copied from `A` to `B`. -/
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
    simp only [Region.Contains, bytesAt, List.length_map, List.length_range] at hx hy
    apply hsep x _ (by omega)
    rw [show x - A = (x - (A + BitVec.ofNat 64 (w * n))) + BitVec.ofNat 64 (w * n) by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (w * n))).toNat + w * n) (2 ^ 64)
    omega
  · omega

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) : (xorBytes a b).length = a.length := by
  simp [xorBytes, h]

/-! ## The exclusive-or of words -/

theorem writeW_xor (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 64 ^^^ m'.readW b 64) =
      writeBytes m d (xorBytes (bytesAt m' a 8) (bytesAt m' b 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁]

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 8 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).writeW
      (d + BitVec.ofNat 64 (8 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).readW
          (x + BitVec.ofNat 64 (8 * k)) 64 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).readW
          (y + BitVec.ofNat 64 (8 * k)) 64) =
      writeBytes m d (xorBytes (bytesAt m x (8 * (k + 1))) (bytesAt m y (8 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length = 8 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  -- The words of `x` and `y` are not in the part of `d` written so far.
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨d, (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨d, (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (8 * k)) 8)
    (bytesAt m (y + BitVec.ofNat 64 (8 * k)) 8))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-! ## Arithmetic -/

theorem dbl_pow (x k : Nat) : BitVec.ofNat 64 (x * 2 ^ k) + BitVec.ofNat 64 (x * 2 ^ k) =
    BitVec.ofNat 64 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

end VG.Proof.Scrypt.Memory
