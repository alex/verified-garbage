import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.Spec

/-!
# GCM: GHASH and counter mode over a message given in pieces

Untrusted: everything here is checked by Lean. Target-independent lemmas
about the steps the implementations of AES-GCM take (on every target):

* GHASH absorbs a string `x` a piece at a time (`Absorbed`): the whole
  blocks into the accumulator `Y`, the rest buffered. A piece is absorbed by
  filling the buffer (`absorb_fill`, `absorb_complete`), then whole blocks
  (`absorb_whole`), then buffering the rest (`absorb_tail`); the buffer is
  padded with zeros and absorbed (`absorb_pad`).
* Counter mode XORs the `i`-th byte of the keystream (`ksByte`) into the
  `i`-th byte of the text (`gctr_eq`), whose counter block and keystream
  block the state keeps (`Ctr`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

/-! ## Blocks and GHASH -/

theorem ghashFrom_append (h y : Block) (xs ys : List Block) :
    ghashFrom h y (xs ++ ys) = ghashFrom h (ghashFrom h y xs) ys := by
  simp only [ghashFrom, List.foldl_append]

theorem ghashFrom_nil (h y : Block) : ghashFrom h y [] = y := rfl

theorem length_blocks (bs : List Byte) : (blocks bs).length = bs.length / 16 := by
  simp [blocks]

theorem blocks_of_lt {bs : List Byte} (h : bs.length < 16) : blocks bs = [] := by
  simp [blocks, Nat.div_eq_of_lt h]

theorem blocks_cons {bs : List Byte} (h : 16 ≤ bs.length) :
    blocks bs = ofBytes (bs.take 16) :: blocks (bs.drop 16) := by
  obtain ⟨n, hn⟩ : ∃ n, bs.length / 16 = n + 1 := ⟨bs.length / 16 - 1, by omega⟩
  have hn' : (bs.drop 16).length / 16 = n := by simp only [List.length_drop]; omega
  simp only [blocks, hn, hn', List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, List.drop_drop]
  congr 3
  omega

theorem blocks_append_aux (ys : List Byte) (n : Nat) :
    ∀ xs : List Byte, xs.length = 16 * n → blocks (xs ++ ys) = blocks xs ++ blocks ys := by
  induction n with
  | zero => intro xs hx; rw [List.eq_nil_of_length_eq_zero hx]; rfl
  | succ n ih =>
    intro xs hx
    rw [blocks_cons (bs := xs ++ ys) (by simp; omega), blocks_cons (bs := xs) (by omega),
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      ih _ (by simp; omega), List.cons_append]

theorem blocks_append {xs ys : List Byte} (hx : xs.length % 16 = 0) :
    blocks (xs ++ ys) = blocks xs ++ blocks ys :=
  blocks_append_aux ys (xs.length / 16) xs (by omega)

theorem blocks_single {bs : List Byte} (h : bs.length = 16) : blocks bs = [ofBytes bs] := by
  rw [blocks_cons (by omega), List.take_of_length_le (by omega),
    blocks_of_lt (by simp; omega)]

theorem blocks_nil : blocks [] = [] := rfl

/-- The `n` blocks at `p` are the blocks of their bytes. -/
theorem blocksAt_eq (m : Mem) (p : Addr) (n : Nat) : blocksAt m p n = blocks (bytesAt m p (16 * n)) := by
  simp only [blocksAt, blocks, Cmac.bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [blockAt]
  congr 1
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro j h₁ h₂
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Absorbing a string a piece at a time -/

/-- The bytes of `x` in whole blocks. -/
abbrev whole (n : Nat) : Nat := 16 * (n / 16)

/-- GHASH, with the hash subkey `h`, has absorbed `x`: the accumulator at `y`
is `GHASH_H` of the whole blocks of `x`, and the rest of `x` (less than a
block) is the first bytes at `b`. -/
def Absorbed (m : Mem) (y b : Addr) (h : Block) (x : List Byte) : Prop :=
  blockAt m y = ghash h (blocks (x.take (whole x.length))) ∧
    bytesAt m b (x.length % 16) = x.drop (whole x.length)

theorem take_whole_append {x d : List Byte} (hx : x.length % 16 = 0) :
    (x ++ d).take (whole (x ++ d).length) = x ++ d.take (whole d.length) := by
  rw [List.take_append, List.take_of_length_le (by simp only [whole, List.length_append]; omega)]
  congr 2
  simp only [whole, List.length_append]; omega

theorem drop_whole_append {x d : List Byte} (hx : x.length % 16 = 0) :
    (x ++ d).drop (whole (x ++ d).length) = d.drop (whole d.length) := by
  rw [List.drop_append, List.drop_of_length_le (show x.length ≤ _ by
    simp only [whole, List.length_append]; omega), List.nil_append]
  congr 1
  simp only [whole, List.length_append]; omega

theorem whole_of_mod {n : Nat} (h : n % 16 = 0) : whole n = n := by simp only [whole]; omega

/-- Nothing absorbed: a zero accumulator. -/
theorem absorbed_nil {m : Mem} {y b : Addr} (h : Block) (hy : blockAt m y = 0) :
    Absorbed m y b h [] := ⟨hy, rfl⟩

/-- `Absorbed` only depends on the accumulator and the buffered bytes. -/
theorem Absorbed.congr {m m' : Mem} {y b : Addr} {h : Block} {x : List Byte} (hx : Absorbed m y b h x)
    (hy : blockAt m' y = blockAt m y) (hb : bytesAt m' b (x.length % 16) = bytesAt m b (x.length % 16)) :
    Absorbed m' y b h x := ⟨hy.trans hx.1, hb.trans hx.2⟩

/-- Whole blocks absorbed into the accumulator, after a whole number of
blocks. -/
theorem absorb_whole {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : Absorbed m y b h x)
    (hx0 : x.length % 16 = 0) (hd : d.length % 16 = 0)
    (hy : blockAt m' y = ghashFrom h (blockAt m y) (blocks d)) : Absorbed m' y b h (x ++ d) := by
  refine ⟨?_, ?_⟩
  · rw [hy, hx.1, take_whole_append hx0, whole_of_mod hd, List.take_of_length_le (Nat.le_refl _),
      List.take_of_length_le (by rw [whole_of_mod hx0]), blocks_append hx0]
    exact (ghashFrom_append _ _ _ _).symm
  · have hl : (x ++ d).length % 16 = 0 := by simp only [List.length_append]; omega
    rw [hl, List.drop_of_length_le (by rw [whole_of_mod hl])]; rfl

/-- The last bytes (less than a block) buffered, after a whole number of
blocks. -/
theorem absorb_tail {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : Absorbed m y b h x)
    (hx0 : x.length % 16 = 0) (hd : d.length < 16)
    (hy : blockAt m' y = blockAt m y) (hb : bytesAt m' b d.length = d) : Absorbed m' y b h (x ++ d) := by
  have hw : whole d.length = 0 := by simp only [whole]; rw [Nat.div_eq_of_lt hd]
  refine ⟨?_, ?_⟩
  · rw [hy, hx.1, take_whole_append hx0, hw, List.take_zero, List.append_nil,
      List.take_of_length_le (by rw [whole_of_mod hx0])]
  · rw [drop_whole_append hx0, hw, List.drop_zero, List.length_append, Nat.add_mod, hx0, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hd, hb]

/-- Filling the buffer, but not to a whole block. -/
theorem absorb_fill {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : Absorbed m y b h x)
    (hfit : x.length % 16 + d.length < 16) (hy : blockAt m' y = blockAt m y)
    (hb : bytesAt m' b (x.length % 16 + d.length) = bytesAt m b (x.length % 16) ++ d) :
    Absorbed m' y b h (x ++ d) := by
  have hl : (x ++ d).length / 16 = x.length / 16 := by simp only [List.length_append]; omega
  have hm : (x ++ d).length % 16 = x.length % 16 + d.length := by simp only [List.length_append]; omega
  have hw : whole (x ++ d).length = whole x.length := by simp only [whole, hl]
  have hle : whole x.length ≤ x.length := by simp only [whole]; omega
  refine ⟨?_, ?_⟩
  · rw [hy, hx.1, hw, List.take_append_of_le_length hle]
  · rw [hm, hb, hx.2, hw, List.drop_append_of_le_length hle]

/-- Filling the buffer to a whole block `B` (the buffered bytes, then `d`),
which is absorbed. -/
theorem absorb_complete {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : Absorbed m y b h x)
    (hfit : x.length % 16 + d.length = 16) {B : List Byte} (hB : B = x.drop (whole x.length) ++ d)
    (hy : blockAt m' y = ghashFrom h (blockAt m y) [ofBytes B]) : Absorbed m' y b h (x ++ d) := by
  have hle : whole x.length ≤ x.length := by simp only [whole]; omega
  have hl : (x ++ d).length % 16 = 0 := by simp only [List.length_append]; omega
  have hw : whole (x ++ d).length = whole x.length + 16 := by
    rw [whole_of_mod hl]; simp only [List.length_append, whole]; omega
  have hBl : B.length = 16 := by rw [hB]; simp only [List.length_append, List.length_drop, whole]; omega
  refine ⟨?_, ?_⟩
  · have hsplit : (x ++ d).take (whole (x ++ d).length) =
        x.take (whole x.length) ++ (x.drop (whole x.length) ++ d) := by
      rw [List.take_of_length_le (by rw [hw]; simp only [List.length_append, whole]; omega),
        ← List.append_assoc, List.take_append_drop]
    have hlen : (x.take (whole x.length)).length % 16 = 0 := by
      rw [List.length_take, Nat.min_eq_left hle]; simp only [whole]; omega
    rw [hy, hx.1, hsplit, blocks_append hlen, ← hB, blocks_single hBl]
    exact (ghashFrom_append _ _ _ _).symm
  · rw [hl, List.drop_of_length_le (by rw [hw]; simp only [List.length_append, whole]; omega)]
    rfl

theorem padLen_lt (n : Nat) : padLen n < 16 := by simp only [padLen]; omega

theorem length_zeros (n : Nat) : (zeros n).length = n := by simp [zeros]

/-- The buffer padded with zeros to a block `B`, which is absorbed: `x ‖ 0ᵘ`. -/
theorem absorb_pad {m m' : Mem} {y b : Addr} {h : Block} {x : List Byte} (hx : Absorbed m y b h x)
    (h0 : x.length % 16 ≠ 0) {B : List Byte}
    (hB : B = bytesAt m b (x.length % 16) ++ zeros (16 - x.length % 16))
    (hy : blockAt m' y = ghashFrom h (blockAt m y) [ofBytes B]) :
    Absorbed m' y b h (x ++ zeros (padLen x.length)) := by
  have hp : padLen x.length = 16 - x.length % 16 := by simp only [padLen]; omega
  refine absorb_complete hx (by rw [length_zeros, hp]; omega) ?_ hy
  rw [hB, hx.2, hp]

/-- With nothing buffered, there is no padding. -/
theorem padLen_of_mod {n : Nat} (h : n % 16 = 0) : padLen n = 0 := by simp only [padLen]; omega

end VG.Proof.Gcm
