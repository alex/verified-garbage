import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming RC2-CBC: the contracts from memory facts

Untrusted: everything here is checked by Lean. Target-independent lemmas that
reduce the postconditions of `vg_rc2_cbc_init` and the update functions
(`Spec.Rc2.cbcInitContract`, `Spec.Rc2.cbcUpdateContract`) to facts about
the memory an implementation leaves, for implementations that

* `init`: check the lengths in order, and on success copy the IV to
  `ctx + 128` and expand the key into `ctx` (`init_post`, `init_post_error`);
* `update`: if there is no complete block (`out_len = 0`), append the data to
  the pending bytes (`update_post_short`); otherwise copy the pending bytes
  and the first `out_len - pending_len` bytes of data to `out`, the rest of
  the data to `ctx + 136`, and run CBC on `out` in place, with the schedule
  at `ctx` and the chaining value at `ctx + 128` (`update_post_long`).
-/

namespace VG.Proof.Rc2

open VG

theorem getD_of_lt {α : Type} (l : List α) {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rc2.bytesAt m p (a + b) = Spec.Rc2.bytesAt m p a ++ Spec.Rc2.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rc2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Rc2.bytesAt m p (i + 1) = Spec.Rc2.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Rc2.bytesAt, List.range_succ]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hn : n ≤ 2 ^ 64) (hd : ∀ r ∈ rs, (Region.mk p n).Disjoint r) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  simp only [Spec.Rc2.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd hn (List.mem_range.mp hi)

/-- Bytes written with `writeBytes` read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, WriteBytes.writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₂, ite_true]
    rw [getD_of_lt _ _ h₂]

theorem bytesAt_eight (m : Mem) (p : Addr) :
    Spec.Rc2.bytesAt m p 8 = (Spec.Rc2.blockAt m p).toList := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rc2.bytesAt, Spec.Rc2.blockAt, List.getElem_map, List.getElem_range,
      Vector.getElem_toList, Vector.getElem_ofFn]

theorem flatMap_blocksAt (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Rc2.blocksAt m p n).flatMap Vector.toList = Spec.Rc2.bytesAt m p (8 * n) := by
  induction n generalizing p with
  | zero => simp [Spec.Rc2.blocksAt, Spec.Rc2.bytesAt]
  | succ n ih =>
    rw [blocksAt_cons, List.flatMap_cons, ih, show 8 * (n + 1) = 8 + 8 * n by omega, bytesAt_add,
      bytesAt_eight]
    rfl

theorem blocks_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rc2.blocks (Spec.Rc2.bytesAt m p (8 * n)) = Spec.Rc2.blocksAt m p n := by
  simp only [Spec.Rc2.blocks, Spec.Rc2.blocksAt, bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Spec.Rc2.blockAt, Spec.Rc2.bytesAt]
  rw [getD_of_lt _ _ (by simp; omega), List.getElem_map, List.getElem_range, Offset.add_add]

/-- Only whole blocks: the blocks of `xs` are those of its first `8 ⌊|xs| / 8⌋` bytes. -/
theorem blocks_take (xs : List Byte) :
    Spec.Rc2.blocks xs = Spec.Rc2.blocks (xs.take (8 * (xs.length / 8))) := by
  have hl : (xs.take (8 * (xs.length / 8))).length = 8 * (xs.length / 8) := by
    simp only [List.length_take]; omega
  simp only [Spec.Rc2.blocks, hl, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  rw [getD_of_lt _ _ (by omega), getD_of_lt _ _ (by omega), List.getElem_take]

/-! ## `update` -/

/-- With no complete block, the data is appended to the pending bytes, and
the schedule and chaining value are unchanged. -/
theorem update_post_short {m m' : Mem} {ctx data out : Addr} {d : Spec.Rc2.Direction} {p len : Nat}
    (hshort : p + len < 8)
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.scheduleAt m ctx)
    (hiv : Spec.Rc2.blockAt m' (ctx + 128) = Spec.Rc2.blockAt m (ctx + 128))
    (hpend : Spec.Rc2.bytesAt m' (ctx + 136) (p + len) =
      Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len) :
    let result := Spec.Rc2.update (Spec.Rc2.contextAt m ctx d p) (Spec.Rc2.bytesAt m data len)
    Spec.Rc2.contextAt m' ctx d ((p + len) % 8) = result.1 ∧
      Spec.Rc2.bytesAt m' out ((p + len) / 8 * 8) = result.2 := by
  have hlen : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).length / 8 = 0 := by
    simp only [List.length_append, bytesAt_length]; omega
  have hb : Spec.Rc2.blocks (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len) = [] := by
    simp only [Spec.Rc2.blocks, hlen, List.range_zero, List.map_nil]
  simp only [Spec.Rc2.update, Spec.Rc2.contextAt, hb, Spec.Rc2.cbc, hlen, Nat.mul_zero, List.drop_zero,
    List.flatMap_nil, Nat.mod_eq_of_lt hshort, Nat.div_eq_of_lt hshort, Nat.zero_mul, hs, hiv, hpend]
  simp [Spec.Rc2.bytesAt]

/-- With complete blocks, from the memory `m₁` after the copies (the pending
bytes and the first `out_len - p` bytes of data at `out`, the rest of the
data at `ctx + 136`) and the memory `m'` after CBC on `out`. -/
theorem update_post_long {m m₁ m' : Mem} {ctx data out : Addr} {d : Spec.Rc2.Direction} {p len : Nat}
    (hp : p < 8) (hlong : 8 ≤ p + len)
    (hout : Spec.Rc2.bytesAt m₁ out ((p + len) / 8 * 8) =
      Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data ((p + len) / 8 * 8 - p))
    (hs₁ : Spec.Rc2.scheduleAt m₁ ctx = Spec.Rc2.scheduleAt m ctx)
    (hiv₁ : Spec.Rc2.blockAt m₁ (ctx + 128) = Spec.Rc2.blockAt m (ctx + 128))
    (hpend : Spec.Rc2.bytesAt m' (ctx + 136) ((p + len) % 8) =
      Spec.Rc2.bytesAt m (data + BitVec.ofNat 64 ((p + len) / 8 * 8 - p)) ((p + len) % 8))
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.scheduleAt m₁ ctx)
    (hc₁ : Spec.Rc2.blocksAt m' out ((p + len) / 8) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m₁ ctx) d
      (Spec.Rc2.blockAt m₁ (ctx + 128)) (Spec.Rc2.blocksAt m₁ out ((p + len) / 8))).1)
    (hc₂ : Spec.Rc2.blockAt m' (ctx + 128) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m₁ ctx) d
      (Spec.Rc2.blockAt m₁ (ctx + 128)) (Spec.Rc2.blocksAt m₁ out ((p + len) / 8))).2) :
    let result := Spec.Rc2.update (Spec.Rc2.contextAt m ctx d p) (Spec.Rc2.bytesAt m data len)
    Spec.Rc2.contextAt m' ctx d ((p + len) % 8) = result.1 ∧
      Spec.Rc2.bytesAt m' out ((p + len) / 8 * 8) = result.2 := by
  have hO : (p + len) / 8 * 8 = 8 * ((p + len) / 8) := Nat.mul_comm _ _
  have hk : (p + len) / 8 * 8 - p + (p + len) % 8 = len := by omega
  have hsplit : Spec.Rc2.bytesAt m data len = Spec.Rc2.bytesAt m data ((p + len) / 8 * 8 - p) ++
      Spec.Rc2.bytesAt m (data + BitVec.ofNat 64 ((p + len) / 8 * 8 - p)) ((p + len) % 8) := by
    rw [← bytesAt_add, hk]
  have hl : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).length = p + len := by
    simp [bytesAt_length]
  have htake : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).take
      (8 * ((p + len) / 8)) = Spec.Rc2.bytesAt m₁ out (8 * ((p + len) / 8)) := by
    rw [← hO, hout, hsplit, ← List.append_assoc, List.take_left' (by simp [bytesAt_length]; omega)]
  have hdrop : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).drop
      (8 * ((p + len) / 8)) = Spec.Rc2.bytesAt m' (ctx + 136) ((p + len) % 8) := by
    rw [hpend, hsplit, ← List.append_assoc, List.drop_left' (by simp [bytesAt_length]; omega)]
  have hblocks : Spec.Rc2.blocks (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len) =
      Spec.Rc2.blocksAt m₁ out ((p + len) / 8) := by
    rw [blocks_take, hl, htake, blocks_bytesAt]
  simp only [Spec.Rc2.update, Spec.Rc2.contextAt, hl, hblocks, hdrop, ← hs₁, ← hiv₁]
  refine ⟨?_, ?_⟩
  · rw [hs, ← hc₂]
  · rw [← hc₁, flatMap_blocksAt, hO]

/-! ## `init` -/

/-- The context `init` writes, from the schedule at `ctx` and the IV at
`ctx + 128`. -/
theorem init_post {m m' : Mem} {key iv ctx : Addr} {keyLen effectiveBits ivLen : Nat} {r : BitVec 32}
    (hk : 1 ≤ keyLen ∧ keyLen ≤ 128) (he : 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) (hi : ivLen = 8)
    (hr : r = 0)
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.expandKey (Spec.Rc2.bytesAt m key keyLen) effectiveBits)
    (hiv : Spec.Rc2.blockAt m' (ctx + 128) = Spec.Rc2.blockAt m iv) :
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen)
        (Spec.Rc2.bytesAt m iv ivLen) direction effectiveBits with
      | .ok c => r = 0 ∧ Spec.Rc2.contextAt m' ctx direction 0 = c
      | .error e => r.toNat = e.code := by
  intro direction
  subst hi
  have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv 8)
      direction effectiveBits = .ok (Spec.Rc2.Context.mk (Spec.Rc2.expandKey (Spec.Rc2.bytesAt m key keyLen)
        effectiveBits) direction (Vector.ofFn fun i => (Spec.Rc2.bytesAt m iv 8).getD i 0) []) := by
    simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk),
      ite_eq_left_of_eq_true _ _ (eq_true he)]
    rfl
  rw [hc]
  refine ⟨hr, ?_⟩
  simp only [Spec.Rc2.contextAt, hs, hiv, Spec.Rc2.Context.mk.injEq, true_and]
  refine ⟨?_, by simp [Spec.Rc2.bytesAt]⟩
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, Vector.getElem_ofFn, Spec.Rc2.bytesAt]
  rw [getD_of_lt _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- The error `init` returns for invalid lengths, in order. -/
theorem init_post_error {m m' : Mem} {key iv ctx : Addr} {keyLen effectiveBits ivLen : Nat} {r : BitVec 32}
    (hr : r.toNat = if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1
      else if ¬(1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) then 2 else 3)
    (hbad : ¬((1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) ∧ ivLen = 8)) :
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen)
        (Spec.Rc2.bytesAt m iv ivLen) direction effectiveBits with
      | .ok c => r = 0 ∧ Spec.Rc2.contextAt m' ctx direction 0 = c
      | .error e => r.toNat = e.code := by
  intro direction
  by_cases hk : 1 ≤ keyLen ∧ keyLen ≤ 128
  · by_cases he : 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024
    · have hi : ivLen ≠ 8 := fun h => hbad ⟨hk, he, h⟩
      have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
          direction effectiveBits = .error .invalidIvLength := by
        simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_left_of_eq_true _ _ (eq_true he), ite_eq_right_of_eq_false _ _ (eq_false hi)]
        rfl
      rw [hc]; simpa [hk, he, Spec.Rc2.Error.code] using hr
    · have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
          direction effectiveBits = .error .invalidEffectiveBits := by
        simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_right_of_eq_false _ _ (eq_false he)]
        rfl
      rw [hc]; simpa [hk, he, Spec.Rc2.Error.code] using hr
  · have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
        direction effectiveBits = .error .invalidKeyLength := by
      simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_right_of_eq_false _ _ (eq_false hk)]
      rfl
    rw [hc]; simpa [hk, Spec.Rc2.Error.code] using hr

end VG.Proof.Rc2
