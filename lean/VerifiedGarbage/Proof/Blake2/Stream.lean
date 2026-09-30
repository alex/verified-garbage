import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Streaming BLAKE2: target-independent lemmas

Untrusted: everything here is checked by Lean. The streaming code keeps `r`
bytes of the data `d` in the buffer (`ReprR`): `Repr` is `ReprR` with `r =
bufLen w |d|` (the last 1 to `bb` bytes), and within `update` the buffer may
also be full or empty. Each step of the code is one lemma here: copying
bytes into the buffer (`reprR_append`), compressing the full buffer
(`reprR_flush`), compressing blocks straight from the data (`reprR_blocks`),
and the final compression (`finalHash_eq`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

section
variable {w : Nat}

/-- The number of bytes a streaming state with a byte count of `n` holds in
its buffer: the last `1` to `bb`, none if `n = 0`. -/
def bufLen (w n : Nat) : Nat := if n = 0 then 0 else (n - 1) % blockBytes w + 1

/-- Where the buffer starts in the streaming state. -/
abbrev bufOff (w : Nat) : Nat := 8 * (w / 8)

variable (P : Params w)

/-- The streaming state at `p` holds the last `r ≤ bb` bytes of the data `d`
in its buffer, and its hash state is `h0` updated with every block before
them. -/
def ReprR (h0 : HashValue w) (mem : Mem) (p : Addr) (d : List Byte) (r : Nat) : Prop :=
  r ≤ blockBytes w ∧ r ≤ d.length ∧ (d.length - r) % blockBytes w = 0 ∧
  stateAt w mem p = compressList P h0 d ((d.length - r) / blockBytes w) ∧
  bytesAt mem (p + BitVec.ofNat 64 (bufOff w)) r = d.drop (d.length - r)

/-! ## Lists and blocks -/

theorem leBytes_congr {n : Nat} {f g : Nat → Byte} (h : ∀ i < n, f i = g i) :
    leBytes n f = leBytes n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [leBytes]
    rw [ih fun i hi => h (i + 1) (by omega), h 0 (by omega)]

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < blockBytes w, f k = g k) :
    parseBlock (w := w) f = parseBlock g := by
  funext j
  simp only [parseBlock, leWord]
  congr 1
  apply leBytes_congr
  intro i hi
  apply h
  have : w / 8 * j.1 ≤ w / 8 * 15 := Nat.mul_le_mul_left _ (by omega)
  simp only [blockBytes]; omega

theorem getD_append_left {d x : List Byte} {i : Nat} (h : i < d.length) :
    (d ++ x).getD i 0 = d.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {d x : List Byte} {i : Nat} (h : d.length ≤ i) :
    (d ++ x).getD i 0 = x.getD (i - d.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem F_congr {h : HashValue w} {b b' : Block w} {t t' : Nat} {f : Bool} (hb : b = b')
    (ht : t = t') : F P h b t f = F P h b' t' f := by subst hb ht; rfl

theorem compressList_succ (h : HashValue w) (d : List Byte) (n : Nat) :
    compressList P h d (n + 1) =
      F P (compressList P h d n) (parseBlock fun k => d.getD (blockBytes w * n + k) 0)
        ((n + 1) * blockBytes w) false := by
  simp only [compressList, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `compressList` reads only the first `bb · n` bytes. -/
theorem compressList_congr (h : HashValue w) {d d' : List Byte} {n : Nat}
    (hd : ∀ i < blockBytes w * n, d.getD i 0 = d'.getD i 0) :
    compressList P h d n = compressList P h d' n := by
  induction n with
  | zero => simp only [compressList, List.range_zero, List.foldl_nil]
  | succ n ih =>
    rw [compressList_succ, compressList_succ, ih fun i hi => hd i (by rw [Nat.mul_succ]; omega)]
    exact congrArg (fun b => F P _ b _ false)
      (parseBlock_congr fun k hk => hd _ (by rw [Nat.mul_succ]; omega))

theorem compressList_append (h : HashValue w) {d : List Byte} (x : List Byte) {n : Nat}
    (hn : blockBytes w * n ≤ d.length) :
    compressList P h (d ++ x) n = compressList P h d n :=
  compressList_congr P h fun _ hi => getD_append_left (by omega)

/-! ## The number of bytes in the buffer -/

theorem bufLen_le (hbb : 0 < blockBytes w) (n : Nat) : bufLen w n ≤ blockBytes w := by
  unfold bufLen; split
  · omega
  · have := Nat.mod_lt (n - 1) hbb; omega

theorem bufLen_le_self (n : Nat) : bufLen w n ≤ n := by
  unfold bufLen; split
  · omega
  · have := Nat.mod_le (n - 1) (blockBytes w); omega

/-- The data before the buffer is `bb · compressed w d` bytes. -/
theorem sub_bufLen (d : List Byte) :
    d.length - bufLen w d.length = blockBytes w * compressed w d := by
  unfold bufLen compressed; split
  · simp [*]
  · have := Nat.div_add_mod (d.length - 1) (blockBytes w); omega

theorem bufLen_pos {n : Nat} (h : n ≠ 0) : 1 ≤ bufLen w n := by
  unfold bufLen; simp [h]

theorem repr_iff (hbb : 0 < blockBytes w) (h0 : HashValue w) (mem : Mem) (p : Addr) (d : List Byte) :
    VG.Spec.Blake2.Repr P h0 mem p d ↔ ReprR P h0 mem p d (bufLen w d.length) := by
  have e := sub_bufLen (w := w) d
  have e' : (d.length - bufLen w d.length) / blockBytes w = compressed w d := by
    rw [e, Nat.mul_div_cancel_left _ hbb]
  have e'' : d.length - blockBytes w * compressed w d = bufLen w d.length := by
    have := bufLen_le_self (w := w) d.length; omega
  unfold Spec.Blake2.Repr ReprR
  rw [e', e, e'', Nat.mul_mod_right]
  exact ⟨fun ⟨a, b⟩ => ⟨bufLen_le hbb _, bufLen_le_self _, rfl, a, b⟩, fun ⟨_, _, _, a, b⟩ => ⟨a, b⟩⟩

/-- A state holding at least one byte in its buffer is the streaming state of
its data. -/
theorem repr_of_reprR (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem : Mem} {p : Addr}
    {d : List Byte} {r : Nat} (h : ReprR P h0 mem p d r) (hr : 1 ≤ r) :
    Spec.Blake2.Repr P h0 mem p d := by
  have e : bufLen w d.length = r := by
    obtain ⟨h1, h2, h3, -⟩ := h
    have hq := Nat.div_add_mod (d.length - r) (blockBytes w)
    rw [h3, Nat.add_zero] at hq
    have hd : d.length ≠ 0 := by omega
    simp only [bufLen, hd, ite_false]
    rw [show d.length - 1 = (r - 1) + blockBytes w * ((d.length - r) / blockBytes w) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [repr_iff P hbb, e]; exact h

/-! ## The steps of `update` -/

/-- Appending `x` to the buffer, if it fits, with the hash state unchanged. -/
theorem reprR_append {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d x : List Byte} {r : Nat}
    (h : ReprR P h0 mem p d r) (hx : r + x.length ≤ blockBytes w)
    (hs : stateAt w mem' p = stateAt w mem p)
    (hb : bytesAt mem' (p + BitVec.ofNat 64 (bufOff w)) (r + x.length) =
      bytesAt mem (p + BitVec.ofNat 64 (bufOff w)) r ++ x) :
    ReprR P h0 mem' p (d ++ x) (r + x.length) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : (d ++ x).length - (r + x.length) = d.length - r := by simp; omega
  have hq : blockBytes w * ((d.length - r) / blockBytes w) ≤ d.length :=
    Nat.le_trans (Nat.mul_div_le _ _) (by omega)
  refine ⟨hx, by simp; omega, by rw [e]; exact h3, ?_, ?_⟩
  · rw [e, hs, h4, compressList_append P h0 x hq]
  · rw [e, hb, h5, List.drop_append_of_le_length (by omega)]

/-- Compressing the full buffer, which is not the last block: its counter is
`|d|`. -/
theorem reprR_flush (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem mem' : Mem} {p : Addr}
    {d : List Byte} (h : ReprR P h0 mem p d (blockBytes w))
    (hs : stateAt w mem' p =
      F P (stateAt w mem p) (blockAt w mem (p + BitVec.ofNat 64 (bufOff w))) d.length false) :
    ReprR P h0 mem' p d 0 := by
  obtain ⟨_, h2, h3, h4, h5⟩ := h
  have hq := Nat.div_add_mod (d.length - blockBytes w) (blockBytes w)
  rw [h3] at hq
  generalize hqd : (d.length - blockBytes w) / blockBytes w = q at hq h4
  have hd0 : d.length / blockBytes w = q + 1 := by
    rw [show d.length = blockBytes w * (q + 1) by rw [Nat.mul_succ]; omega,
      Nat.mul_div_cancel_left _ hbb]
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, by simp [bytesAt]⟩
  · rw [Nat.sub_zero, show d.length = blockBytes w * (q + 1) by rw [Nat.mul_succ]; omega,
      Nat.mul_mod_right]
  · rw [Nat.sub_zero, hd0, compressList_succ, hs, h4]
    refine F_congr P ?_ ?_
    · apply parseBlock_congr
      intro k hk
      have := congrArg (fun l => l.getD k 0) h5
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some, List.getElem?_drop] at this
      rw [this, show d.length - blockBytes w + k = blockBytes w * q + k by omega]
      simp [List.getD_eq_getElem?_getD]
    · rw [Nat.succ_mul, Nat.mul_comm q]; omega

theorem bytesAt_getD (mem : Mem) (q : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt mem q n).getD i 0 = mem (q + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- The blocks after `bb · n` bytes of data `d` are those at `q`. -/
theorem compressList_bytes (h : HashValue w) {d : List Byte} {n : Nat}
    (hd : d.length = blockBytes w * n) (mem : Mem) (q : Addr) {K k : Nat} (hk : k ≤ K) :
    compressList P h (d ++ bytesAt mem q (blockBytes w * K)) (n + k) =
      compressBlocks P (compressList P h d n) mem q k (d.length + blockBytes w) false := by
  induction k with
  | zero => rw [Nat.add_zero, compressList_append P h _ (by omega), compressBlocks_zero]
  | succ k ih =>
    rw [← Nat.add_assoc, compressList_succ, compressBlocks_succ, ih (by omega)]
    refine F_congr P ?_ ?_
    · apply parseBlock_congr
      intro j hj
      have hkK : blockBytes w * k + j < blockBytes w * K := by
        have h1 : blockBytes w * (k + 1) ≤ blockBytes w * K := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at h1; omega
      rw [getD_append_right (by rw [hd, Nat.mul_add]; omega),
        show blockBytes w * (n + k) + j - d.length = blockBytes w * k + j by rw [hd, Nat.mul_add]; omega,
        bytesAt_getD _ _ hkK, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [hd, Nat.mul_comm (blockBytes w) n, Nat.succ_mul, Nat.add_mul]; omega

/-- Compressing `k` whole blocks straight from the data (at `q`), with an
empty buffer: the first one's counter is `|d| + bb`. -/
theorem reprR_blocks (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem mem' : Mem} {p q : Addr}
    {d : List Byte} {k : Nat} (h : ReprR P h0 mem p d 0)
    (hs : stateAt w mem' p =
      compressBlocks P (stateAt w mem p) mem q k (d.length + blockBytes w) false) :
    ReprR P h0 mem' p (d ++ bytesAt mem q (blockBytes w * k)) 0 := by
  obtain ⟨_, _, h3, h4, _⟩ := h
  rw [Nat.sub_zero] at h3 h4
  have hn := Nat.div_add_mod d.length (blockBytes w)
  rw [h3, Nat.add_zero] at hn
  have hl : (d ++ bytesAt mem q (blockBytes w * k)).length = blockBytes w * (d.length / blockBytes w + k) := by
    simp only [List.length_append, bytesAt, List.length_map, List.length_range, Nat.mul_add]; omega
  refine ⟨Nat.zero_le _, Nat.zero_le _, by rw [Nat.sub_zero, hl, Nat.mul_mod_right], ?_,
    by simp [bytesAt]⟩
  rw [Nat.sub_zero, hl, Nat.mul_div_cancel_left _ hbb, hs, h4,
    compressList_bytes P h0 hn.symm mem q (Nat.le_refl k)]

theorem compressList_zero (h : HashValue w) (d : List Byte) : compressList P h d 0 = h := by
  simp only [compressList, List.range_zero, List.foldl_nil]

/-! ## `init` -/

theorem padZeros_eq {key : List Byte} (h0 : key.length ≠ 0) (h : key.length ≤ blockBytes w) :
    padZeros w key = key ++ List.replicate (blockBytes w - key.length) 0 := by
  unfold padZeros
  congr 2
  by_cases e : key.length = blockBytes w
  · rw [e, Nat.mod_self, Nat.sub_zero, Nat.mod_self, Nat.sub_self]
  · rw [Nat.mod_eq_of_lt (show key.length < blockBytes w by omega),
      Nat.mod_eq_of_lt (show blockBytes w - key.length < blockBytes w by omega)]

/-- The state `init` writes: the initial hash value and, for a key, the key
padded with zeros in the buffer. -/
theorem repr_keyBlock (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem : Mem} {p : Addr}
    {key : List Byte} (hk : key.length ≤ blockBytes w) (hs : stateAt w mem p = h0)
    (hb : key.length ≠ 0 → bytesAt mem (p + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
      key ++ List.replicate (blockBytes w - key.length) 0) :
    Spec.Blake2.Repr P h0 mem p (keyBlock w key) := by
  rw [repr_iff P hbb]
  unfold keyBlock
  split
  · simp only [List.length_nil, show bufLen w 0 = 0 from rfl]
    exact ⟨Nat.zero_le _, Nat.le_refl _, Nat.zero_mod _, by
      rw [List.length_nil, Nat.zero_div, compressList_zero, hs], by simp [bytesAt]⟩
  · rename_i h0'
    rw [padZeros_eq h0' hk]
    have hl : (key ++ List.replicate (blockBytes w - key.length) 0).length = blockBytes w := by
      simp; omega
    have hbl : bufLen w (blockBytes w) = blockBytes w := by
      simp only [bufLen, Nat.ne_of_gt hbb, ite_false, Nat.mod_eq_of_lt (show blockBytes w - 1 < blockBytes w by omega)]
      omega
    rw [hl, hbl]
    refine ⟨Nat.le_refl _, by rw [hl], by rw [hl, Nat.sub_self, Nat.zero_mod], ?_, ?_⟩ <;>
      rw [hl, Nat.sub_self]
    exacts [
      by rw [Nat.zero_div, compressList_zero, hs], by rw [List.drop_zero, hb h0']]

/-! ## `finalize` -/

/-- The last block, padded with zeros, compressed with the final block flag
and the counter `|d|`, gives the final hash. -/
theorem final_eq (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem mem' : Mem} {p : Addr}
    {d : List Byte} (h : Spec.Blake2.Repr P h0 mem p d) (hs : stateAt w mem' p = stateAt w mem p)
    (hb : bytesAt mem' (p + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
      bytesAt mem (p + BitVec.ofNat 64 (bufOff w)) (bufLen w d.length) ++
        List.replicate (blockBytes w - bufLen w d.length) 0) :
    (F P (stateAt w mem' p) (blockAt w mem' (p + BitVec.ofNat 64 (bufOff w))) d.length true).toList.flatMap
      wordBytes = finalHash P h0 d := by
  obtain ⟨-, -, -, h4, h5⟩ := (repr_iff P hbb h0 mem p d).mp h
  have e := sub_bufLen (w := w) d
  have hr := bufLen_le hbb d.length
  have e' : (d.length - bufLen w d.length) / blockBytes w = compressed w d := by
    rw [e, Nat.mul_div_cancel_left _ hbb]
  rw [e'] at h4
  rw [e] at h5
  have e2 : d.length - blockBytes w * compressed w d = bufLen w d.length := by
    have := bufLen_le_self (w := w) d.length; omega
  unfold finalHash
  rw [hs, h4]
  refine congrArg (fun h : HashValue w => h.toList.flatMap wordBytes) (F_congr P ?_ rfl)
  apply parseBlock_congr
  intro k hk
  have := congrArg (fun l => l.getD k 0) hb
  simp only [bytesAt_getD _ _ hk] at this
  rw [this, h5]
  by_cases hkr : k < bufLen w d.length
  · rw [getD_append_left (by simp only [List.length_drop, e2]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  · rw [getD_append_right (by simp only [List.length_drop, e2]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    rw [List.getElem?_eq_none (by omega)]
    split <;> rfl

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr}
    (h : ∀ i < bufOff w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    stateAt w mem' p = stateAt w mem p := by
  simp only [stateAt]
  congr 1; funext j
  apply Mem.readW_congr
  intro i hi
  have : w / 8 * j.1 ≤ w / 8 * 7 := Nat.mul_le_mul_left _ (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by simp only [bufOff]; omega)

theorem blockAt_congr {mem mem' : Mem} {p : Addr}
    (h : ∀ k < blockBytes w, mem' (p + BitVec.ofNat 64 k) = mem (p + BitVec.ofNat 64 k)) :
    blockAt w mem' p = blockAt w mem p :=
  parseBlock_congr h

theorem compressBlocks_congr {h : HashValue w} {m m' : Mem} {p : Addr} {n t : Nat} {f : Bool}
    (hm : ∀ j < blockBytes w * n, m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j)) :
    compressBlocks P h m' p n t f = compressBlocks P h m p n t f := by
  induction n with
  | zero => rw [compressBlocks_zero, compressBlocks_zero]
  | succ n ih =>
    rw [compressBlocks_succ, compressBlocks_succ,
      ih fun j hj => hm j (by rw [Nat.mul_succ]; omega)]
    refine F_congr P (blockAt_congr fun k hk => ?_) rfl
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm _ (by rw [Nat.mul_succ]; omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    bytesAt mem' p n = bytesAt mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-! ## Bytes and words -/

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem wordBytes_readW (m : Mem) (a : Addr) (hw : w = 32 ∨ w = 64) :
    wordBytes (m.readW a w) = bytesAt m a (w / 8) := by
  apply List.ext_getElem (by simp [wordBytes, bytesAt])
  intro i h1 _
  simp only [wordBytes, List.length_map, List.length_range] at h1
  simp only [wordBytes, bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a h1]
  rcases hw with rfl | rfl <;> rfl

theorem bytesAt_words (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (w / 8 * n) =
      (List.range n).flatMap fun j => bytesAt m (p + BitVec.ofNat 64 (w / 8 * j)) (w / 8) := by
  induction n with
  | zero => simp [bytesAt]
  | succ n ih => rw [Nat.mul_succ, bytesAt_add, ih, List.range_succ, List.flatMap_append]; simp

/-- The bytes of a stored state. -/
theorem bytesAt_state (m : Mem) (p : Addr) (hw : w = 32 ∨ w = 64) :
    bytesAt m p (bufOff w) = (stateAt w m p).toList.flatMap wordBytes := by
  rw [bufOff, Nat.mul_comm, bytesAt_words, stateAt, Vector.toList_ofFn, List.flatMap,
    List.flatMap, List.map_ofFn, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, Function.comp_apply,
    Fin.val_succ, Fin.val_zero, Nat.reduceAdd, wordBytes_readW m _ hw]

end

end VG.Proof.Blake2
