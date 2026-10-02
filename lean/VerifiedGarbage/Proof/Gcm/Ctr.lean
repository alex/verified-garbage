import VerifiedGarbage.Proof.Gcm.Stream

/-!
# GCM: counter mode over a text given in pieces

Untrusted: everything here is checked by Lean. `GCTR_K(ICB, X)` XORs byte
`i` of the keystream `CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …` (`ksByte`) into byte `i`
of `X` (`gctr_eq`), so the text from byte `n` on is XORed with the keystream
from byte `n` on (`xorKs`). The state keeps the next counter block and,
within a block, the keystream block (`Ctr`); a piece of text is XORed with
the rest of that block (`ctr_head`), whole blocks with `vg_aes_ctr32`
(`ctr_whole`) and the last bytes with a new keystream block (`ctr_tail`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

/-- `Nat.repeat` composes. -/
theorem repeat_add (f : Block → Block) (a b : Nat) (x : Block) :
    Nat.repeat f (a + b) x = Nat.repeat f a (Nat.repeat f b x) := by
  induction a with
  | zero => simp [Nat.repeat]
  | succ a ih => rw [Nat.add_right_comm, Nat.repeat, ih]; rfl

/-- Byte `i` of the keystream from the counter block `icb`. -/
def ksByte (ciph : Block → Block) (icb : Block) (i : Nat) : Byte :=
  (toBytes (ciph (Nat.repeat inc32 (i / 16) icb))).getD (i % 16) 0

/-- `d` XORed with the keystream from byte `n` on. -/
def xorKs (ciph : Block → Block) (icb : Block) (n : Nat) (d : List Byte) : List Byte :=
  (List.range d.length).map fun i => d.getD i 0 ^^^ ksByte ciph icb (n + i)

theorem length_xorKs (ciph : Block → Block) (icb : Block) (n : Nat) (d : List Byte) :
    (xorKs ciph icb n d).length = d.length := by simp [xorKs]

theorem getD_xorKs (ciph : Block → Block) (icb : Block) (n : Nat) (d : List Byte) {i : Nat}
    (hi : i < d.length) : (xorKs ciph icb n d).getD i 0 = d.getD i 0 ^^^ ksByte ciph icb (n + i) := by
  simp [xorKs, List.getD_eq_getElem?_getD, hi]

theorem list_ext {x y : List Byte} (hl : x.length = y.length)
    (h : ∀ k < x.length, x.getD k 0 = y.getD k 0) : x = y := by
  apply List.ext_getElem hl
  intro k h₁ h₂
  have := h k h₁
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem xorKs_append (ciph : Block → Block) (icb : Block) (n : Nat) (d e : List Byte) :
    xorKs ciph icb n (d ++ e) = xorKs ciph icb n d ++ xorKs ciph icb (n + d.length) e := by
  simp only [xorKs, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
  · refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, Nat.add_assoc]

theorem xorKs_nil (ciph : Block → Block) (icb : Block) (n : Nat) : xorKs ciph icb n [] = [] := rfl

theorem getD_flatMap_toBytes (L : List Block) :
    ∀ i, i < 16 * L.length → (L.flatMap toBytes).getD i 0 = (toBytes (L.getD (i / 16) 0)).getD (i % 16) 0 := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons a L ih =>
    intro i hi
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD]
    by_cases h : i < 16
    · rw [List.getElem?_append_left (by rw [Cmac.toBytes_length]; exact h), ← List.getD_eq_getElem?_getD,
        Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rw [List.getElem?_append_right (by rw [Cmac.toBytes_length]; omega), Cmac.toBytes_length,
        ← List.getD_eq_getElem?_getD, ih (i - 16) (by simp at hi; omega)]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 16 := ⟨i - 16, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ (by decide), Nat.add_mod_right]
      rfl

theorem length_flatMap_toBytes (L : List Block) : (L.flatMap toBytes).length = 16 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, List.length_append, ih, Cmac.toBytes_length]; simp; omega

theorem getD_bytesAt' (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- A XOR with the bytes `L` is one with the keystream from byte `n` on. -/
theorem zipWith_eq_xorKs {ciph : Block → Block} {icb : Block} {n : Nat} {d L : List Byte}
    (hl : L.length = d.length) (h : ∀ k < d.length, L.getD k 0 = ksByte ciph icb (n + k)) :
    List.zipWith (· ^^^ ·) d L = xorKs ciph icb n d := by
  refine list_ext (by simp [length_xorKs, hl]) fun k hk => ?_
  simp only [List.length_zipWith, hl, Nat.min_self] at hk
  rw [getD_xorKs _ _ _ _ hk, ← h k hk]
  simp [List.getD_eq_getElem?_getD, hk, hl]

/-- `GCTR` XORs the keystream into the text. -/
theorem gctr_eq (ciph : Block → Block) (icb : Block) (x : List Byte) :
    gctr ciph icb x = xorKs ciph icb 0 x := by
  have hlen : ((keystream ciph icb ((x.length + 15) / 16)).flatMap toBytes).length =
      16 * ((x.length + 15) / 16) := by
    rw [length_flatMap_toBytes]; simp [keystream]
  refine list_ext (by simp [gctr, length_xorKs, hlen]; omega) fun i hi => ?_
  simp only [gctr, List.length_zipWith] at hi
  have hix : i < x.length := by omega
  rw [getD_xorKs _ _ _ _ hix, Nat.zero_add, gctr, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hix, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  congr 1
  · simp [List.getD_eq_getElem?_getD, hix]
  · have := getD_flatMap_toBytes (keystream ciph icb ((x.length + 15) / 16)) i
      (by simp [keystream]; omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [this, ksByte]
    congr 2
    simp [keystream, List.getD_eq_getElem?_getD, show i / 16 < (x.length + 15) / 16 by omega]

/-- `GCTR` of a text given in two pieces. -/
theorem gctr_append (ciph : Block → Block) (icb : Block) (p d : List Byte) :
    gctr ciph icb (p ++ d) = gctr ciph icb p ++ xorKs ciph icb p.length d := by
  rw [gctr_eq, gctr_eq, xorKs_append, Nat.zero_add]

theorem length_gctr (ciph : Block → Block) (icb : Block) (p : List Byte) :
    (gctr ciph icb p).length = p.length := by rw [gctr_eq, length_xorKs]

/-- `GCTR` twice is the identity. -/
theorem gctr_gctr (ciph : Block → Block) (icb : Block) (p : List Byte) :
    gctr ciph icb (gctr ciph icb p) = p := by
  rw [gctr_eq, gctr_eq]
  refine list_ext (by simp [length_xorKs]) fun k hk => ?_
  simp only [length_xorKs] at hk
  rw [getD_xorKs _ _ _ _ (by rw [length_xorKs]; exact hk), getD_xorKs _ _ _ _ hk, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

/-- One block of `GCTR`. -/
theorem gctr_block (ciph : Block → Block) (j s : Block) :
    gctr ciph j (toBytes s) = toBytes (s ^^^ ciph j) := by
  rw [gctr_eq]
  refine list_ext (by simp [length_xorKs, Cmac.toBytes_length]) fun k hk => ?_
  simp only [length_xorKs, Cmac.toBytes_length] at hk
  rw [getD_xorKs _ _ _ _ (by rw [Cmac.toBytes_length]; exact hk), Proof.Aes.toBytes_xor _ _ hk, ksByte,
    Nat.zero_add, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
  rfl

/-! ## The counter state -/

/-- The counter block at `cb` and the keystream block at `ks` after `n` bytes
of text: the next counter block, `inc₃₂^⌈n/16⌉(ICB)`, and, within a block,
that block's keystream. -/
def Ctr (m : Mem) (cb ks : Addr) (ciph : Block → Block) (icb : Block) (n : Nat) : Prop :=
  blockAt m cb = Nat.repeat inc32 ((n + 15) / 16) icb ∧
    (n % 16 ≠ 0 → blockAt m ks = ciph (Nat.repeat inc32 (n / 16) icb))

theorem Ctr.congr {m m' : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (hc : blockAt m' cb = blockAt m cb) (hk : blockAt m' ks = blockAt m ks) :
    Ctr m' cb ks ciph icb n := ⟨hc.trans h.1, fun h0 => hk.trans (h.2 h0)⟩

theorem ctr_zero (m : Mem) (cb ks : Addr) (ciph : Block → Block) {icb : Block}
    (h : blockAt m cb = icb) : Ctr m cb ks ciph icb 0 := ⟨h, fun h0 => absurd rfl h0⟩

theorem bytes_toBytes_blockAt (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    m (p + BitVec.ofNat 64 k) = (toBytes (blockAt m p)).getD k 0 := (Proof.Aes.toBytes_blockAt m p hk).symm

/-- Within a keystream block: the `k` bytes of text `d` XORed with the
keystream block's bytes from `n mod 16` on. -/
theorem ctr_head {m : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 ≠ 0) {d : List Byte} (hk : n % 16 + d.length ≤ 16) :
    List.zipWith (· ^^^ ·) d (bytesAt m (ks + BitVec.ofNat 64 (n % 16)) d.length) = xorKs ciph icb n d := by
  refine zipWith_eq_xorKs (Cmac.bytesAt_length _ _ _) fun k hk' => ?_
  rw [getD_bytesAt' _ _ hk', BitVec.add_assoc, ← BitVec.ofNat_add,
    bytes_toBytes_blockAt m ks (k := n % 16 + k) (by omega), h.2 h0, ksByte,
    show (n + k) / 16 = n / 16 by omega, show (n + k) % 16 = n % 16 + k by omega]

/-- Within a keystream block, the state is that for `n + k` bytes. -/
theorem Ctr.head {m : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n k : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 ≠ 0) (hk : n % 16 + k ≤ 16) : Ctr m cb ks ciph icb (n + k) := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [h.1]; congr 1; omega
  · rw [h.2 h0]; congr 2; omega

theorem length_blocksAt (m : Mem) (p : Addr) (n : Nat) : (blocksAt m p n).length = n := by
  simp [blocksAt]

theorem blocksAt_getD (m : Mem) (p : Addr) (n : Nat) {q : Nat} (hq : q < n) :
    (blocksAt m p n).getD q 0 = blockAt m (p + BitVec.ofNat 64 (16 * q)) := by
  simp [blocksAt, List.getD_eq_getElem?_getD, hq]

theorem ctr32_getD (ciph : Block → Block) (icb : Block) (xs : List Block) {q : Nat} (hq : q < xs.length) :
    (ctr32 ciph icb xs).getD q 0 = xs.getD q 0 ^^^ ciph (Nat.repeat inc32 q icb) := by
  simp [ctr32, keystream, List.getD_eq_getElem?_getD, hq]

/-- Whole blocks, from a whole number of blocks: `vg_aes_ctr32`. -/
theorem ctr_whole {m m' : Mem} {cb ks dp : Addr} {ciph : Block → Block} {icb : Block} {n nb : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hd : blocksAt m' dp nb = ctr32 ciph (blockAt m cb) (blocksAt m dp nb))
    (hc : blockAt m' cb = Nat.repeat inc32 nb (blockAt m cb)) :
    bytesAt m' dp (16 * nb) = xorKs ciph icb n (bytesAt m dp (16 * nb)) ∧ Ctr m' cb ks ciph icb (n + 16 * nb) := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun h1 => absurd (by omega) h1⟩
  · refine list_ext (by simp [length_xorKs, Cmac.bytesAt_length]) fun k hk => ?_
    simp only [Cmac.bytesAt_length] at hk
    rw [getD_xorKs _ _ _ _ (by rw [Cmac.bytesAt_length]; exact hk), getD_bytesAt' _ _ hk,
      getD_bytesAt' _ _ hk]
    have hq : k / 16 < nb := by omega
    have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [ctr32_getD _ _ _ (by rw [length_blocksAt]; exact hq), blocksAt_getD _ _ _ hq,
      blocksAt_getD _ _ _ hq] at e₁
    have ea : dp + BitVec.ofNat 64 k = dp + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [ea, bytes_toBytes_blockAt m' _ (by omega), bytes_toBytes_blockAt m _ (by omega), e₁,
      Proof.Aes.toBytes_xor _ _ (by omega), ksByte, hcb, ← repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega, show (n + k) % 16 = k % 16 by omega]
  · rw [hc, hcb, ← repeat_add]; congr 1; omega

/-- The last bytes, from a whole number of blocks: a keystream block from
`vg_aes_ctr32` (of the counter block on a zero block), XORed in. -/
theorem ctr_tail {m m₁ : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hk : blockAt m₁ ks = ciph (blockAt m cb)) (hc : blockAt m₁ cb = inc32 (blockAt m cb))
    {d : List Byte} (hd : d.length < 16) (hd0 : d.length ≠ 0) :
    List.zipWith (· ^^^ ·) d (bytesAt m₁ ks d.length) = xorKs ciph icb n d ∧ Ctr m₁ cb ks ciph icb (n + d.length) := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun _ => ?_⟩
  · refine zipWith_eq_xorKs (Cmac.bytesAt_length _ _ _) fun k hk' => ?_
    rw [getD_bytesAt' _ _ hk', bytes_toBytes_blockAt m₁ ks (k := k) (by omega), hk, hcb, ksByte,
      show (n + k) / 16 = n / 16 by omega, show (n + k) % 16 = k by omega]
  · rw [hc, hcb, show (n + d.length + 15) / 16 = n / 16 + 1 by omega]; rfl
  · rw [hk, hcb, show (n + d.length) / 16 = n / 16 by omega]

end VG.Proof.Gcm
