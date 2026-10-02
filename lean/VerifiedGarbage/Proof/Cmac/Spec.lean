import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.Aes.Blocks

/-!
# CMAC: lemmas about the specification

* `macFull_split`: the MAC of a message of whole blocks followed by its last
  bytes `Mₙ*` (at most a block, and some unless the message is empty) is the
  cipher of the chaining value of the whole blocks XORed with `Mₙ` (§6.2
  steps 3–6), which is how `update` and `finalize` compute it.
* `ctr32_one`: counter mode on one zero block is the cipher of the counter
  block, which is how the implementations call `vg_aes_ctr32`: as bytes,
  `Spec.Gcm.toBytes (aesWith nr w (Spec.Gcm.ofBytes x)) = Cmac.aesWith nr w x`.
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

/-! ## Lists of bytes -/

theorem length_xor (x y : List Byte) : (Spec.Cmac.xor x y).length = min x.length y.length := by
  simp [Spec.Cmac.xor]

theorem length_zeros (n : Nat) : (zeros n).length = n := by simp [zeros]

theorem getD_xor {x y : List Byte} (h : x.length = y.length) {k : Nat} (hk : k < x.length) :
    (Spec.Cmac.xor x y).getD k 0 = x.getD k 0 ^^^ y.getD k 0 := by
  simp only [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show k < y.length by omega)]
  rfl

/-- Lists of 16 bytes are equal if their bytes are. -/
theorem ext16 {x y : List Byte} (hx : x.length = 16) (hy : y.length = 16)
    (h : ∀ k < 16, x.getD k 0 = y.getD k 0) : x = y := by
  apply List.ext_getElem (by rw [hx, hy])
  intro k h₁ h₂
  have := h k (by omega)
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

/-! ## Splitting the MAC -/

theorem chain_append (ciph : Cipher) (c : List Byte) (xs ys : List (List Byte)) :
    chain ciph c (xs ++ ys) = chain ciph (chain ciph c xs) ys := by
  simp [chain, List.foldl_append]

theorem chain_single (ciph : Cipher) (c m : List Byte) : chain ciph c [m] = ciph (xor c m) := rfl

theorem blocks_eq {msg : List Byte} (hm : msg.length % 16 = 0) (last : List Byte) (q : Nat)
    (hq : msg.length = 16 * q) :
    (List.range q).map (fun i => ((msg ++ last).drop (16 * i)).take 16) = blocks 16 msg := by
  simp only [blocks, hq, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- §6.2 steps 3–6, for a message of whole blocks `msg` followed by `last`. -/
theorem macFull_split (ciph : Cipher) {msg last : List Byte} (hm : msg.length % 16 = 0)
    (hl : last.length ≤ 16) (hne : msg = [] ∨ 0 < last.length) :
    macFull ciph 16 (msg ++ last) =
      ciph (xor (chain ciph (zeros 16) (blocks 16 msg))
        (lastBlock 16 (subkeys ciph 16).1 (subkeys ciph 16).2 last)) := by
  obtain ⟨q, hq⟩ : ∃ q, msg.length = 16 * q := ⟨msg.length / 16, by omega⟩
  have hn : (if (msg ++ last).length = 0 then 1 else ((msg ++ last).length + 16 - 1) / 16) = q + 1 := by
    rw [List.length_append]
    split
    · omega
    · have hl0 : 0 < last.length := by
        rcases hne with h | h
        · subst h; simp only [List.length_nil] at *; omega
        · exact h
      omega
  simp only [macFull, hn, Nat.add_sub_cancel]
  rw [blocks_eq hm last q hq, chain_append, chain_single,
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

/-! ## One block of counter mode -/

theorem toBytes_length (x : Spec.Gcm.Block) : (Spec.Gcm.toBytes x).length = 16 := by simp [Spec.Gcm.toBytes]

theorem toBytes_ofBytes {bs : List Byte} (h : bs.length = 16) : Spec.Gcm.toBytes (Spec.Gcm.ofBytes bs) = bs :=
  ext16 (toBytes_length _) h fun _ hk => Proof.Aes.toBytes_ofBytes h hk

theorem ctr32_one (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [0] = [ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem aesWith_bytes (nr : Nat) (w : List Byte) {x : List Byte} (h : x.length = 16) :
    Spec.Gcm.toBytes (Spec.Gcm.aesWith nr w (Spec.Gcm.ofBytes x)) = aesWith nr w x := by
  rw [Spec.Gcm.aesWith, toBytes_ofBytes (by simp), aesWith]
  congr 2
  exact Vector.ext fun i hi => by simpa only [Vector.getElem_ofFn] using Proof.Aes.toBytes_ofBytes h hi

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Aes.bytesAt m p n).length = n := by
  simp [Spec.Aes.bytesAt]

theorem bytesAt_blockAt (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = Spec.Gcm.toBytes (Spec.Gcm.blockAt m p) :=
  (toBytes_ofBytes (bytesAt_length m p 16)).symm

/-! ## Lengths -/

theorem aesWith_length (nr : Nat) (w x : List Byte) : (aesWith nr w x).length = 16 := by simp [aesWith]

theorem dbl_length {x : List Byte} (h : x.length = 16) : (dbl 16 x).length = 16 := by
  unfold dbl; split <;> simp [shiftLeft1, length_xor, rb, zeros, h]

theorem subkeys_aes_length (nr : Nat) (w : List Byte) : (subkeys (aesWith nr w) 16).1.length = 16 :=
  dbl_length (aesWith_length _ _ _)

end VG.Proof.Cmac
