import VerifiedGarbage.Proof.AesSiv.X86_64.Env
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common

/-!
# AES-SIV on x86-64: CTR a block at a time

`ctrPart ciph q x k` is CTR's output with only its first `k` bytes done
(the rest of `x` as it is): `x` itself for `k = 0` and `ctr ciph q x` for
`k ≥ len(x)`. The data after `xorBytes` on block `i`, at `P + 16 i`, is
the next one (`ctrPart_step`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.Stream.X86_64 (writeBytes_at)

/-- CTR with the first `k` bytes done. -/
def ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) : List Byte :=
  (List.range x.length).map fun p =>
    if p < k then x.getD p 0 ^^^ (Siv.ksBlock ciph q (p / 16)).getD (p % 16) 0 else x.getD p 0

theorem length_ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) : (ctrPart ciph q x k).length = x.length := by
  simp [ctrPart]

theorem getD_ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) {p : Nat} (hp : p < x.length) :
    (ctrPart ciph q x k).getD p 0 =
      if p < k then x.getD p 0 ^^^ (Siv.ksBlock ciph q (p / 16)).getD (p % 16) 0 else x.getD p 0 := by
  simp [ctrPart, List.getD_eq_getElem?_getD, hp]

theorem ext_getD {a b : List Byte} (hl : a.length = b.length) (h : ∀ p < a.length, a.getD p 0 = b.getD p 0) : a = b := by
  apply List.ext_getElem hl
  intro p h₁ h₂
  have := h p h₁
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem ctrPart_zero (ciph : Spec.Cmac.Cipher) (q x : List Byte) : ctrPart ciph q x 0 = x :=
  ext_getD (length_ctrPart _ _ _ _) fun p hp => by
    rw [length_ctrPart] at hp; rw [getD_ctrPart _ _ _ _ hp]; simp

theorem ctrPart_all (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) {k : Nat}
    (hk : x.length ≤ k) : ctrPart ciph q x k = Spec.Siv.ctr ciph q x :=
  ext_getD (by rw [length_ctrPart, Siv.length_ctr ciph hc]) fun p hp => by
    rw [length_ctrPart] at hp
    rw [getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), Siv.ctr_getD ciph hc q x hp]

theorem getD_xor {a b : List Byte} {k : Nat} (ha : k < a.length) (hb : k < b.length) :
    (Spec.Cmac.xor a b).getD k 0 = a.getD k 0 ^^^ b.getD k 0 := by
  simp [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem getD_take {a : List Byte} {n k : Nat} (h : k < n) : (a.take n).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- One block of CTR, `n` bytes of it, XORed into the data at `P + 16 i`. -/
theorem ctrPart_step (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) (m : Mem)
    (P : Addr) {i n : Nat} (hx : x.length < 2 ^ 64) (hn : n ≤ 16) (hin : 16 * i + n ≤ x.length)
    (hd : Spec.Aes.bytesAt m P x.length = ctrPart ciph q x (16 * i)) :
    Spec.Aes.bytesAt (writeBytes m (P + BitVec.ofNat 64 (16 * i))
        (Spec.Cmac.xor (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n) ((Siv.ksBlock ciph q i).take n)))
        P x.length =
      ctrPart ciph q x (16 * i + n) := by
  have hlk : (Siv.ksBlock ciph q i).length = 16 := hc _
  have hlb : (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n)
      ((Siv.ksBlock ciph q i).take n)).length = n := by
    rw [Proof.Cmac.length_xor, hlb, List.length_take, hlk]; omega
  have hdk : ∀ p < x.length, m (P + BitVec.ofNat 64 p) = (ctrPart ciph q x (16 * i)).getD p 0 := fun p hp => by
    rw [← hd, Proof.Cmac.getD_bytesAt _ _ hp]
  refine ext_getD (by rw [Proof.Cmac.bytesAt_length, length_ctrPart]) fun p hp => ?_
  rw [Proof.Cmac.bytesAt_length] at hp
  rw [Proof.Cmac.getD_bytesAt _ _ hp, getD_ctrPart _ _ _ _ hp]
  by_cases h₁ : p < 16 * i
  · rw [writeBytes_before _ _ _ h₁ (by rw [hlx]; omega), hdk p hp, getD_ctrPart _ _ _ _ hp,
      ite_eq_left h₁, ite_eq_left (by omega)]
  · have e : P + BitVec.ofNat 64 p = P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i) := by
      rw [Offset.add_add, show 16 * i + (p - 16 * i) = p by omega]
    have hm : m (P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i)) = x.getD p 0 := by
      rw [← e, hdk p hp, getD_ctrPart _ _ _ _ hp, ite_eq_right h₁]
    rw [e, writeBytes_at _ _ _ (by omega), hlx]
    by_cases h₂ : p < 16 * i + n
    · rw [ite_eq_left (by omega), ite_eq_left h₂, getD_xor (by rw [hlb]; omega) (by rw [List.length_take, hlk]; omega),
        Proof.Cmac.getD_bytesAt _ _ (by omega), hm, getD_take (by omega),
        show p / 16 = i by omega, show p % 16 = p - 16 * i by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h₂, hm]

end VG.Proof.AesSiv.X86_64
