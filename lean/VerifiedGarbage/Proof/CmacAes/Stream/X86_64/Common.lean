import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming AES-CMAC on x86-64: arithmetic and memory

Untrusted: everything here is checked by Lean. The number of bytes held
back, as the code computes it from `count` (`held_bv`); immediates; the
copy of a block a word at a time (`copyMem`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.Cmac.Stream (held held_pos held_zero)

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem sx6 : BitVec.signExtend 64 (6 : BitVec 32) = 6 := by decide
theorem sx15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide
theorem sx240 : BitVec.signExtend 64 (240 : BitVec 32) = BitVec.ofNat 64 240 := by decide
theorem sx272 : BitVec.signExtend 64 (272 : BitVec 32) = BitVec.ofNat 64 272 := by decide
theorem sx288 : BitVec.signExtend 64 (288 : BitVec 32) = BitVec.ofNat 64 288 := by decide

theorem and15 (x : BitVec 64) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, as `sub 1; and 15; add 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - 1) &&& 15) + 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  have := c.isLt
  omega

theorem beq_zero_iff (c : BitVec 64) : (c == 0) = decide (c.toNat = 0) := by
  by_cases h : c = 0
  · subst h; rfl
  · have : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simpa [this] using h

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem rsi_ofNat {s₀ : State} {R : Nat} (h : (s₀.gpr .rsi).toNat = R) (_hR : R = 10 ∨ R = 12 ∨ R = 14) :
    s₀.gpr .rsi = BitVec.ofNat 64 R :=
  BitVec.eq_of_toNat_eq (by rw [h, toNat_ofNat (by omega)])

/-! ## Copying a block a word at a time -/

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def copyMem (m : Mem) (o p : Addr) : Mem :=
  let m₁ := m.writeW o (m.readW p 64)
  m₁.writeW (o + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (copyMem m o p) :=
  Proof.CmacAes.X86_64.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) {o p : Addr} (h : (⟨o, 16⟩ : Region).Disjoint ⟨p, 16⟩) :
    Spec.Aes.bytesAt (copyMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  have g : Frame [⟨o, 8⟩] m (m.writeW o (m.readW p 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [copyMem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.sub_left (Region.sub_prefix (by decide))).sub_right
          (Offset.sub_base p (d := 8) (n := 8) (k := 16) (by decide)) |>.symm) (by decide),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-! ## Bytes written -/

section
open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

end

end VG.Proof.CmacAes.Stream.X86_64
