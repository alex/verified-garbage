import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# CMAC: forming the last block in memory

Untrusted: everything here is checked by Lean.

What `finalize`'s stores leave, on any target: the XOR of two blocks stored a
word at a time (`xor2Mem`), a zeroed block (`zero2`), and a partial last
block copied onto zeros and padded with `0x80` (`padded_bytes`).
-/

namespace VG.Proof.Cmac

open VG

/-! ## XORing two blocks, a word at a time -/

/-- The memory after storing at `c` the XOR of the blocks at `p` and `q`,
a word at a time. -/
def xor2Mem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)

theorem xor2Mem_frame (m : Mem) (c p q : Addr) : Frame [⟨c, 16⟩] m (xor2Mem m c p q) := frame_store2 _ _ _

theorem xor2Mem_bytes (m : Mem) {c p q : Addr}
    (hp : (⟨c, 8⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 8⟩)
    (hq : (⟨c, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    Spec.Aes.bytesAt (xor2Mem m c p q) c 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  have g : Frame [⟨c, 8⟩] m (m.writeW c (m.readW p 64 ^^^ m.readW q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [xor2Mem, bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.symm) (by decide),
    g.readW (r := ⟨q + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.symm) (by decide)]
  exact xor_words m p q

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Zeroing, copying and padding -/

theorem zeros_8_8 : Spec.Cmac.zeros 8 ++ Spec.Cmac.zeros 8 = Spec.Cmac.zeros 16 := by decide

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem :=
  (m.writeW c (0 : BitVec 64)).writeW (c + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem zero2_bytes (m : Mem) (c : Addr) : Spec.Aes.bytesAt (zero2 m c) c 16 = Spec.Cmac.zeros 16 := by
  rw [zero2, bytesAt_store2, le8_zero, zeros_8_8]

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Aes.bytesAt m p (i + 1) = Spec.Aes.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Aes.bytesAt, List.range_succ]

theorem bytesAt_32 (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 32 = Spec.Aes.bytesAt m p 16 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 16) 16 := by
  simp only [Spec.Aes.bytesAt]
  rw [show (32 : Nat) = 16 + 16 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The two subkeys, from the 32 bytes after the key schedule. -/
theorem k1k2 {m : Mem} {W : Addr} {k1 k2 : List Byte} (h1 : k1.length = 16)
    (h : Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 32 = k1 ++ k2) :
    Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16 = k1 ∧ Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16 = k2 := by
  rw [bytesAt_32, Offset.add_add] at h
  exact List.append_inj h (by rw [bytesAt_length, h1])

open VG.WriteBytes in
/-- The padded last block `Mₙ* ‖ 10ʲ`, from the bytes copied onto zeros. -/
theorem padded_bytes (m : Mem) (C : Addr) (xs : List Byte) (hL : xs.length < 16)
    (hz : Spec.Aes.bytesAt m C 16 = Spec.Cmac.zeros 16) :
    Spec.Aes.bytesAt ((writeBytes m C xs).writeW (C + BitVec.ofNat 64 xs.length) (0x80 : Byte)) C 16 =
      xs ++ [0x80] ++ Spec.Cmac.zeros (16 - xs.length - 1) := by
  refine ext16 (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Cmac.zeros]; omega) fun k hk => ?_
  rw [getD_bytesAt _ _ hk, writeW8_apply]
  have hz' : m (C + BitVec.ofNat 64 k) = 0 := by
    have := congrArg (fun l => l.getD k 0) hz
    rw [getD_bytesAt _ _ hk] at this
    rw [this]; simp only [Spec.Cmac.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk,
      ite_true, Option.getD_some]
  have hsub : (C + BitVec.ofNat 64 k - C).toNat = k := Mem.sub_ofNat_toNat C (by omega)
  have heq : (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) ↔ k = xs.length := by
    constructor
    · intro h
      have := congrArg (fun a => (a - C).toNat) h
      simp only [Mem.sub_ofNat_toNat C (show k < 2 ^ 64 by omega),
        Mem.sub_ofNat_toNat C (show xs.length < 2 ^ 64 by omega)] at this
      exact this
    · intro h; rw [h]
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, h, ite_true]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, show ¬ k < xs.length by omega, hz']
    obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, Spec.Cmac.zeros, List.getElem?_replicate]
    simp only [show j < 16 - xs.length - 1 by omega, ite_true, Option.getD_some]

end VG.Proof.Cmac
