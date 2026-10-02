import VerifiedGarbage.Proof.Cmac.Frame

/-!
# CMAC: blocks in memory as 32-bit words

On the 32-bit targets a 16-byte block is loaded and stored as four
little-endian 32-bit words: `le4 w` is the bytes of the word `w`, and storing
`w₀ … w₃` at `p`, `p + 4`, `p + 8` and `p + 12` (`store4`) leaves
`le4 w₀ ++ … ++ le4 w₃` there. `xor4Mem` stores the XOR of two blocks a
word at a time (the block written may be one of those read), `zero4` zeroes
a block, and `chainMem4` forms a counter block `C = P ⊕ Q` and zeroes `P`.
-/

namespace VG.Proof.Cmac

open VG

/-- The bytes of a 32-bit word, least significant first. -/
def le4 (w : BitVec 32) : List Byte := (List.range 4).map fun i => w.extractLsb' (8 * i) 8

theorem length_le4 (w : BitVec 32) : (le4 w).length = 4 := by simp [le4]

theorem getD_le4 (w : BitVec 32) {k : Nat} (hk : k < 4) : (le4 w).getD k 0 = w.extractLsb' (8 * k) 8 := by
  simp [le4, List.getD_eq_getElem?_getD, hk]

theorem le4_readW (m : Mem) (a : Addr) : le4 (m.readW a 32) = Spec.Aes.bytesAt m a 4 := by
  apply List.ext_getElem (by simp [le4, Spec.Aes.bytesAt])
  intro k h₁ h₂
  have hk : k < 4 := by simpa [le4] using h₁
  simp only [le4, Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a (n := 4) hk]
  simp only [Mem.readW]
  rfl

theorem le4_xor (a b : BitVec 32) : le4 (a ^^^ b) = Spec.Cmac.xor (le4 a) (le4 b) := by
  apply List.ext_getElem (by simp [le4, Spec.Cmac.xor])
  intro k h₁ h₂
  have hk : k < 4 := by simpa [le4] using h₁
  simp only [le4, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem le4_zero : le4 0 = Spec.Cmac.zeros 4 := by decide

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Aes.bytesAt m p (a + b) = Spec.Aes.bytesAt m p a ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Aes.bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- A block as its four words' bytes. -/
theorem bytesAt_split4 (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = Spec.Aes.bytesAt m p 4 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 4) 4 ++
      Spec.Aes.bytesAt m (p + BitVec.ofNat 64 8) 4 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 12) 4 := by
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add]
  simp only [Offset.add_add, List.append_assoc]

/-- The four words `w₀ … w₃` stored at `p`. -/
def store4 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) : Mem :=
  (((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8) w₂).writeW
    (p + BitVec.ofNat 64 12) w₃

theorem frame_store4 {m : Mem} (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    Frame [⟨p, 16⟩] m (store4 m p w₀ w₁ w₂ w₃) := by
  have c (d : Nat) (h : d + 4 ≤ 16) : (⟨p, 16⟩ : Region).Contains (p + BitVec.ofNat 64 d) 4 :=
    Offset.contains_base p h (by omega)
  have c0 : (⟨p, 16⟩ : Region).Contains p 4 := by simpa using c 0 (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _
    (c 4 (by decide))).writeW (List.mem_singleton_self _) _ (c 8 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 12 (by decide))

theorem readW_store4_of_sep {m : Mem} {p a : Addr} (w₀ w₁ w₂ w₃ : BitVec 32) (h : (⟨p, 16⟩ : Region).Disjoint ⟨a, 4⟩) :
    (store4 m p w₀ w₁ w₂ w₃).readW a 32 = m.readW a 32 :=
  (frame_store4 (m := m) p w₀ w₁ w₂ w₃).readW (r := ⟨a, 4⟩) (Region.contains_self _ _)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.symm) (by decide)

/-- The bytes of a block after storing its four words. -/
theorem bytesAt_store4 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    Spec.Aes.bytesAt (store4 m p w₀ w₁ w₂ w₃) p 16 = le4 w₀ ++ le4 w₁ ++ le4 w₂ ++ le4 w₃ := by
  have sep (d e : Nat) (h : d + 4 ≤ e ∨ e + 4 ≤ d) (he : e + 4 ≤ 16) (hd : d + 4 ≤ 16) :
      Mem.Sep (p + BitVec.ofNat 64 d) (32 / 8) (p + BitVec.ofNat 64 e) (32 / 8) :=
    Offset.sep p h (by omega) (by omega)
  rw [bytesAt_split4, ← le4_readW, ← le4_readW, ← le4_readW, ← le4_readW, store4]
  rw [Mem.readW_writeW_self32, Mem.readW_writeW_sep (sep 8 12 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32, Mem.readW_writeW_sep (sep 4 12 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 4 8 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  rw [Mem.readW_writeW_sep (by simpa using sep 0 12 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (by simpa using sep 0 8 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (by simpa using sep 0 4 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem xor_append4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length) :
    Spec.Cmac.xor (a ++ b ++ c ++ d) (a' ++ b' ++ c' ++ d') =
      Spec.Cmac.xor a a' ++ Spec.Cmac.xor b b' ++ Spec.Cmac.xor c c' ++ Spec.Cmac.xor d d' := by
  simp only [List.append_assoc]
  rw [xor_append ha, xor_append hb, xor_append hc]

/-- The XOR of two blocks, a word at a time. -/
theorem xor_words4 (m : Mem) (p q : Addr) :
    le4 (m.readW p 32 ^^^ m.readW q 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 4) 32 ^^^ m.readW (q + BitVec.ofNat 64 4) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 8) 32 ^^^ m.readW (q + BitVec.ofNat 64 8) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 12) 32 ^^^ m.readW (q + BitVec.ofNat 64 12) 32) =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  rw [le4_xor, le4_xor, le4_xor, le4_xor, le4_readW, le4_readW, le4_readW, le4_readW, le4_readW,
    le4_readW, le4_readW, le4_readW, bytesAt_split4 m p, bytesAt_split4 m q,
    xor_append4 (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Aes.bytesAt])]

end VG.Proof.Cmac
