import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Tactic.SplitIfs

/-!
# AES and GHASH on x86 (32-bit): regions of 32-bit buffers

Parts of a buffer at a 32-bit address `b` that does not wrap around the
(32-bit) address space: which parts contain which accesses, and which are
disjoint. The single-instruction weakest-precondition rules are
`Proof/Framework/X86/Wp.lean`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86

/-- The region of `n` bytes at a 32-bit pointer. -/
abbrev reg32 (b : BitVec 32) (n : Nat) : Region := ⟨b.setWidth 64, n⟩

theorem addr_zero (b : BitVec 32) : addr b 0 = b.setWidth 64 := by simp [addr]

theorem toNat_setWidth32 (b : BitVec 32) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The `n` bytes at offset `o` of a buffer at `b` are within its part at offset `a`. -/
theorem part_contains {b : BitVec 32} {N a k o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hak : a + k ≤ N)
    (h1 : a ≤ o) (h2 : o + n ≤ a + k) (hn : 0 < n) : (⟨addr b a, k⟩ : Region).Contains (addr b o) n := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have hE := toNat_setWidth32 b
  generalize b.setWidth 64 = E at *
  bv_omega

theorem reg_contains {b : BitVec 32} {N o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : o + n ≤ N)
    (hn : 0 < n) : (reg32 b N).Contains (addr b o) n := by
  have := part_contains (a := 0) (k := N) hfit (by omega) (Nat.zero_le o) (by omega) hn
  rwa [addr_zero] at this

theorem in_reg {rs : List Region} {b : BitVec 32} {N : Nat} (hr : reg32 b N ∈ rs)
    (hfit : b.toNat + N ≤ 2 ^ 32) {o n : Nat} (h : o + n ≤ N) (hn : 0 < n) : InRegions rs (addr b o) n :=
  ⟨_, hr, reg_contains hfit h hn⟩

theorem in_rd {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs' a n) :
    InRegions (rs ++ rs') a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem in_rd_left {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    InRegions (rs ++ rs') a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_left _ hr, hc⟩

/-- Two parts of a buffer at `b` that do not overlap. -/
theorem part_disj {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ha : a + n ≤ N)
    (hc : c + k ≤ N) (h : a + n ≤ c ∨ c + k ≤ a) :
    Region.Disjoint ⟨addr b a, n⟩ ⟨addr b c, k⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  by_cases hn : n = 0
  · omega
  by_cases hk : k = 0
  · omega
  rw [addr_eq (by omega)] at h₁
  rw [addr_eq (by omega)] at h₂
  have hE := toNat_setWidth32 b
  generalize b.setWidth 64 = E at *
  rcases h with h | h <;> bv_omega

/-- A part of a buffer at `b` within another. -/
theorem part_sub {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hc : c + k ≤ N)
    (h1 : c ≤ a) (h2 : a + n ≤ c + k) : Region.Sub ⟨addr b a, n⟩ ⟨addr b c, k⟩ := by
  intro x h
  simp only [Region.Contains] at h ⊢
  by_cases hn : n = 0
  · omega
  rw [addr_eq (by omega)] at h ⊢
  have hE := toNat_setWidth32 b
  generalize b.setWidth 64 = E at *
  bv_omega

theorem part_sub_reg {b : BitVec 32} {N a n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : a + n ≤ N) :
    Region.Sub ⟨addr b a, n⟩ (reg32 b N) := by
  have := part_sub (c := 0) (k := N) (a := a) (n := n) hfit (by omega) (Nat.zero_le _) (by omega)
  rwa [addr_zero] at this

theorem addr_add (b : BitVec 32) (a o : Nat) : addr (b + BitVec.ofNat 32 a) o = addr b (a + o) := by
  simp only [addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Words of a buffer -/

theorem rd_wr_other {m : Mem} {a b : Addr} {v : BitVec 32} {r₁ r₂ : Region} (h : r₁.Disjoint r₂)
    (ha : r₁.Contains a (32 / 8)) (hb : r₂.Contains b (32 / 8)) : (m.writeW b v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (h.sep ha hb) (by decide)

theorem frame_one {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {r : Region}
    (hc : r.Contains a 1) (hd : ∀ r' ∈ rs, r.Disjoint r') : m' a = m a :=
  hf a fun r' hr' hc' => hd r' hr' a hc hc'

/-- A word of a 32-bit buffer, after writing a word of it. -/
theorem rd_wr {B : BitVec 32} {N : Nat} (hfit : B.toNat + N ≤ 2 ^ 32) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hd4 : d % 4 = 0) (he4 : e % 4 = 0) :
    (m.writeW (addr B e) v).readW (addr B d) 32 = if d = e then v else m.readW (addr B d) 32 := by
  split
  · subst_vars; exact Mem.readW_writeW_self32 _ _ _
  · refine Mem.readW_writeW_sep (Region.Disjoint.sep (r₁ := ⟨addr B d, 4⟩) (r₂ := ⟨addr B e, 4⟩)
      (part_disj hfit hd he (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

theorem rd_wr_ne {B : BitVec 32} {N : Nat} (hfit : B.toNat + N ≤ 2 ^ 32) (m : Mem) (v : BitVec 32)
    {d e : Nat} (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hd4 : d % 4 = 0) (he4 : e % 4 = 0) (hne : d ≠ e) :
    (m.writeW (addr B e) v).readW (addr B d) 32 = m.readW (addr B d) 32 := by
  rw [rd_wr hfit m v hd he hd4 he4, ite_eq_right hne]

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega))

/-- Bit `8 i + t` of a little-endian word is bit `t` of its byte `i`. -/
theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 4) (ht : t < 8) :
    (m.readW a 32).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 4) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 32 by omega]

theorem addr_add64 {S : BitVec 32} {x y : Nat} (h : S.toNat + x + y < 2 ^ 32) :
    addr S x + BitVec.ofNat 64 y = addr S (x + y) := by
  rw [addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Aes.X86
