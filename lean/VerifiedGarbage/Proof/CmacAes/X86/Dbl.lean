import VerifiedGarbage.Proof.CmacAes.X86.Save
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Dbl

/-!
# AES-CMAC on x86: doubling a block in four 32-bit words

`dbl src dst` loads a block as four byte-reversed words (`bswap`), the block
as a big-endian integer (`Cmac.ofBytes_rev4`), doubles the integer a word at a
time (`Cmac.dbl_words4`, shifting by `add r, r`), and stores the words
byte-reversed again (`Cmac.le4_rev4`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_add wp_sub wp_andi wp_or wp_shr wp_bswap)

theorem bswap_eq (a : BitVec 32) : bswap a = byteRev32 a := rfl

theorem add_self_shl (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The memory after `dbl src dst`, with `ebx` pointing at `A`. -/
def dblMem (m : Mem) (A : Addr) (src dst : Nat) : Mem :=
  let P := A + BitVec.ofNat 64 src
  let b₀ := byteRev32 (m.readW P 32)
  let b₁ := byteRev32 (m.readW (P + BitVec.ofNat 64 4) 32)
  let b₂ := byteRev32 (m.readW (P + BitVec.ofNat 64 8) 32)
  let b₃ := byteRev32 (m.readW (P + BitVec.ofNat 64 12) 32)
  Proof.Cmac.store4 m (A + BitVec.ofNat 64 dst) (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (A : Addr) (src dst : Nat) :
    Frame [⟨A + BitVec.ofNat 64 dst, 16⟩] m (dblMem m A src dst) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem dblMem_bytes (m : Mem) (A : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (dblMem m A src dst) (A + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (A + BitVec.ofNat 64 src) 16) := by
  simp only [dblMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4,
    Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), Proof.Cmac.ofBytes_rev4]

/-- `dbl src dst`, with `ebx` pointing at `K`. -/
theorem dbl_wp {is : List Instr} {s : State} {Q : State → Prop} {K : BitVec 32} {src dst : Nat}
    (hb : s.gpr .ebx = K) (fs : K.toNat + src + 16 ≤ 2 ^ 32) (fd : K.toNat + dst + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨K.setWidth 64 + BitVec.ofNat 64 src, 16⟩] (s.rd ++ s.wr))
    (wD : Covers [⟨K.setWidth 64 + BitVec.ofNat 64 dst, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = dblMem s.mem (K.setWidth 64) src dst → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dbl src dst ++ is)) s Q := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src) (by rw [ea_at', hb]; exact addr_eq (by omega))
    (in_word0 rS) fun s₁ u₁ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 4)
    (by rw [ea_at', u₁.other _ (by decide), hb]; exact addr_word 4 fs (by decide))
    (by rw [u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₂ u₂ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 8)
    (by rw [ea_at', u₂.other _ (by decide), u₁.other _ (by decide), hb]; exact addr_word 8 fs (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₃ u₃ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 12)
    (by rw [ea_at', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb]
        exact addr_word 12 fs (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₄ u₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => wp_bswap fun s₇ u₇ => wp_bswap fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_shr (by decide) fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ =>
    wp_sub fun s₁₂ u₁₂ _ => wp_andi fun s₁₃ u₁₃ => ?_
  refine wp_add fun s₁₄ u₁₄ => wp_mov fun s₁₅ u₁₅ => wp_shr (by decide) fun s₁₆ u₁₆ => wp_or fun s₁₇ u₁₇ => ?_
  refine wp_add fun s₁₈ u₁₈ => wp_mov fun s₁₉ u₁₉ => wp_shr (by decide) fun s₂₀ u₂₀ => wp_or fun s₂₁ u₂₁ => ?_
  refine wp_add fun s₂₂ u₂₂ => wp_mov fun s₂₃ u₂₃ => wp_shr (by decide) fun s₂₄ u₂₄ => wp_or fun s₂₅ u₂₅ => ?_
  refine wp_add fun s₂₆ u₂₆ => wp_xor fun s₂₇ u₂₇ => ?_
  refine wp_bswap fun s₂₈ u₂₈ => wp_bswap fun s₂₉ u₂₉ => wp_bswap fun s₃₀ u₃₀ => wp_bswap fun s₃₁ u₃₁ => ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → r ≠ .ebp → s₃₁.gpr r = s.gpr r :=
    fun r ha hc hd hs hi hp => by
      rw [u₃₁.other _ hs, u₃₀.other _ hd, u₂₉.other _ hc, u₂₈.other _ ha, u₂₇.other _ hs, u₂₆.other _ hs,
        u₂₅.other _ hd, u₂₄.other _ hi, u₂₃.other _ hi, u₂₂.other _ hd, u₂₁.other _ hc, u₂₀.other _ hi,
        u₁₉.other _ hi, u₁₈.other _ hc, u₁₇.other _ ha, u₁₆.other _ hi, u₁₅.other _ hi, u₁₄.other _ ha,
        u₁₃.other _ hp, u₁₂.other _ hp, u₁₁.other _ hp, u₁₀.other _ hi, u₉.other _ hi, u₈.other _ hs,
        u₇.other _ hd, u₆.other _ hc, u₅.other _ ha, u₄.other _ hs, u₃.other _ hd, u₂.other _ hc, u₁.other _ ha]
  have gb : s₃₁.gpr .ebx = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hb]
  have m31 : s₃₁.mem = s.mem := by
    rw [u₃₁.mem, u₃₀.mem, u₂₉.mem, u₂₈.mem, u₂₇.mem, u₂₆.mem, u₂₅.mem, u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem,
      u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem,
      u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd31 : s₃₁.rd = s.rd := by
    rw [u₃₁.rd, u₃₀.rd, u₂₉.rd, u₂₈.rd, u₂₇.rd, u₂₆.rd, u₂₅.rd, u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd,
      u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd,
      u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr31 : s₃₁.wr = s.wr := by
    rw [u₃₁.wr, u₃₀.wr, u₂₉.wr, u₂₈.wr, u₂₇.wr, u₂₆.wr, u₂₅.wr, u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr,
      u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr,
      u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  -- The four words, byte-reversed.
  have b₀ : s₈.gpr .eax = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, bswap_eq]
  have b₁ : s₈.gpr .ecx = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.mem, bswap_eq]
  have b₂ : s₈.gpr .edx = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.mem, u₁.mem, bswap_eq]
  have b₃ : s₈.gpr .esi = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
      u₁.mem, bswap_eq]
  have v : s₃₁.gpr .eax = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .eax) (s₈.gpr .ecx)) ∧
      s₃₁.gpr .ecx = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .ecx) (s₈.gpr .edx)) ∧
      s₃₁.gpr .edx = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .edx) (s₈.gpr .esi)) ∧
      s₃₁.gpr .esi = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .eax) (s₈.gpr .esi)) := by
    simp (disch := decide) only [u₃₁.gpr, u₃₁.other, u₃₀.gpr, u₃₀.other, u₂₉.gpr, u₂₉.other, u₂₈.gpr, u₂₈.other, u₂₇.gpr, u₂₇.other, u₂₆.gpr, u₂₆.other, u₂₅.gpr, u₂₅.other, u₂₄.gpr, u₂₄.other, u₂₃.gpr, u₂₃.other, u₂₂.gpr, u₂₂.other, u₂₁.gpr, u₂₁.other, u₂₀.gpr, u₂₀.other, u₁₉.gpr, u₁₉.other, u₁₈.gpr, u₁₈.other, u₁₇.gpr, u₁₇.other, u₁₆.gpr, u₁₆.other, u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other,
      bswap_eq, add_self_shl, Proof.Cmac.dblW0, Proof.Cmac.dblW3, and_self]
  obtain ⟨v₀, v₁, v₂, v₃⟩ := v
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst) (by rw [ea_at', gb]; exact addr_eq (by omega))
    (by rw [wr31]; exact in_word0 wD) fun s₃₂ v₃₂ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 4)
    (by rw [ea_at', v₃₂.gpr, gb]; exact addr_word 4 fd (by decide))
    (by rw [v₃₂.wr, wr31]; exact in_word wD (by decide)) fun s₃₃ v₃₃ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 8)
    (by rw [ea_at', v₃₃.gpr, v₃₂.gpr, gb]; exact addr_word 8 fd (by decide))
    (by rw [v₃₃.wr, v₃₂.wr, wr31]; exact in_word wD (by decide)) fun s₃₄ v₃₄ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 12)
    (by rw [ea_at', v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, gb]; exact addr_word 12 fd (by decide))
    (by rw [v₃₄.wr, v₃₃.wr, v₃₂.wr, wr31]; exact in_word wD (by decide)) fun s₃₅ v₃₅ => k s₃₅ ?_ ?_ ?_ ?_
  · intro r ha hc hd hs hi hp
    rw [v₃₅.gpr, v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, g r ha hc hd hs hi hp]
  · rw [v₃₅.mem, v₃₄.mem, v₃₃.mem, v₃₂.mem, v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, m31, v₀, v₁, v₂, v₃, b₀, b₁, b₂, b₃]
    rfl
  · rw [v₃₅.rd, v₃₄.rd, v₃₃.rd, v₃₂.rd, rd31]
  · rw [v₃₅.wr, v₃₄.wr, v₃₃.wr, v₃₂.wr, wr31]

end VG.Proof.CmacAes.X86
