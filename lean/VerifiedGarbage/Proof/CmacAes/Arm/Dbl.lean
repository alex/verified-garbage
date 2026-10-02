import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Dbl

/-!
# AES-CMAC on ARMv7: doubling a block in four 32-bit words

`dbl src dst` loads a block as four byte-reversed words (`rev`), the block as
a big-endian integer (`Cmac.ofBytes_rev4`), doubles the integer a word at a
time (`Cmac.dbl_words4`), and stores the words byte-reversed again
(`Cmac.le4_rev4`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_sub wp_and wp_orr wp_rev wp_ldr wp_str)

theorem rev_eq (a : BitVec 32) : rev a = byteRev32 a := rfl

/-- The memory after `dbl src dst`, with `r6` pointing at `A`. -/
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

/-- `dbl src dst`, with `r6` pointing at `K`. -/
theorem dbl_wp {is : List Instr} {s : State} {Q : State → Prop} {K : BitVec 32} {src dst : Nat}
    (h6 : s.gpr .r6 = K) (hs : src + 12 < 4096) (hd : dst + 12 < 4096)
    (fs : K.toNat + src + 16 ≤ 2 ^ 32) (fd : K.toNat + dst + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨State.addr K + BitVec.ofNat 64 src, 16⟩] (s.rd ++ s.wr))
    (wD : Covers [⟨State.addr K + BitVec.ofNat 64 dst, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = dblMem s.mem (State.addr K) src dst → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block is) s' Q) :
    WP isa (.block (dbl src dst ++ is)) s Q := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src) (by omega) (by rw [h6]; exact addr_add (by omega))
    (in_word0 rS) fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) (by omega)
    (by rw [u₁.other _ (by decide), h6]; exact addr_word 4 fs (by decide))
    (by rw [u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₂ u₂ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h6]; exact addr_word 8 fs (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (a := State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h6]
        exact addr_word 12 fs (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_word rS (by decide)) fun s₄ u₄ => ?_
  refine wp_rev fun s₅ u₅ => wp_rev fun s₆ u₆ => wp_rev fun s₇ u₇ => wp_rev fun s₈ u₈ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₉ u₉ => wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
    wp_sub (op2_reg _ _) fun s₁₁ u₁₁ => wp_and (op2_imm (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₃ u₁₃ => wp_orr (op2_lsr (by decide)) fun s₁₄ u₁₄ =>
    wp_mov (op2_lsl (by decide)) fun s₁₅ u₁₅ => wp_orr (op2_lsr (by decide)) fun s₁₆ u₁₆ =>
    wp_mov (op2_lsl (by decide)) fun s₁₇ u₁₇ => wp_orr (op2_lsr (by decide)) fun s₁₈ u₁₈ =>
    wp_mov (op2_lsl (by decide)) fun s₁₉ u₁₉ => wp_eor (op2_reg _ _) fun s₂₀ u₂₀ => ?_
  refine wp_rev fun s₂₁ u₂₁ => wp_rev fun s₂₂ u₂₂ => wp_rev fun s₂₃ u₂₃ => wp_rev fun s₂₄ u₂₄ => ?_
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₂₄.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 h12 => by
      rw [u₂₄.other _ h3, u₂₃.other _ h2, u₂₂.other _ h1, u₂₁.other _ h0, u₂₀.other _ h3, u₁₉.other _ h3,
        u₁₈.other _ h2, u₁₇.other _ h2, u₁₆.other _ h1, u₁₅.other _ h1, u₁₄.other _ h0, u₁₃.other _ h0,
        u₁₂.other _ h12, u₁₁.other _ h12, u₁₀.other _ h4, u₉.other _ h12, u₈.other _ h3, u₇.other _ h2,
        u₆.other _ h1, u₅.other _ h0, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have g6 : s₂₄.gpr .r6 = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  have m24 : s₂₄.mem = s.mem := by
    rw [u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem, u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem,
      u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem]
  have rd24 : s₂₄.rd = s.rd := by
    rw [u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd,
      u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr24 : s₂₄.wr = s.wr := by
    rw [u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr,
      u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp24 : s₂₄.sp = s.sp := by
    rw [u₂₄.sp, u₂₃.sp, u₂₂.sp, u₂₁.sp, u₂₀.sp, u₁₉.sp, u₁₈.sp, u₁₇.sp, u₁₆.sp, u₁₅.sp, u₁₄.sp, u₁₃.sp,
      u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  -- The four words.
  have w₀ : s₁.gpr .r0 = s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32 := u₁.gpr
  have w₁ : s₂.gpr .r1 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32 := by
    rw [u₂.gpr, u₁.mem]
  have w₂ : s₃.gpr .r2 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32 := by
    rw [u₃.gpr, u₂.mem, u₁.mem]
  have w₃ : s₄.gpr .r3 = s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32 := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  have b₀ : s₈.gpr .r0 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), w₀, rev_eq]
  have b₁ : s₈.gpr .r1 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), w₁, rev_eq]
  have b₂ : s₈.gpr .r2 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      w₂, rev_eq]
  have b₃ : s₈.gpr .r3 = byteRev32 (s.mem.readW (State.addr K + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), w₃, rev_eq]
  have mask : s₁₂.gpr .r12 = ((0 : BitVec 32) - (s₈.gpr .r0 >>> 31)) &&& 0x87 := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr]
  have v₀ : s₂₄.gpr .r0 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r0) (s₈.gpr .r1)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.gpr, rev_eq,
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₁ : s₂₄.gpr .r1 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r1) (s₈.gpr .r2)) := by
    rw [u₂₄.other _ (by decide), u₂₃.other _ (by decide), u₂₂.gpr, rev_eq, u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.gpr, u₁₅.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₂.other _ (by decide),
      u₁₁.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₂ : s₂₄.gpr .r2 = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .r2) (s₈.gpr .r3)) := by
    rw [u₂₄.other _ (by decide), u₂₃.gpr, rev_eq, u₂₂.other _ (by decide), u₂₁.other _ (by decide),
      u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.gpr, u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide)]
    rfl
  have v₃ : s₂₄.gpr .r3 = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .r0) (s₈.gpr .r3)) := by
    rw [u₂₄.gpr, rev_eq, u₂₃.other _ (by decide), u₂₂.other _ (by decide), u₂₁.other _ (by decide), u₂₀.gpr,
      u₁₉.gpr, u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₆.other _ (by decide), u₁₅.other _ (by decide),
      u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₃.other _ (by decide), mask, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide)]
    rfl
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst) (by omega) (by rw [g6]; exact addr_add (by omega))
    (by rw [wr24]; exact in_word0 wD) fun s₂₅ v₂₅ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 4) (by omega)
    (by rw [v₂₅.gpr, g6]; exact addr_word 4 fd (by decide))
    (by rw [v₂₅.wr, wr24]; exact in_word wD (by decide)) fun s₂₆ v₂₆ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8) (by omega)
    (by rw [v₂₆.gpr, v₂₅.gpr, g6]; exact addr_word 8 fd (by decide))
    (by rw [v₂₆.wr, v₂₅.wr, wr24]; exact in_word wD (by decide)) fun s₂₇ v₂₇ => ?_
  refine wp_str (a := State.addr K + BitVec.ofNat 64 dst + BitVec.ofNat 64 12) (by omega)
    (by rw [v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, g6]; exact addr_word 12 fd (by decide))
    (by rw [v₂₇.wr, v₂₆.wr, v₂₅.wr, wr24]; exact in_word wD (by decide)) fun s₂₈ v₂₈ => k s₂₈ ?_ ?_ ?_ ?_ ?_
  · intro r h0 h1 h2 h3 h4 h12
    rw [v₂₈.gpr, v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, g r h0 h1 h2 h3 h4 h12]
  · rw [v₂₈.mem, v₂₇.mem, v₂₆.mem, v₂₅.mem, v₂₇.gpr, v₂₆.gpr, v₂₅.gpr, m24, v₀, v₁, v₂, v₃, b₀, b₁, b₂, b₃]
    rfl
  · rw [v₂₈.rd, v₂₇.rd, v₂₆.rd, v₂₅.rd, rd24]
  · rw [v₂₈.wr, v₂₇.wr, v₂₆.wr, v₂₅.wr, wr24]
  · rw [v₂₈.sp, v₂₇.sp, v₂₆.sp, v₂₅.sp, sp24]

end VG.Proof.CmacAes.Arm
