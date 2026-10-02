import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory

/-! Load the encoded y-coordinate and its separate sign bit. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem decodeLE_inputWords (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      val4 (m.readW (off p 0) 64) (m.readW (off p 8) 64)
        (m.readW (off p 16) 64) (m.readW (off p 24) 64) := by
  rw [decodeLE_eq, show off p 0 = p from BitVec.add_zero p, val4]
  exact VG.Proof.X25519.leNum_bytesAt_words64 m p

private theorem encoded_top (m : Mem) (p : Addr) :
    ((m.readW (off p 24) 64) >>> 63).toNat =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) / 2 ^ 255 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, decodeLE_inputWords, val4]
  have h0 := (m.readW (off p 0) 64).isLt
  have h1 := (m.readW (off p 8) 64).isLt
  have h2 := (m.readW (off p 16) 64).isLt
  omega

theorem loadSign_ok (s : State) (p : Addr) (hp : s.gpr .x2 = p)
    (hr : InRegions (s.rd ++ s.wr) (off p 24) 8) :
    WP isa (.block loadSign) s fun t =>
      t.gpr .x1 = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      Keeps [.x1] s t := by
  have hn := decodeLE_lt (Spec.Ed25519.bytesAt s.mem p 32)
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [hl] at hn
  have hv : (s.mem.readW (off p 24) 64) >>> 63 =
      signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) := by
    have h : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 0 ∨
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 1 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [encoded_top]
    rcases h with h | h <;> rw [h] <;> rfl
  apply WP.of_runBlock
  simp only [loadSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bytes, hp, hr, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    and_self, show 63 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨hv, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem clearYSign_ok (s : State) (hl : s.gpr .x8 = low63) :
    WP isa (.block [.logic .and .x .x7 .x7 .x8]) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 ^ 255 ∧
      Keeps [.x7] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, hl, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [val4, low63, and_low63]
    have h0 := (s.gpr .x4).isLt
    have h1 := (s.gpr .x5).isLt
    have h2 := (s.gpr .x6).isLt
    omega
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem loadY_ok (s : State) (p : Addr) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadY) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  change WP isa (.block (loadWords .x2 ++ const64 .x8 low63 ++
    ([.logic .and .x .x7 .x7 .x8] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWords_ok s .x2 (by decide) (by rw [hp]; exact hr)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok a .x8 low63) fun b ⟨bl, kb⟩ => ?_
  refine WP.mono (clearYSign_ok b bl) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [tv, val4, kb.gpr .x4 (by decide), kb.gpr .x5 (by decide),
    kb.gpr .x6 (by decide), kb.gpr .x7 (by decide)]
  rw [← val4, av, hp, decodeLE_inputWords]

end VG.Proof.Ed25519.AArch64
