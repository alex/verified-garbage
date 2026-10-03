import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.X86_64.Setup

/-! Load the encoded y-coordinate and its separate sign bit. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps ea_at val4)

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

theorem loadSign_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : InRegions (s.rd ++ s.wr) (off p 24) 8) :
    WP isa (.block loadSign) s fun t =>
      t.gpr .rsi = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      Keeps [.rsi] s t := by
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
  simp only [loadSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift,
    State.load64, ea_at, hp, hr, show 1 ≤ 63 ∧ 63 ≤ 63 by decide, and_self,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

theorem loadY_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block Impl.X25519.X86_64.loadU) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s t := by
  refine WP.mono (Proof.X25519.X86_64.loadU_ok s hp hr) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, kt⟩
  rw [tv, Proof.X25519.decodeUCoordinate_eq (Proof.X25519.length_bytesAt _ _ _), decodeLE_eq]
  rfl

end VG.Proof.Ed25519.X86_64
