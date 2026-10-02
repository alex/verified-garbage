import VerifiedGarbage.Proof.AesGcm.X86.Flush

namespace VG.Proof.AesGcm.X86
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Gcm (be64)

theorem ext32 (w : BitVec 32) (k : Nat) : w.extractLsb' (8 * k) 8 = BitVec.ofNat 8 (w.toNat / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bswap_eq : VG.X86.bswap = byteRev32 := rfl

theorem le4_bswap (w : BitVec 32) : Proof.Cmac.le4 (VG.X86.bswap w) =
    [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8] := by
  rw [bswap_eq, Proof.Cmac.le4, byteRev32_extract]

theorem le4_be (u v : BitVec 32) :
    Proof.Cmac.le4 (VG.X86.bswap u) ++ Proof.Cmac.le4 (VG.X86.bswap v) = be64 (u.toNat * 2 ^ 32 + v.toNat) := by
  have hu := u.isLt
  have hv := v.isLt
  rw [le4_bswap, le4_bswap]
  simp only [be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append,
    List.cons.injEq, and_true]
  rw [show (24 : Nat) = 8 * 3 from rfl, show (16 : Nat) = 8 * 2 from rfl, show (8 : Nat) = 8 * 1 from rfl,
    show (0 : Nat) = 8 * 0 from rfl, ext32, ext32, ext32, ext32, ext32, ext32, ext32, ext32]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;>
    omega
