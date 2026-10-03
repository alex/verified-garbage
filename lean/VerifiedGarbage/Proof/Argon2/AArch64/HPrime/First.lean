import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FinishInput
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Length

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (len : (s.gpr .x21).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩) :
    WP isa (first v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (min (s.gpr .x23).toNat 64) =
        Spec.Argon2.H (min (s.gpr .x23).toNat 64)
          (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  have na : (a.gpr .x1).toNat = min (s.gpr .x23).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wrA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lenA : 1 ≤ (a.gpr .x1).toNat ∧ (a.gpr .x1).toNat ≤ 64 := by rw [na]; omega
  refine WP.seq ((init_ok v a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) u.mem (u.gpr .x24) [] := by
    rw [ku.x24]; simpa only [na] using reprU
  have wrU' : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact hwr
  have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ksu.x24, ksu.sp]; exact stackWork
  have headU : bytesAt u.mem (u.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat := by
    rw [ksu.x24, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok v u _ 832 4 (by decide) (by rw [ksu.sp]; exact hsp) (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  have ksw := ksu.trans kw
  have r12 : w.gpr .x20 = s.gpr .x20 := ksw.regs _ (by decide) (by decide)
  have r13 : w.gpr .x21 = s.gpr .x21 := ksw.regs _ (by decide) (by decide)
  have headLen : (Spec.Argon2.le32 (s.gpr .x23).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  have reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) w.mem (w.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat) := by
    rw [kw.x24]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have dataW : Covers [⟨w.gpr .x20, (w.gpr .x21).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  have dwW : (⟨w.gpr .x20, (w.gpr .x21).toNat⟩ : Region).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [r12, r13, ksw.x24]; exact dataWork
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.sp, ksw.x24]; exact stackWork
  have sdW : (below w.sp 16).Disjoint ⟨w.gpr .x20, (w.gpr .x21).toNat⟩ := by
    rw [ksw.sp, r12, r13]; exact stackData
  have inputW : bytesAt w.mem (w.gpr .x20) (w.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .x21).toNat ≤ 2 ^ 64 by omega)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    (by rw [ksw.sp]; exact hsp) wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  have ksx := ksw.trans kx
  have reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) x.mem (x.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) := by
    rw [kx.x24]; simpa only [inputW] using reprX
  have r13X : x.gpr .x21 = s.gpr .x21 := ksx.regs _ (by decide) (by decide)
  have length : (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat).length =
      4 + (x.gpr .x21).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  have wrX : (⟨x.gpr .x24, 16384⟩ : Region) ∈ x.wr := by rw [ksx.x24, ksx.wr]; exact hwr
  have swX : (below x.sp 16).Disjoint ⟨x.gpr .x24, 16384⟩ := by
    rw [ksx.sp, ksx.x24]; exact stackWork
  refine (finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) (by rw [ksx.sp]; exact hsp) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  have result := congrArg (List.take (min (s.gpr .x23).toNat 64)) out
  rw [ksx.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
