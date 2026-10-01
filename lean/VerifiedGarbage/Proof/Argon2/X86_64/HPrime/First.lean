import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.FinishInput
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Length

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .r15).toNat ∧ (s.gpr .r15).toNat < 2 ^ 32)
    (len : (s.gpr .r13).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩) :
    WP isa (first (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (min (s.gpr .r15).toNat 64) =
        Spec.Argon2.H (min (s.gpr .r15).toNat 64)
          (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s).mono ?_)
  rintro a ⟨lengthA, ka⟩
  have na : (a.gpr .rsi).toNat = min (s.gpr .r15).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wrA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  have retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ :=
    (swA.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))
  have lenA : 1 ≤ (a.gpr .rsi).toNat ∧ (a.gpr .rsi).toNat ≤ 64 := by rw [na]; omega
  refine WP.seq ((init_ok v a lenA wrA retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  have ku : Keeps a u := ⟨regsU, rdU, wrU, init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) u.mem (u.gpr .rbx) [] := by
    rw [ku.rbx]; simpa only [na] using reprU
  have wrU' : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact hwr
  have swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ksu.rbx, ksu.rsp]; exact stackWork
  have headU : bytesAt u.mem (u.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat := by
    rw [ksu.rbx, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok v u _ 832 4 (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  have ksw := ksu.trans kw
  have r12 : w.gpr .r12 = s.gpr .r12 := ksw.regs _ (by decide)
  have r13 : w.gpr .r13 = s.gpr .r13 := ksw.regs _ (by decide)
  have headLen : (Spec.Argon2.le32 (s.gpr .r15).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  have reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) w.mem (w.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat) := by
    rw [kw.rbx]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  have wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  have dataW : Covers [⟨w.gpr .r12, (w.gpr .r13).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  have dwW : (⟨w.gpr .r12, (w.gpr .r13).toNat⟩ : Region).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [r12, r13, ksw.rbx]; exact dataWork
  have swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rsp, ksw.rbx]; exact stackWork
  have sdW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .r12, (w.gpr .r13).toNat⟩ := by
    rw [ksw.rsp, r12, r13]; exact stackData
  have inputW : bytesAt w.mem (w.gpr .r12) (w.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .r13).toNat ≤ 2 ^ 64 by omega)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  have ksx := ksw.trans kx
  have reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) x.mem (x.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) := by
    rw [kx.rbx]; simpa only [inputW] using reprX
  have r13X : x.gpr .r13 = s.gpr .r13 := ksx.regs _ (by decide)
  have length : (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat).length =
      4 + (x.gpr .r13).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  have wrX : (⟨x.gpr .rbx, 16384⟩ : Region) ∈ x.wr := by rw [ksx.rbx, ksx.wr]; exact hwr
  have swX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rbx, 16384⟩ := by
    rw [ksx.rsp, ksx.rbx]; exact stackWork
  refine (finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  have result := congrArg (List.take (min (s.gpr .r15).toNat 64)) out
  rw [ksx.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
