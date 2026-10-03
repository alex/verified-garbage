import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb

/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem next_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (next v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (s.gpr .x1).toNat =
        Spec.Argon2.H (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x24 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok v s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [ka.x24]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) a.mem (a.gpr .x24) [] := by
    rw [ka.x24]; exact reprA
  have wrA' : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) u.mem (u.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [ku.x24]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_movz fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr _ => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) w.mem (w.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.mem, kw.x24]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .x1 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .x24 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .x24 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.x24, ksw.sp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .x1).toNat) out
  rw [ksw.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
