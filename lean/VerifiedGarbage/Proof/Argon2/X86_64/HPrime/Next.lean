import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb

/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem next_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (next (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (s.gpr .rsi).toNat =
        Spec.Argon2.H (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rbx + 768) 64) ∧ Keeps s t := by
  unfold next
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have retState := (stackWork.sub_left retSub).sub_right
    (Region.sub_prefix (base := s.gpr .rbx) (len := 192) (len' := 16384) (by decide))
  refine WP.seq ((init_ok v s hlen hwr retState).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [ka.rbx]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
    · exact ((stackWork.sub_left retSub).sub_right (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) a.mem (a.gpr .rbx) [] := by
    rw [ka.rbx]; exact reprA
  have wrA' : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) u.mem (u.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [ku.rbx]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_mov32i fun w hw _ _ => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) w.mem (w.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.mem, kw.rbx]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .rsi = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .rbx + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .rbx + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  have swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rbx, ksw.rsp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .rsi).toNat) out
  rw [ksw.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
