import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame

/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm)

theorem finishInput_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (length : d.length = 4 + (s.gpr .x21).toNat) (bound : (s.gpr .x21).toNat < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (finishInput v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha => wp_addImm (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u := by
    refine ⟨fun r hr _ => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, hu.sp.trans ha.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  have repr' : Repr b h0 u.mem (u.gpr .x24) d := by rw [hu.mem, ha.mem, ku.x24]; exact repr
  have count : u.gpr .x1 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  have len : d.length < 2 ^ 64 := by rw [length]; omega
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ku.x24, ku.wr]; exact hwr
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ku.x24, ku.sp]; exact stackWork
  refine (finalize_ok v u h0 d repr' count len (by rw [ku.sp]; exact hsp) wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ _ frame⟩⟩
  simpa only [ku.x24] using out

end VG.Proof.Argon2.AArch64.HPrime
