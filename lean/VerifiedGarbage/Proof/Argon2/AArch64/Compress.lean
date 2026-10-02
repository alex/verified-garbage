import VerifiedGarbage.Proof.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Argon2.AArch64.Round
import VerifiedGarbage.Proof.Argon2.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-! Correctness, memory safety, ABI preservation, and constant time of ARM64 Argon2 G. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64 VG.Spec.Argon2

theorem original_preserved {m m' : Mem} {p : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have he : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega))
      (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.base_disjoint p (by decide) (by decide)) (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at he
  exact he

theorem round_frame {m m' : Mem} {p out : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 4096⟩, by simp, Offset.sub_base p (by decide)⟩

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.AArch64.compress s fun t => compressLocal.post s t := by
  obtain ⟨hrd, hwr, hout, hx, hy⟩ := hs
  have scr : Scratch s (s.gpr .x3) := ⟨rfl, by simp [hwr]⟩
  have inputs : Inputs s (s.gpr .x0) (s.gpr .x1) (s.gpr .x3) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.AArch64.compress
  apply WP.seq
  refine (init_prefix 128 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, _hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  have scr1 := scr.of_copy hk1
  apply WP.seq
  refine (rounds_ok rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8) s1 scr1).mono ?_
  rintro s2 ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (rounds_ok colIndex Proof.Argon2.colIndex_injective (List.finRange 8)
    s2 (scr1.of_keeps hk2)).mono ?_
  rintro s3 ⟨hcol, hf3, hk3⟩
  have hout3 : s3.gpr .x2 = s.gpr .x2 := by
    rw [hk3.1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk2.1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk1.1 .x2 (by decide) (by decide)]
  have hw3 : s3.wr = s.wr := hk3.2.2.trans (hk2.2.2.trans hk1.2.2)
  refine (finish_prefix 128 (by decide) s3 ((scr1.of_keeps hk2).of_keeps hk3) hout3
    (by rw [hw3, hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, _hf4, _hk4⟩
  have ho3 := original_preserved (hf2.trans hf3)
  rw [horig] at ho3
  have he := written_block hfinish
  rw [hcol, hrow, hwork, ho3] at he
  exact he

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.AArch64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp⟩ := compress_wp s hs
  refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hp⟩
  intro r hr
  apply Exec.gpr (c := Impl.Argon2.AArch64.compress) (hn := .inl (by decide +kernel)) _ he
  have hk : Impl.Argon2.AArch64.compress.allInstrs (keeps (RegSet.ofList preserved)) = true := by
    lit_decide
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps hk) i hi) r hr
  simpa only [bne_iff_ne] using h

theorem compress_verified : Verified AArch64.target Impl.Argon2.AArch64.compress
    (Spec.Argon2.compressContract AArch64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies
end VG.Proof.Argon2.AArch64
