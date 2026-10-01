import VerifiedGarbage.Proof.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Argon2.X86_64.Round
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-! # Verified Argon2 block compression on x86-64 -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

theorem CopyKeeps.callee {s t : State} (h : CopyKeeps s t) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  apply h.1
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Keeps.callee {s t : State} (h : Keeps s t) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact h.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem move_output (s : State) :
    WP isa (.block [.mov .rdi (.reg .rdx)]) s fun t =>
      t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ite_true]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial⟩

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
    WP isa Impl.Argon2.X86_64.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  have inputs : Inputs s (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.X86_64.compress
  apply WP.seq
  refine (init_prefix 128 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  apply WP.seq
  refine (move_output s1).mono ?_
  rintro s2 ⟨hout2, hk2, hm2, hr2, hw2⟩
  have scr2 : Scratch s2 (s.gpr .rcx) :=
    ⟨(hk2 .rcx (by decide)).trans ((hk1.1 .rcx (by decide)).trans rfl),
      (hw2.trans hk1.2.2) ▸ scr.wr⟩
  apply WP.seq
  refine (rounds_ok rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8) s2 scr2).mono ?_
  rintro s3 ⟨hrow, hf3, hk3⟩
  apply WP.seq
  refine (rounds_ok colIndex Proof.Argon2.colIndex_injective (List.finRange 8)
    s3 (scr2.of_keeps hk3)).mono ?_
  rintro s4 ⟨hcol, hf4, hk4⟩
  have hout4 : s4.gpr .rdi = s.gpr .rdx := by
    rw [hk4.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk3.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hout2, hk1.1 .rdx (by decide)]
  have hw4 : s4.wr = s.wr := hk4.2.2.trans (hk3.2.2.trans (hw2.trans hk1.2.2))
  refine (finish_prefix 128 (by decide) s4 ((scr2.of_keeps hk3).of_keeps hk4) hout4
    (by rw [hw4, hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, hf5, hk5⟩
  refine ⟨?_, ?_, ?_⟩
  · have ho4 := original_preserved (hf3.trans hf4)
    rw [hm2, horig] at ho4
    have he := written_block hfinish
    rw [hcol, hrow, hm2, hwork, ho4] at he
    exact he
  · intro r hr
    have ne : r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hk5.callee r hr).trans ((hk4.callee r hr).trans ((hk3.callee r hr).trans
      ((hk2 r ne).trans (hk1.callee r hr))))
  · rw [hwr]
    have f1 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f2 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s1.mem s2.mem := by
      rw [hm2]; exact Frame.refl _ _
    have f5 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s4.mem t.mem :=
      hf5.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    exact (((f1.trans f2).trans (round_frame hf3)).trans (round_frame hf4)).trans f5

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

/-- The emitted primitive is verified against the merged, target-independent contract. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies

end VG.Proof.Argon2.X86_64
