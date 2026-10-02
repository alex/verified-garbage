import VerifiedGarbage.Proof.Argon2.X86_64.FillSetupEnvironment
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup

/-! Establish the complete pass-loop invariant from memory initialization's byte stride. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  environment : Environment p s
  bound : 1024 * p.laneLen < 2 ^ 64
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * p.laneLen)

structure Prepared (s t : State) (p : Params) : Prop where
  ready : FillIterations.Ready p 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  words : ∀ d, 8 ≤ d → d + 8 ≤ 272 →
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.X86_64.FillSetup.code s (Prepared s · p) := by
  unfold Impl.Argon2.X86_64.FillSetup.code
  refine WP.seq ((dimensions_nat_ok s p h.bound h.stride).mono ?_)
  rintro a ⟨laneLength, segmentLength, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
  have environment := h.environment.of_state bp sp keeps.mem keeps.rd keeps.wr
  refine (reset_ok a environment.passWrite).mono ?_
  intro t reset
  have header := reset.header environment ((reset.regs .r12 (by decide)).trans laneLength)
    ((reset.regs .r13 (by decide)).trans segmentLength)
  have words (d : Nat) (lower : 8 ≤ d) (upper : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [reset.read d lower upper, keeps.mem, bp]
  refine ⟨⟨⟨environment.parameters, 0, 0, header⟩, environment.passesBound, ?_⟩,
    words 232 (by decide) (by decide), words 248 (by decide) (by decide), ?_,
    reset.rd.trans keeps.rd, reset.wr.trans keeps.wr, ?_, reset.mxcsr.trans keeps.mxcsr, words⟩
  · rw [reset.wr, reset.regs .rbp (by decide)]; exact environment.passWrite
  · intro r hr bx q g sl
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reset.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ne, bx, sl⟩)).trans
      (keeps.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨q, g⟩))
  · have frame := reset.frame
    rw [bp, keeps.mem] at frame; exact frame

theorem Prepared.represents {s t : State} {p : Params} (ready : Ready p s) (done : Prepared s t p)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [done.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame done.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.environment.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Region.sub_prefix (by decide))

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.FillSetup.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.FillSetup
