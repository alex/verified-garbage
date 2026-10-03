import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Invoke the verified compression primitive with narrowed permissions,
retaining the surrounding matrix and derivation frame. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64

structure CallReady (s : State) : Prop where
  left : Covers [⟨s.gpr .rdi, 1024⟩] (s.rd ++ s.wr)
  right : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr)
  output : Covers [⟨s.gpr .rdx, 1024⟩] s.wr
  scratch : Covers [⟨s.gpr .rcx, 4096⟩] s.wr
  leftScratch : (⟨s.gpr .rdi, 1024⟩ : Region).Disjoint ⟨s.gpr .rcx, 4096⟩
  rightScratch : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rcx, 4096⟩
  outputScratch : (⟨s.gpr .rdx, 1024⟩ : Region).Disjoint ⟨s.gpr .rcx, 4096⟩
  stackLeft : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 1024⟩
  stackRight : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 1024⟩
  stackOutput : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdx, 1024⟩
  stackScratch : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rcx, 4096⟩

structure Called (s t : State) : Prop where
  result : Spec.Argon2.blockAt t.mem (s.gpr .rdx) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.mem (s.gpr .rdi)) (Spec.Argon2.blockAt s.mem (s.gpr .rsi))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩, below (s.gpr .rsp) 8] s.mem t.mem

theorem noSp : NoSp Impl.Argon2.X86_64.compress := by
  have h : Impl.Argon2.X86_64.compress.allInstrs (fun i => !Taint.clobbers i .rsp) = true :=
    by lit_decide
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa only [Bool.not_eq_true'] using h i hi

theorem depth : Impl.Argon2.X86_64.compress.depth = 0 := by lit_decide

theorem call_hyps (s : State) (h : CallReady s) :
    compressLocal.pre (s.callEntry.withRegions [⟨s.gpr .rdi, 1024⟩, ⟨s.gpr .rsi, 1024⟩]
      [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩]) ∧
    Covers [⟨s.gpr .rdi, 1024⟩, ⟨s.gpr .rsi, 1024⟩,
      ⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] (s.rd ++ s.wr) ∧
    Covers [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s.wr := by
  have g : ∀ r, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun _ hr => State.callEntry_gpr s hr
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressLocal, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp]
    exact ⟨trivial, trivial, h.outputScratch, h.leftScratch, h.rightScratch,
      h.stackOutput, h.stackScratch⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.left p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.right p n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.output p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · obtain ⟨r, hr, hc⟩ := h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.output p n ⟨_, List.mem_singleton_self _, hc⟩
    · exact h.scratch p n ⟨_, List.mem_singleton_self _, hc⟩

theorem callEntry_block (s : State) (p : Addr)
    (h : (below (s.gpr .rsp) 8).Disjoint ⟨p, 1024⟩) :
    Spec.Argon2.blockAt s.callEntry.mem p = Spec.Argon2.blockAt s.mem p := by
  have frame : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem]
    exact (Frame.refl _ _).writeW (r := below (s.gpr .rsp) 8) (by simp) _
      (below_call _ (by decide) (by decide))
  apply Vector.ext
  intro i hi
  have read := frame.readW (r := ⟨p, 1024⟩) (a := off p (8 * i)) (w := 64)
    (Offset.contains_base p (d := 8 * i) (n := 8) (k := 1024) (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.symm) (by decide)
  rw [← blockAt_get s.callEntry.mem p ⟨i, hi⟩, ← blockAt_get s.mem p ⟨i, hi⟩] at read
  exact read

theorem call_ok (name : String) (s : State) (h : CallReady s) :
    WP isa (.call name Impl.Argon2.X86_64.compress) s (Called s) := by
  obtain ⟨pre, cover, writes⟩ := call_hyps s h
  refine WP.call (k := compressLocal) compress_correct noSp (by rw [depth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ ⟨u, memU, regsU, result⟩
  change Spec.Argon2.blockAt u.mem (s.callEntry.gpr .rdx) = Spec.Argon2.compress
    (Spec.Argon2.blockAt s.callEntry.mem (s.callEntry.gpr .rdi))
    (Spec.Argon2.blockAt s.callEntry.mem (s.callEntry.gpr .rsi)) at result
  rw [State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), memU,
    callEntry_block s _ h.stackLeft, callEntry_block s _ h.stackRight] at result
  rw [depth] at frame
  exact ⟨result, regs, rd, wr, frame⟩

end VG.Proof.Argon2.X86_64.FillCompress
