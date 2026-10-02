import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressOperation
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCallCT
import VerifiedGarbage.Proof.Argon2.AArch64.FillWriteCT

/-! Only the compression argument addresses, public frame words and stack
pointer determine the compression-and-write trace. -/

namespace VG.Proof.Argon2.AArch64.FillCompress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress

structure Related (s t : State) : Prop where
  left : OperationReady s
  right : OperationReady t
  args : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x19], s.gpr r = t.gpr r
  dest : destination s = destination t
  counter : pass s = pass t
  sp : s.sp = t.sp

structure BeforeWrite (s t : State) : Prop where
  leftRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  rightRead : ∀ d ∈ [0, 16, 248], InRegions (t.rd ++ t.wr) (off (t.gpr .x19) d) 8
  bases : s.gpr .x19 = t.gpr .x19
  sp : s.sp = t.sp
  words : ∀ d ∈ [0, 16, 248],
    s.mem.readW (off (s.gpr .x19) d) 64 = t.mem.readW (off (t.gpr .x19) d) 64

theorem called_public {s t a b : State} (hp : Related s t)
    (ha : Called s a) (hb : Called t b) : BeforeWrite a b := by
  have abp : a.gpr .x19 = s.gpr .x19 := ha.regs .x19 (by simp [loopRegs])
  have bbp : b.gpr .x19 = t.gpr .x19 := hb.regs .x19 (by simp [loopRegs])
  refine ⟨?_, ?_, abp.trans ((hp.args .x19 (by simp)).trans bbp.symm), ha.sp.trans (hp.sp.trans hb.sp.symm), ?_⟩
  · intro d hd
    rw [ha.rd, ha.wr, abp]; exact hp.left.frameRead d hd
  · intro d hd
    rw [hb.rd, hb.wr, bbp]; exact hp.right.frameRead d hd
  · intro d hd
    rw [abp, bbp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [frame_word hp.left ha 0 (by decide), frame_word hp.right hb 0 (by decide)]
      exact hp.counter
    · rw [frame_word hp.left ha 16 (by decide), frame_word hp.right hb 16 (by decide)]
      exact hp.dest
    · rw [frame_word hp.left ha 248 (by decide), frame_word hp.right hb 248 (by decide),
        hp.left.workWord, hp.right.workWord]
      exact hp.args .x3 (by simp)

theorem call_public_rel : RelCT isa Related
    (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.AArch64.compress) BeforeWrite := by
  have trace := call_rel Spec.Argon2.compressApi.name (P := Related) (fun _ _ hp =>
    ⟨hp.left.call, hp.right.call, hp.args .x0 (by simp), hp.args .x1 (by simp),
      hp.args .x2 (by simp), hp.args .x3 (by simp), hp.sp⟩)
  have full := trace.wpDep (fun s t hp =>
    ⟨call_ok _ s hp.left.call, call_ok _ t hp.right.call⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact called_public hp ha hb

theorem writeArgs_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block writeArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem writeArgs_public_rel : RelCT isa BeforeWrite (.block writeArgs)
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x5, .x0, .x1], s.gpr r = t.gpr r) := by
  have trace := writeArgs_rel.mono (P' := BeforeWrite) (fun _ _ h => ⟨h.bases, h.sp⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨writeArgs_ok s (hp.leftRead 16 (by simp)) (hp.leftRead 248 (by simp)) (hp.leftRead 0 (by simp)),
      writeArgs_ok t (hp.rightRead 16 (by simp)) (hp.rightRead 248 (by simp)) (hp.rightRead 0 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨eq, s, t, hp, ha, hb⟩ := h
  refine ⟨eq, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha.2.2.1.trans ((hp.words 0 (by simp)).trans hb.2.2.1.symm)
  · exact ha.1.trans ((hp.words 16 (by simp)).trans hb.1.symm)
  · exact ha.2.1.trans ((congrArg (· + (4096 : Addr)) (hp.words 248 (by simp))).trans hb.2.1.symm)

theorem operation_rel : RelCT isa Related operation (fun s t => s.sp = t.sp) :=
  call_public_rel.seq (writeArgs_public_rel.seq FillWrite.code_rel)

end VG.Proof.Argon2.AArch64.FillCompress
