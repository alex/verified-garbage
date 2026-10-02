import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressOperation
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressCallCT
import VerifiedGarbage.Proof.Argon2.X86_64.FillWriteCT

/-! Only the compression argument addresses, public frame words and stack
pointer determine the compression-and-write trace. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

structure Related (s t : State) : Prop where
  left : OperationReady s
  right : OperationReady t
  args : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .rbp], s.gpr r = t.gpr r
  dest : destination s = destination t
  counter : pass s = pass t

structure BeforeWrite (s t : State) : Prop where
  leftRead : ∀ d ∈ [0, 16, 248], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  rightRead : ∀ d ∈ [0, 16, 248], InRegions (t.rd ++ t.wr) (off (t.gpr .rbp) d) 8
  bases : s.gpr .rbp = t.gpr .rbp
  words : ∀ d ∈ [0, 16, 248],
    s.mem.readW (off (s.gpr .rbp) d) 64 = t.mem.readW (off (t.gpr .rbp) d) 64

theorem called_public {s t a b : State} (hp : Related s t)
    (ha : Called s a) (hb : Called t b) : BeforeWrite a b := by
  have abp : a.gpr .rbp = s.gpr .rbp := ha.regs .rbp (by simp [calleeSaved])
  have bbp : b.gpr .rbp = t.gpr .rbp := hb.regs .rbp (by simp [calleeSaved])
  refine ⟨?_, ?_, abp.trans ((hp.args .rbp (by simp)).trans bbp.symm), ?_⟩
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
      exact hp.args .rcx (by simp)

theorem call_public_rel : RelCT isa Related
    (.call Spec.Argon2.compressApi.name VG.Impl.Argon2.X86_64.compress) BeforeWrite := by
  have trace := call_rel Spec.Argon2.compressApi.name (P := Related) (fun _ _ hp =>
    ⟨hp.left.call, hp.right.call, hp.args .rdi (by simp), hp.args .rsi (by simp),
      hp.args .rdx (by simp), hp.args .rcx (by simp), hp.args .rsp (by simp)⟩)
  have full := trace.wpDep (fun s t hp =>
    ⟨call_ok _ s hp.left.call, call_ok _ t hp.right.call⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact called_public hp ha hb

theorem writeArgs_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block writeArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem writeArgs_public_rel : RelCT isa BeforeWrite (.block writeArgs)
    (fun s t => ∀ r ∈ [Reg.r9, .rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := writeArgs_rel.mono (P' := BeforeWrite) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t hp =>
    ⟨writeArgs_ok s (hp.leftRead 16 (by simp)) (hp.leftRead 248 (by simp)) (hp.leftRead 0 (by simp)),
      writeArgs_ok t (hp.rightRead 16 (by simp)) (hp.rightRead 248 (by simp)) (hp.rightRead 0 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ha.2.2.1.trans ((hp.words 0 (by simp)).trans hb.2.2.1.symm)
  · exact ha.1.trans ((hp.words 16 (by simp)).trans hb.1.symm)
  · exact ha.2.1.trans ((congrArg (· + (4096 : Addr)) (hp.words 248 (by simp))).trans hb.2.1.symm)

theorem operation_rel : RelCT isa Related operation (fun _ _ => True) :=
  call_public_rel.seq (writeArgs_public_rel.seq FillWrite.code_rel)

end VG.Proof.Argon2.X86_64.FillCompress
