import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheWord
import VerifiedGarbage.Proof.Argon2.X86_64.AddressGenerationCT

/-! The cached random word is secret; its read address is public. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

structure WordRelated (s t : State) : Prop where
  layout : AddressCalls.Related s t
  indices : s.gpr .r15 = t.gpr .r15

theorem wordArgs_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r15], s.gpr r = t.gpr r)
    (.block wordArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem wordRead_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rcx, .rax], s.gpr r = t.gpr r)
    (.block wordRead) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rcx, .rax])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem word_rel : RelCT isa WordRelated Impl.Argon2.X86_64.AddressCache.word (fun _ _ => True) := by
  have trace := wordArgs_rel.mono (P' := WordRelated) (by
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.layout.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨wordArgs_ok s h.layout.left.frameRead, wordArgs_ok t h.layout.right.frameRead⟩)
  have args : RelCT isa WordRelated (.block wordArgs)
      (fun s t => ∀ r ∈ [Reg.rcx, .rax], s.gpr r = t.gpr r) := full.mono (fun _ _ h => h) (by
    intro a b h r hr
    obtain ⟨_, s, t, hp, ⟨sa, ia, _⟩, ⟨sb, ib, _⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sa.trans (hp.layout.work.trans sb.symm)
    · exact ia.trans ((congrArg (· &&& 127) hp.indices).trans ib.symm))
  exact args.seq wordRead_rel

end VG.Proof.Argon2.X86_64.AddressCache
