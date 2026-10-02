import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWord
import VerifiedGarbage.Proof.Argon2.AArch64.AddressGenerationCT

/-! The cached random word is secret; its read address is public. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache

structure WordRelated (s t : State) : Prop where
  layout : AddressCalls.Related s t
  indices : s.gpr .x23 = t.gpr .x23

theorem wordArgs_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x23], s.gpr r = t.gpr r)
    (.block wordArgs) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem wordRead_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x3, .x8], s.gpr r = t.gpr r)
    (.block wordRead) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x3, .x8])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem word_rel : RelCT isa WordRelated Impl.Argon2.AArch64.AddressCache.word (fun s t => s.sp = t.sp) := by
  have trace := wordArgs_rel.mono (P' := WordRelated) (by
    intro s t h
    refine ⟨h.layout.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.layout.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨wordArgs_ok s h.layout.left.frameRead, wordArgs_ok t h.layout.right.frameRead⟩)
  have args : RelCT isa WordRelated (.block wordArgs)
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x3, .x8], s.gpr r = t.gpr r) := full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨eq, s, t, hp, ⟨sa, ia, _⟩, ⟨sb, ib, _⟩⟩ := h
    refine ⟨eq, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sa.trans (hp.layout.work.trans sb.symm)
    · exact ia.trans ((congrArg (· &&& 127) hp.indices).trans ib.symm))
  exact args.seq wordRead_rel

end VG.Proof.Argon2.AArch64.AddressCache
