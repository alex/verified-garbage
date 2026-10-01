import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update

/-! # H′: finishing a BLAKE2b hash -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

structure FinalizeArgs (s t : State) : Prop where
  state : t.gpr .rdi = s.gpr .rbx
  digest : t.gpr .rdx = s.gpr .rbx + 768
  scratch : t.gpr .rcx = s.gpr .rbx + 192
  other : ∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem finalizeArgs_ok (s : State) : WP isa (.block finalizeArgs) s (FinalizeArgs s) := by
  apply WP.of_runBlock
  simp only [finalizeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, ite_false]

/-- The narrowed finalization call, independently of the represented message. -/
theorem finalize_call_hyps (s u : State) (hu : FinalizeArgs s u)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    (Proof.Blake2.finalizeX86_64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩]) ∧
    Covers ([] ++ [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩,
      ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .rbx + 768, 64⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  have hp : (Proof.Blake2.finalizeX86_64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩]) := by
    simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp, hu.state, hu.digest, hu.scratch, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), (Offset.disjoint _ (by decide) (by decide) (by decide)).symm,
      (stackWork.sub_left retSub).sub_right subState, (stackWork.sub_left retSub).sub_right subDigest,
      (stackWork.sub_left retSub).sub_right subScratch, (stackWork.sub_left nestSub).sub_right subState,
      (stackWork.sub_left nestSub).sub_right subDigest, (stackWork.sub_left nestSub).sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .rbx, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨768, rfl, by change 768 + 64 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([] ++ [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩,
      ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n h
    obtain ⟨r, hr, hc⟩ := writes a n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  exact ⟨hp, cover, writes⟩

theorem finalize_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .rbx) d)
    (count : s.gpr .rsi = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (finalize (hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbx + 768) 64 = Spec.Blake2.finalHash b h0 d ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩,
        ⟨s.gpr .rbx + 192, 576⟩, below (s.gpr .rsp) 16] s.mem t.mem := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have cnt : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .rbx + 768, 64⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  obtain ⟨hp, cover, writes⟩ := finalize_call_hyps s u hu hwr stackWork
  have retState : (below (u.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩ := by
    rw [sp]; exact (stackWork.sub_left retSub).sub_right subState
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .rbx) d := by
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := s.mem) _ repr
    intro i hi
    rw [callEntry_byte u retState (show 192 ≤ 2 ^ 64 by decide) hi, hu.mem]
  refine WP.call (k := Proof.Blake2.finalizeX86_64 b) v.finalize_correct (hash_ok v).finalizeNoSp
    (by change 8 * (hash v).finalize.depth + 16 < 2 ^ 64; rw [(hash_ok v).finalizeDepth]; decide)
    hp cover writes ?_
  intro t rd wr cs frame keep ⟨t', hm, hg, post⟩
  simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rsi ≠ .rsp),
    g _ (by decide : Reg.rdx ≠ .rsp), hu.state, hu.digest, cnt, hm] at post
  refine ⟨post h0 d repr' bound count, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).finalize.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).finalizeDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.X86_64.HPrime
