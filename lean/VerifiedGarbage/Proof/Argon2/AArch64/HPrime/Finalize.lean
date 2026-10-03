import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Update

/-! # H′: finishing a BLAKE2b hash -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

structure FinalizeArgs (s t : State) : Prop where
  state : t.gpr .x0 = s.gpr .x24
  digest : t.gpr .x2 = s.gpr .x24 + 768
  scratch : t.gpr .x3 = s.gpr .x24 + 192
  other : ∀ r, r ≠ .x0 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem finalizeArgs_ok (s : State) : WP isa (.block finalizeArgs) s (FinalizeArgs s) := by
  apply WP.of_runBlock
  simp only [finalizeArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (192 : Nat) < 4096 from by decide,
    show (768 : Nat) < 4096 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

/-- The narrowed finalization call, independently of the represented message. -/
theorem finalize_call_hyps (s u : State) (hu : FinalizeArgs s u)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    (Proof.Blake2.finalizeAArch64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩]) ∧
    Covers ([] ++ [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩,
      ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have subState : Region.Sub ⟨s.gpr .x24, 192⟩ ⟨s.gpr .x24, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .x24 + 768, 64⟩ ⟨s.gpr .x24, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .x24 + 192, 576⟩ ⟨s.gpr .x24, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have hp : (Proof.Blake2.finalizeAArch64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩]) := by
    simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .x0 (by decide), g .x2 (by decide),
      g .x3 (by decide), State.callEntry_sp, State.withRegions_sp, hu.state, hu.digest, hu.scratch, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), (Offset.disjoint _ (by decide) (by decide) (by decide)).symm,
      hsp, stackWork.sub_right subState, stackWork.sub_right subDigest,
      stackWork.sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .x24, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨768, rfl, by change 768 + 64 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([] ++ [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩,
      ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n h
    obtain ⟨r, hr, hc⟩ := writes a n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  exact ⟨hp, cover, writes⟩

theorem finalize_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (count : s.gpr .x1 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (finalize v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩,
        ⟨s.gpr .x24 + 192, 576⟩, below s.sp 16] s.mem t.mem := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have cnt : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := finalize_call_hyps s u hu hsp hwr stackWork
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .x24) d := by
    simpa only [State.callEntry_mem, hu.mem] using repr
  refine WP.callF (k := Proof.Blake2.finalizeAArch64 b) v.finalizeCorrect hp cover writes ?_
    (by rw [v.ok.finalizeDepth]; decide)
  intro t rd wr sp' frame cs post
  simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem,
    g .x0 (by decide), g .x1 (by decide),
    g .x2 (by decide), hu.state, hu.digest, cnt] at post
  refine ⟨post h0 d repr' bound count, fun r hr h30 => (cs r hr h30).trans ?_, rd.trans hu.rd, wr.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [v.ok.finalizeDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.HPrime
