import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init

/-! # H′: absorbing bytes with the selected BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

structure UpdateArgs (s t : State) : Prop where
  state : t.gpr .x0 = s.gpr .x24
  scratch : t.gpr .x4 = s.gpr .x24 + 192
  other : ∀ r, r ≠ .x0 → r ≠ .x4 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem updateArgs_ok (s : State) : WP isa (.block updateArgs) s (UpdateArgs s) := by
  apply WP.of_runBlock
  simp only [updateArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (192 : Nat) < 4096 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, ite_false]

/-- The narrowed streaming call, without assumptions about message contents. -/
theorem update_call_hyps (s u : State) (hu : UpdateArgs s u)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 192⟩)
    (dataScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24 + 192, 576⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩) :
    (Proof.Blake2.updateAArch64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) ∧
    Covers ([⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ++
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have src : u.gpr .x2 = s.gpr .x2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .x3 = s.gpr .x3 := hu.other _ (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .x24, 192⟩ ⟨s.gpr .x24, 16384⟩ := Region.sub_prefix (by decide)
  have subScratch : Region.Sub ⟨s.gpr .x24 + 192, 576⟩ ⟨s.gpr .x24, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have hp : (Proof.Blake2.updateAArch64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .x2, (s.gpr .x3).toNat⟩]
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) := by
    simp only [Proof.Blake2.updateAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .x0 (by decide), g .x2 (by decide),
      g .x3 (by decide), g .x4 (by decide), State.callEntry_sp, State.withRegions_sp,
      hu.state, hu.scratch, src, len, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide), dataState, dataScratch,
      hsp, stackWork.sub_right subState, stackData, stackWork.sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .x24, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ++
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hu.rd, hu.wr]; exact hdata a n ⟨r, hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := writes a n ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  exact ⟨hp, cover, writes⟩

theorem update_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (count : s.gpr .x1 = BitVec.ofNat 64 d.length)
    (bound : d.length + (s.gpr .x3).toNat < 2 ^ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 192⟩)
    (dataScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24 + 192, 576⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩) :
    WP isa (update v.hash) s fun t =>
      Repr b h0 t.mem (s.gpr .x24) (d ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩, below s.sp 16] s.mem t.mem := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have src : u.gpr .x2 = s.gpr .x2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .x3 = s.gpr .x3 := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := update_call_hyps s u hu hsp hwr hdata dataState dataScratch stackWork stackData
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .x24) d := by
    simpa only [State.callEntry_mem, hu.mem] using repr
  have bytes : bytesAt u.callEntry.mem (s.gpr .x2) (s.gpr .x3).toNat =
      bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat := by
    rw [State.callEntry_mem, hu.mem]
  refine WP.callF (k := Proof.Blake2.updateAArch64 b) v.updateCorrect hp cover writes ?_
    (by rw [v.ok.updateDepth]; decide)
  intro t rd wr sp' frame cs post
  simp only [Proof.Blake2.updateAArch64, State.withRegions_gpr, State.withRegions_mem,
    g .x0 (by decide), g .x1 (by decide),
    g .x2 (by decide), g .x3 (by decide),
    hu.state, src, len, cnt] at post
  have result := post h0 d repr' count bound
  rw [bytes] at result
  refine ⟨result, fun r hr h30 => (cs r hr h30).trans ?_, rd.trans hu.rd, wr.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x4 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2
  · simpa only [v.ok.updateDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.HPrime
