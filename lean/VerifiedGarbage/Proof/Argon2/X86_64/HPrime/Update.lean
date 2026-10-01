import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init

/-! # H′: absorbing bytes with the selected BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

structure UpdateArgs (s t : State) : Prop where
  state : t.gpr .rdi = s.gpr .rbx
  scratch : t.gpr .r8 = s.gpr .rbx + 192
  other : ∀ r, r ≠ .rdi → r ≠ .r8 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem updateArgs_ok (s : State) : WP isa (.block updateArgs) s (UpdateArgs s) := by
  apply WP.of_runBlock
  simp only [updateArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, ite_false]

theorem update_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .rbx) d)
    (count : s.gpr .rsi = BitVec.ofNat 64 d.length)
    (bound : d.length + (s.gpr .rcx).toNat < 2 ^ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩)
    (dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) :
    WP isa (update (hash v)) s fun t =>
      Repr b h0 t.mem (s.gpr .rbx) (d ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩, below (s.gpr .rsp) 16] s.mem t.mem := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide)
  have src : u.gpr .rdx = s.gpr .rdx := hu.other _ (by decide) (by decide)
  have len : u.gpr .rcx = s.gpr .rcx := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  have hp : (Proof.Blake2.updateX86_64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩]
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩]) := by
    simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp,
      hu.state, hu.scratch, src, len, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide), dataState, dataScratch,
      (stackWork.sub_left retSub).sub_right subState, (stackWork.sub_left retSub).sub_right subScratch,
      (stackWork.sub_left nestSub).sub_right subState, stackData.sub_left nestSub,
      (stackWork.sub_left nestSub).sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .rbx, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ++
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hu.rd, hu.wr]; exact hdata a n ⟨r, hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := writes a n ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  have retState : (below (u.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩ := by
    rw [sp]; exact (stackWork.sub_left retSub).sub_right subState
  have retData : (below (u.gpr .rsp) 8).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ := by
    rw [sp]; exact stackData.sub_left retSub
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .rbx) d := by
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := s.mem) _ repr
    intro i hi
    rw [callEntry_byte u retState (show 192 ≤ 2 ^ 64 by decide) hi, hu.mem]
  have bytes : bytesAt u.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    rw [callEntry_byte u retData (Nat.le_of_lt (s.gpr .rcx).isLt) hi, hu.mem]
  refine WP.call (k := Proof.Blake2.updateX86_64 b) v.update_correct (hash_ok v).updateNoSp
    (by change 8 * (hash v).update.depth + 16 < 2 ^ 64; rw [(hash_ok v).updateDepth]; decide)
    hp cover writes ?_
  intro t rd wr cs frame keep ⟨t', hm, hg, post⟩
  simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr, State.withRegions_mem,
    g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rsi ≠ .rsp),
    g _ (by decide : Reg.rdx ≠ .rsp), g _ (by decide : Reg.rcx ≠ .rsp),
    hu.state, src, len, cnt, hm] at post
  have result := post h0 d repr' count bound
  rw [bytes] at result
  refine ⟨result, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2
  · change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).update.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).updateDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.X86_64.HPrime
