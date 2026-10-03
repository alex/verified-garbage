import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseLit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain

/-! Merged from `Proof.Ed25519.AArch64.ScalarBaseMemory`. -/
section
/-! Output pointer and saved registers remain outside the point workspace. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t => t.gpr .x0 = s.gpr .x2 ∧
      (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 ∧ Outside (s.gpr .x2) 48 8 s.mem t.mem := by
  have hw' : InRegions s.wr (off (s.gpr .x2) 48) 8 :=
    ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, mov, hw', Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write, BitVec.setWidth_eq, write64_eq_writeW, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write, BitVec.setWidth_eq, write64_eq_writeW]
    exact writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .x2 = base ∧ t.gpr .x0 = s.mem.readW (off base 48) 64 ∧ Keeps [.x2, .x0] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    mov, ld, addr, Size.bytes, State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs.x0, hr, BitVec.setWidth_eq, BitVec.add_zero, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 32 = Spec.Ed25519.bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.AArch64
end

/-! Base-point multiplication satisfies its memory and ABI obligations. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt)

def scalarBaseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .x1) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

theorem farScr {base p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    8192 ≤ ofs base (off p i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  change (off p i - base).toNat + 1 ≤ 8192
  change (off p i - base).toNat < 8192 at h
  omega

theorem scalarBase_correct {s : State} (hs : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd, hn⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBase]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, spa, ma, sva⟩ => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, spb, ob, mb⟩ => ?_
  rw [ga] at pb ob mb
  have hb : Scr b (s.gpr .x2) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .x2, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .x2) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .x1) 32 = bytesAt s.mem (s.gpr .x1) 32 := bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (scalarBaseEngine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .x1, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => farScr hd hq (by decide))) fun c ⟨kc, vc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .x2) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have x2d : d.gpr .x2 = s.gpr .x2 := pd
  have x0d : d.gpr .x0 = s.gpr .x0 := od.trans oc
  have wd : d.wr = s.wr := kd.wr.trans wc
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) x2d (wd ▸ hws) (by rw [kd.mem]; exact svc))
    fun e ⟨re, ke⟩ => ?_
  have x0e : e.gpr .x0 = s.gpr .x0 := (ke.gpr _ (by decide)).trans x0d
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ e.wr := by rw [ke.wr, wd, hw]; simp
  refine WP.mono (scalarOut_ok x0e hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.x19, 0) (by decide)
    · exact re (.x20, 8) (by decide)
    · exact re (.x21, 16) (by decide)
    · exact re (.x22, 24) (by decide)
    · exact re (.x23, 32) (by decide)
    · exact re (.x24, 40) (by decide)
    all_goals
      rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
  · exact ke.sp.trans (kd.sp.trans (kc.sp.trans (spb.trans spa)))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarBase, encodedValue_spec, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [val4, ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide), ke.gpr .x7 (by decide),
      kd.gpr .x4 (by decide), kd.gpr .x5 (by decide), kd.gpr .x6 (by decide), kd.gpr .x7 (by decide)]
    change val4 (c.gpr .x4) (c.gpr .x5) (c.gpr .x6) (c.gpr .x7) = _
    rw [vc, input]

end VG.Proof.Ed25519.AArch64
