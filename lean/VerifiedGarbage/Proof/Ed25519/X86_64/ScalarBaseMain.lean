import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddCodec
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain

/-! Merged from `Proof.Ed25519.X86_64.ScalarBaseMemory`. -/
section
/-! Keep the output pointer and saved registers outside the point workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Outside Keeps ea_at ea_sc)

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t => t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi ∧ Outside (s.gpr .rdx) 48 8 s.mem t.mem := by
  have hw' : InRegions s.wr (off (s.gpr .rdx) 48) 8 :=
    ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, hw', ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_self _ _ _
  · exact RegUpd.gpr_setReg_of_ne _ _ hr
  · exact Mem.readW_writeW_self64 _ _ _
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .rdx = base ∧ t.gpr .rdi = s.mem.readW (off base 48) 64 ∧ Keeps [.rdx, .rdi] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 32 = Spec.Ed25519.bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.X86_64
end

/-! Base-point multiplication satisfies its memory and ABI obligations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved val4 st4 bytesAt_st4)
open VG.Spec.Ed25519 (bytesAt)

variable {fld : Arith} [EdArith fld]

def scalarBaseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rsi, 32⟩] ∧ s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .rsi) 32)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

theorem farScratch {base p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    8192 ≤ ofs base (off p i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  change (off p i - base).toNat + 1 ≤ 8192
  change (off p i - base).toNat < 8192 at h
  omega

theorem scalarBase_correct_of_engine (engine : Prog isa) (engine_ok : BaseEngineCorrect engine)
    {s : State} (hs : scalarBaseLocal.pre s) :
    WP isa (scalarBaseWith engine) s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hn⟩ := hs
  have hws : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, ma, sva⟩ => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ => ?_
  rw [ga] at pb ob mb
  have hb : Scratch b (s.gpr .rdx) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .rdx, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .rdx) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .rsi) 32 = bytesAt s.mem (s.gpr .rsi) 32 := bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (engine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .rsi, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => farScratch hd hq (by decide))) fun c ⟨kc, vc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .rdx) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have rdxd : d.gpr .rdx = s.gpr .rdx := pd
  have rdid : d.gpr .rdi = s.gpr .rdi := od.trans oc
  have wd : d.wr = s.wr := kd.2.2.2.trans wc
  rw [WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) rdxd (wd ▸ hws) (by rw [kd.2.1]; exact svc))
    fun e ⟨re, ge, me, _, we⟩ => ?_
  have rdie : e.gpr .rdi = s.gpr .rdi := (ge _ (by decide)).trans rdid
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ e.wr := by rw [we, wd, hw]; simp
  refine WP.mono (scalarOut_ok rdie hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fme : Frame [⟨s.gpr .rdx, 8192⟩] s.mem e.mem := by
    rw [me, kd.2.1]; exact fm.trans (scratchFrame mc (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.rbx, 0) (by decide)
    · exact re (.rbp, 8) (by decide)
    · rw [ge _ (by decide), kd.1 _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
    · exact re (.r12, 16) (by decide)
    · exact re (.r13, 24) (by decide)
    · exact re (.r14, 32) (by decide)
    · exact re (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have hc : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fme.mono (by simp)).writeW hm _ (hc 0 (by decide))).writeW hm _
        (hc 8 (by decide))).writeW hm _ (hc 16 (by decide))).writeW hm _ (hc 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · change bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarBase _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarBase, encodedValue_spec, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [val4, ge .r8 (by decide), ge .r9 (by decide), ge .r10 (by decide), ge .r11 (by decide),
      kd.1 .r8 (by decide), kd.1 .r9 (by decide), kd.1 .r10 (by decide), kd.1 .r11 (by decide)]
    change val4 (c.gpr .r8) (c.gpr .r9) (c.gpr .r10) (c.gpr .r11) = _
    rw [vc, input]

end VG.Proof.Ed25519.X86_64
