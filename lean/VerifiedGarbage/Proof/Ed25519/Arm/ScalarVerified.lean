import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarLoop
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Merged from `Proof.Ed25519.Arm.ScalarMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarSetup`. -/
section
/-! The scalar-reduction wrapper's local contract and scratch setup. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarReduceLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let wide : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧
      wide.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 64)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

structure ScalarReducePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 64⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_wide : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 64⟩
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  wide_ws : (⟨State.addr (s.gpr .r1), 64⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

theorem ScalarReducePre.of {s : State} (h : scalarReduceLocal.pre s) : ScalarReducePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem scalarReduceSetup_ok {s : State} (h : ScalarReducePre s) :
    WP isa (.block scalarReduceSetup) s fun t =>
      Ctx (s.gpr .r2) t ∧ t.gpr .r12 = s.gpr .r1 ∧
      ScalarSaved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) 32 = s.gpr .r0 ∧
      Rest [.r0, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 36⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  rw [scalarReduceSetup]
  refine WP.append (scalarSave_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t :=
    (ku.mono (by decide)).trans ((hv.rest _).trans ((hw'.rest (by decide)).trans (ht.rest (by decide))))
  have mt : t.mem = u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (s.gpr .r0) := by
    rw [ht.mem, hw'.mem, hv.mem, gu]
  refine ⟨⟨?_, h.f2, by rw [kt.wr]; exact hw⟩, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hw'.gpr, hv.gpr, gu]
  · rw [ht.gpr, hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 32) (n := 4) (k := 4) (by omega) (by omega) (by omega)) (by decide)]
    exact su i hi
  · rw [mt, Mem.readW_writeW_self32]
  · rw [mt]
    exact (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! The complete scalar-reduction function, including its ABI and bytes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalar_region_sub {b : BitVec 32} {r : Region} (h : r ∈ scalarRegions b) :
    r.Sub ⟨State.addr b, 8192⟩ := by
  simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact Offset.sub_base _ (by decide)

theorem scalarReduce_correct {s : State} (h : ScalarReducePre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  have hR : SR = 256 := rfl
  have hD : SD = 320 := rfl
  unfold scalarReduce
  refine WP.seq (WP.mono (scalarReduceSetup_ok h) fun u ⟨hcu, pu, su, ou, ku, fu⟩ => ?_)
  have wide : (⟨State.addr (s.gpr .r1), 64⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (scalarReduceEngine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base wide (by omega) (by omega))
    (fun r hr => h.wide_ws.sub_right (scalar_region_sub hr))) fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (.inl (by change _ ≤ _; omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) 32 = s.gpr .r0 := by
    rw [kv.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), ou]
    simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine WP.mono (scalarFinish_ok (kv.ctx hcu) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kv.rest.gpr _ (by decide), ku.gpr _ (by decide)]
  · change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.encodeLE 32 _
    rw [bt, vv]
    apply congrArg (Spec.Ed25519.encodeLE 32)
    apply congrArg (fun bs => Spec.Ed25519.decodeLE bs % Spec.Ed25519.L)
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 64⟩) (fun r hr => ?_) (by decide : 64 ≤ 2 ^ 64)
      (List.mem_range.mp hn)
    rw [List.mem_singleton.mp hr]
    exact h.wide_ws.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code scalarReduce
end VG.Impl.Ed25519.Arm
end

/-! The complete 512-bit scalar reducer meets the merged specification,
preserves the ABI, and keeps all scalar bytes secret. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct (ScalarReducePre.of hs)

def scalarTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [32, 8192], bases := [(.r2, 1)] }

theorem scalarTaint_wf {s : State} (h : scalarReduceLocal.pre s) : VG.Arm.Taint.Wf scalarTaint s := by
  have hp := ScalarReducePre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarTaint], ?_, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f2
  · intro p hm
    simp only [scalarTaint, List.mem_singleton] at hm
    subst hm
    simp [VG.Arm.Taint.region, hp.wr]

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) scalarTaint ?_ (by taint_decide)
  intro s t hs ht ⟨_, h0, h1, h2⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarTaint_wf hs, scalarTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [scalarTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [(ScalarReducePre.of hs).wr, (ScalarReducePre.of ht).wr, h0, h2]

theorem scalarReduce_verified : Verified Arm.target scalarReduce
    (Spec.Ed25519.scalarReduceContract Arm.abi) :=
  Verified.of_correct scalarReduce_ok scalarReduce_ct (by
    sig_implies [Spec.Ed25519.scalarReduceContract, Spec.Ed25519.scalarReduceSig,
      Spec.Ed25519.scratchWords, scalarReduceLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [scalarSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scalarSatState)

end VG.Proof.Ed25519.Arm
