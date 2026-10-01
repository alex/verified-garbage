import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target

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
