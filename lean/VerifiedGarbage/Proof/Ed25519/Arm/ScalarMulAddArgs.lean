import VerifiedGarbage.Impl.Ed25519.Arm.ScalarMulAdd
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.TCB.Arm.Target

/-! Preserve the input pointers and callee-saved registers before arithmetic. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ScalarArgs (b : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (State.addr b + BitVec.ofNat 64 (32 + 4 * i)) 32 = g (scalarArgReg i)

theorem scalarStoreArgs_ok {b : BitVec 32} {s : State} (hp : s.gpr .r12 = b)
    (hfit : b.toNat + 8192 ≤ 2 ^ 32) (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarStoreArgs) s fun t => ScalarArgs b s.gpr t.mem ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ Rest [] s t := by
  refine wp_range_flatMap (M := isa)
    (fun n t => (∀ i < n, t.mem.readW (State.addr b + BitVec.ofNat 64 (32 + 4 * i)) 32 =
      s.gpr (scalarArgReg i)) ∧ Frame [⟨State.addr b + BitVec.ofNat 64 32, 4 * n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ Rest [] s t)
    (fun n t hn ⟨hval, hf, hg, hk⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨fun _ h => by omega, Frame.refl _ _, rfl, Rest.refl _ _⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (32 + 4 * n)) (by omega)
    (by rw [hg, hp]; exact addr_add (by omega))
    (by rw [hk.wr]; exact in_base hw (by omega) (by omega)) fun u hu => WP.block_nil ?_
  refine ⟨fun i hi => ?_, ?_, by rw [hu.gpr, hg], hk.trans (hu.rest _)⟩
  · rw [hu.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hval i hi
    · rw [Mem.readW_writeW_self32, hg]
  · rw [hu.mem]
    exact (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem scalar_ldrSp {s : State} {is : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (k : ∀ t, Upd s t .r12 (stackArg s 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r12 0 :: is)) s Q := by
  refine WP.cons (s' := s.setReg .r12 (stackArg s 0)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32,
    BitVec.add_zero, hr, Option.map_some]
  simp [stackArg, stackArgAddr]

theorem scalarMulAddArgs_ok {s : State}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (hfit : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarMulAddArgs) s fun t =>
      Ctx (stackArg s 0) t ∧ ScalarSaved (State.addr (stackArg s 0)) s.gpr t.mem ∧
      ScalarArgs (stackArg s 0) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (stackArg s 0), 48⟩] s.mem t.mem := by
  rw [scalarMulAddArgs, List.append_assoc, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine scalar_ldrSp hr fun u hu => ?_
  refine WP.append (scalarSave_ok hu.gpr hfit (hu.wr ▸ hw)) fun v ⟨sv, fv, gv, kv⟩ => ?_
  refine WP.append (scalarStoreArgs_ok (by rw [gv]; exact hu.gpr) hfit
    (by rw [kv.wr, hu.wr]; exact hw)) fun w ⟨aw, fw, gw, kw⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t := (hu.rest (by decide)).trans
    ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans (ht.rest (by decide))))
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, ?_, ?_, kt, ?_⟩
  · rw [ht.gpr, gw, gv, hu.gpr]
  · have sn : ∀ i < 8, scalarSavedReg i ≠ .r12 := by decide
    intro i hi
    rw [ht.mem, fw.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), sv i hi]
    · exact hu.other _ (sn i hi)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · have an : ∀ i < 4, scalarArgReg i ≠ .r12 := by decide
    intro i hi
    rw [ht.mem, aw i hi, gv]
    exact hu.other _ (an i hi)
  · rw [ht.mem, ← hu.mem]
    exact (fv.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)

end VG.Proof.Ed25519.Arm
