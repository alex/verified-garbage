import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep

/-! Untrusted: save and reload the verification equation's packed points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scratchAddr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (o : Nat) (ho : o < 8192) :
    WP isa (.block (scratchAddr o)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 o := by
  refine wp_movw fun u hu => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest (by decide)), by rw [ht.mem, hu.mem], ?_⟩
  rw [ht.gpr]
  change u.gpr .r0 + u.gpr .r12 = _
  rw [hu.other _ (by decide), hc.r0, hu.gpr]
  refine congrArg (b + ·) (BitVec.eq_of_toNat_eq ?_)
  rw [movw_nat (by omega), toNat_imm (by omega)]

theorem pointTableWrite_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1600 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep b o 128 s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ tablePoint t.mem b o = point (env s.mem b) 0 1 2 3 := by
  unfold pointTableWrite
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc o (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointToTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tk⟩ => ?_
  exact ⟨⟨(ur.mono (by decide)).trans (tk.rest.mono (by decide)), by rw [← um]; exact TableFrame.table tk.frame⟩,
    tk.lim ho hn (um ▸ hl), (tk.env ho hn).trans (congrArg (fun m => env m b) um),
    tp.trans (congrArg (fun m => point (env m b) 0 1 2 3) um)⟩

theorem pointTableRead_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1600 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem b i = env s.mem b i := by
  unfold pointTableRead
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc o (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointFromTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tl, tk⟩ => ?_
  refine ⟨(AccKeep.of_rest ur (by decide) um).trans (AccKeep.of_table tk (by decide) (by decide)), tl,
    tp.trans (congrArg (fun m => tablePoint m b o) um), fun i hi => ?_⟩
  exact (tk.high i hi).trans (congrArg (fun m => env m b i) um)

end VG.Proof.Ed25519.Arm
