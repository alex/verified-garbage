import VerifiedGarbage.Proof.Ed25519.Arm.PointMulLoop

/-! Untrusted: full scalar multiplication agrees with the reviewed specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem constPoint_d (p : Spec.Ed25519.Point) (e : Env) : evalOps (constPointOps p) e 16 = e 16 := rfl

theorem pointMultiply_ok {b ptr : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (count scalar : Nat) (hi : MulInput b ptr count scalar s) (hn : 0 < count)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (pointMultiply count) s fun t => MulKeep b 1600 6144 s t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul scalar (point (env s.mem b) 0 1 2 3) := by
  let p := point (env s.mem b) 0 1 2 3
  have hs : scalar < 2 ^ (16 * count) := by
    rw [← hi.value]
    exact val16_lt (fun k _ => packedLimb_lt _ _ k)
  refine WP.seq (WP.mono (pointPowers_ok true hc hl 1600 count (by decide)
    (by have := hi.bound; omega) hn hi.bound hd) fun a ⟨al, ats, _, ah, ak⟩ => ?_)
  have kam : MulKeep b 1600 6144 s a := (MulKeep.of_powers ak).mono (by decide) (by have := hi.bound; omega)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (kam.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have kum : MulKeep b 1600 6144 s u := kam.trans (MulKeep.of_powers (PowersKeep.of_keep uk))
  have ud : env u.mem b 16 = Spec.Ed25519.d := by rw [ue, constPoint_d, ah 16 (by decide), hd]
  have up : point (env u.mem b) 0 1 2 3 = after scalar p (16 * count) :=
    ((congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)).trans
      (after_top scalar (16 * count) p hs).symm
  have ut : ∀ j < count, tablePoint u.mem b (1600 + 128 * j) = powerPoint p (16 * j) := by
    intro j hj
    have := hi.bound
    exact (workspace_tablePoint uk.frame (by omega) (by omega)).trans (ats j hj)
  refine WP.seq (wp_movw fun v hv => ?_)
  have vc : v.gpr .r11 = BitVec.ofNat 32 count := by
    apply BitVec.eq_of_toNat_eq
    rw [hv.gpr, movw_nat (by have := hi.bound; omega), toNat_imm (by have := hi.bound; omega)]
  have kvm : MulKeep b 1600 6144 s v := kum.trans
    (MulKeep.of_rest (hv.rest (ws := [.r11]) (by decide)) (by decide) hv.mem)
  refine WP.mono (counterStore_ok (kvm.ctx hc) count vc) fun w ⟨wr, wf, wc⟩ => ?_
  have kwm : MulKeep b 1600 6144 s w := kvm.trans (MulKeep.of_counter wr (by decide) wf)
  have we : env w.mem b = env u.mem b := (smallFrame_env wf (by decide)).trans
    (congrArg (fun m => env m b) hv.mem)
  have wl : AllLim w.mem b := smallFrame_lim wf (by decide) (by rw [hv.mem]; exact ul)
  refine WP.mono (pointMulLoop_ok (kwm.ctx hc) wl count scalar p
    (hi.keep kwm (by decide) (by decide)) hn ((congrFun we 16).trans ud)
    ((congrArg (fun e => point e 0 1 2 3) we).trans up) wc (fun j hj => ?_))
    fun t ⟨tk, tl, td, tp⟩ => ⟨kwm.trans (tk.mono (by decide) (by decide)), tl, td, tp⟩
  have := hi.bound
  exact (smallFrame_table wf (by decide) (by omega) (by omega)).trans
    ((congrArg (fun m => tablePoint m b (1600 + 128 * j)) hv.mem).trans (ut j hj))

end VG.Proof.Ed25519.Arm
