import VerifiedGarbage.Proof.Ed25519.Arm.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.Arm.BitMask
import VerifiedGarbage.Proof.Ed25519.Arm.PointSelect

/-! Untrusted: add one exact table power and select with its scalar bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem select_flip {α : Type} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) : c = if bit then b else a := by
  cases bit with
  | false => exact hc.trans hd
  | true => exact hc.trans he

theorem pointAccumulate_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (j : Nat) (hj : j < 16) (h11 : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : env s.mem b 16 = Spec.Ed25519.d) (bit : Bool)
    (hbit : s.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat) :
    WP isa pointAccumulate s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 =
        (if bit then Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3)
          (tablePoint s.mem b (5696 + 128 * j)) else point (env s.mem b) 0 1 2 3) ∧
      env t.mem b 16 = env s.mem b 16 := by
  refine WP.seq (WP.mono (prepareAdd_ok hc hl j hj h11) fun u ⟨ku, lu, up, uq, us, ud⟩ => ?_)
  refine WP.seq (WP.mono (pointAdd_ok (ku.ctx hc) lu (ud.trans hd)) fun v ⟨kv, lv, vp, vh⟩ => ?_)
  have ks := ku.trans (AccKeep.of_keep kv)
  have hvc : v.gpr .r11 = BitVec.ofNat 32 j := (ks.rest.gpr _ (by decide)).trans h11
  have hvb : v.mem (State.addr b + BitVec.ofNat 64 (32 + j)) = BitVec.ofNat 8 bit.toNat :=
    (ks.bit j hj).trans hbit
  have vs : point (env v.mem b) 17 18 19 20 = point (env s.mem b) 0 1 2 3 :=
    (point_congr (e := env v.mem b) (f := env u.mem b) 17 18 19 20 (vh 17 (by decide)) (vh 18 (by decide))
      (vh 19 (by decide)) (vh 20 (by decide))).trans us
  have vp' : point (env v.mem b) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (tablePoint s.mem b (5696 + 128 * j)) :=
    vp.trans (congrArg₂ Spec.Ed25519.pointAdd up uq)
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (ks.ctx hc) j hj hvc bit hvb) fun w ⟨kw, mw, mask⟩ => ?_
  refine WP.mono (pointSelect_ok (kw.ctx (ks.ctx hc)) (by rw [mw]; exact lv) mask)
    fun t ⟨kt, lt, tp, td⟩ => ?_
  refine ⟨ks.trans (kw.trans (AccKeep.of_keep kt)), lt, ?_, ?_⟩
  · exact select_flip bit tp
      ((congrArg (fun m => point (env m b) 17 18 19 20) mw).trans vs)
      ((congrArg (fun m => point (env m b) 0 1 2 3) mw).trans vp')
  · exact td.trans ((congrArg (fun m => env m b 16) mw).trans ((vh 16 (by decide)).trans ud))

end VG.Proof.Ed25519.Arm
