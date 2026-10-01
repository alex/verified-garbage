import VerifiedGarbage.Proof.Ed25519.Arm.BatchFrame
import VerifiedGarbage.Proof.Ed25519.Arm.MulInput

/-! Untrusted: one outer batch consumes exactly sixteen scalar bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointMulBody_ok {b ptr : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (count scalar j : Nat) (p : Spec.Ed25519.Point) (hi : MulInput b ptr count scalar s)
    (hj : j < count) (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1))
    (ht : tablePoint s.mem b (1600 + 128 * j) = powerPoint p (16 * j)) :
    WP isa pointMulBody s fun t => MulKeep b 5696 2048 s t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = after scalar p (16 * j) ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j ∧ t.z = decide (j = 0) := by
  have hj32 : j < 32 := Nat.lt_of_lt_of_le hj hi.bound
  refine WP.seq (WP.mono (batchStart_ok hc j hcj) fun a ⟨ar, af, av, ac⟩ => ?_)
  have ak : MulKeep b 5696 2048 s a := MulKeep.of_counter ar (by decide) af
  have al := smallFrame_lim af (by decide) hl
  have ae := smallFrame_env af (by decide)
  have ad : env a.mem b 16 = Spec.Ed25519.d := (congrFun ae 16).trans hd
  refine WP.seq (WP.mono (prepareBatch_ok (ak.ctx hc) al j hj32 av ad) fun u ⟨uk, ul, up, ut, ud⟩ => ?_)
  have kum : MulKeep b 5696 2048 s u := ak.trans (MulKeep.of_powers uk)
  have ui := hi.keep kum (by decide) (by decide)
  have uc := (uk.counter (by decide) (by decide)).trans ac
  have upt : point (env u.mem b) 0 1 2 3 = after scalar p (16 * j + 16) :=
    up.trans ((congrArg (fun e => point e 0 1 2 3) ae).trans
      (hp.trans (congrArg (after scalar p) (by omega))))
  have utt : ∀ i < 16, tablePoint u.mem b (5696 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hib
    exact (ut i hib).trans ((congrArg (fun q => powerPoint q i)
      ((smallFrame_table af (by decide) (by omega) (by omega)).trans ht)).trans
      (powerPoint_add p (16 * j) i).symm)
  refine WP.seq (WP.mono (batchBits_ok (kum.ctx hc) count j hj ui.bound ui.fit ui.pointer uc ui.readable)
    fun v ⟨vr, vf, vb⟩ => ?_)
  have kv : MulKeep b 5696 2048 u v := MulKeep.of_bits vr (by decide) vf
  have ve := smallFrame_env vf (by decide)
  have vl := smallFrame_lim vf (by decide) ul
  have vbits : ∀ i < 16, v.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (scalarBit scalar (16 * j + i)).toNat := by
    intro i hib
    exact (vb i hib).trans (congrArg (fun x => BitVec.ofNat 8 (scalarBit x (16 * j + i)).toNat) ui.value)
  refine WP.seq (WP.mono (accumulate16_ok (kv.ctx (kum.ctx hc)) vl (16 * j) scalar p vbits
    ((congrFun ve 16).trans ud) ((congrArg (fun e => point e 0 1 2 3) ve).trans upt)
    (fun i hib => (smallFrame_table vf (by decide) (by omega) (by omega)).trans (utt i hib)))
    fun w ⟨wl, wp, wd, wk⟩ => ?_)
  have kwm : MulKeep b 5696 2048 s w := kum.trans (kv.trans (MulKeep.of_loop wk))
  have wc := wk.counter.trans ((bitsFrame_counter vf).trans uc)
  refine WP.mono (batchTest_ok (kwm.ctx hc) j hj32 wc) fun t ⟨tr, tm, tz⟩ => ?_
  exact ⟨kwm.trans (MulKeep.of_rest tr (by decide) tm), tm ▸ wl,
    (congrArg (fun m => env m b 16) tm).trans wd,
    (congrArg (fun m => point (env m b) 0 1 2 3) tm).trans wp,
    (congrArg (fun m => m.readW (State.addr b + BitVec.ofNat 64 56) 32) tm).trans wc, tz⟩

end VG.Proof.Ed25519.Arm
