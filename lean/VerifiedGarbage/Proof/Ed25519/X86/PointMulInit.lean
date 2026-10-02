import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame

/-! Checkpoints, identity accumulator and the public batch count. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem constPoint_d (p : Spec.Ed25519.Point) (e : Env) : evalOps (constPointOps p) e 16 = e 16 := rfl

theorem pointMultiplyInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointMultiplyInit count) s fun t => MulKeep x s t ∧
      wd t.mem x 28 = BitVec.ofNat 32 count ∧ point (env t.mem x) 0 1 2 3 = Spec.Ed25519.identity ∧
      (∀ j < count, tablePoint t.mem x (1024 + 128 * j) =
        powerPoint (point (env s.mem x) 0 1 2 3) (16 * j)) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (pointPowers_ok true hc 1024 count (by decide) (by omega) hn0 hn hd)
    fun a ⟨ka, ta, _, ha⟩ => ?_)
  have ca := ka.ctx hc
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) ca) fun b ⟨kb, eb⟩ => ?_)
  have cb := kb.ctx ca
  refine WP.mono (mulCounterInit_ok cb count) fun t ⟨kt, ft, it⟩ => ?_
  have et := counter28_env hc.fit ft
  have bt : BatchKeep x b t := BatchKeep.of_counter cb kt.edi kt.esp kt.rd kt.wr ft
  refine ⟨((MulKeep.of_powers hc ka (by decide) (by omega)).trans
    (MulKeep.of_ikeep ca (IKeep.of_field kb))).trans (MulKeep.of_batch cb bt), it, ?_, ?_, ?_⟩
  · rw [et, eb, constPoint_eval]
  · intro j hj
    rw [bt.checkpoint cb j (by omega), workspace_table (IKeep.of_field kb) ca _ (by omega) (by omega), ta j hj]
    rfl
  · rw [et, eb, constPoint_d, ha 16 (by decide), hd]

end VG.Proof.Ed25519.X86
