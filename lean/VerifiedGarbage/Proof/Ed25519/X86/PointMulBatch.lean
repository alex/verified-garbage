import VerifiedGarbage.Proof.Ed25519.X86.PointMulCounter

/-! Untrusted: rebuild and consume one batch of sixteen exact powers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem pointMulBatch_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (scalar j : Nat) (p : Spec.Ed25519.Point) (hj : j < 32)
    (hcounter : wd s.mem x 28 = BitVec.ofNat 32 (j + 1))
    (hbits : ∀ i < 16, s.mem (addr x (7168 + (16 * j + i))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * j + i)).toNat)
    (hcheckpoint : tablePoint s.mem x (1024 + 128 * j) = powerPoint p (16 * j))
    (hp : point (env s.mem x) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa pointMulBatch s fun t => BatchKeep x s t ∧
      wd t.mem x 28 = BitVec.ofNat 32 j ∧ isa.eval .ne t = some (!decide (j = 0)) ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * j) ∧ env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (batchBegin_ok hc j hcounter) fun a ⟨ka, ba, ia, fa⟩ => ?_)
  have ca := ka.ctx hc
  have ea := counter28_env hc.fit fa
  refine WP.seq (WP.mono (prepareBatch_ok ca j hj ba (by rw [ea]; exact hd)) fun b ⟨kb, pb, tb, db⟩ => ?_)
  have cb := kb.ctx ca
  have ib := (kb.batch_index ca).trans ia
  have ks := ka.trans (BatchKeep.of_powers ca kb)
  have bits : ∀ i < 16, b.mem (addr x (7168 + (16 * j + i))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * j + i)).toNat :=
    fun i hi => (ks.bit hc _ (by omega)).trans (hbits i hi)
  have tables : ∀ i < 16, tablePoint b.mem x (5120 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hi
    rw [tb i hi, ka.checkpoint hc j hj, hcheckpoint, ← powerPoint_add]
  have pointb : point (env b.mem x) 0 1 2 3 = after scalar p (16 * j + 16) := by
    rw [pb, ea, hp, Nat.mul_add, Nat.mul_one]
  refine WP.seq (WP.mono (accumulate16_ok cb scalar j p hj ib bits tables pointb db)
    fun c ⟨kc, pc, dc⟩ => ?_)
  have cc := kc.ctx cb
  have ic := (kc.word cb 28 (by decide)).trans ib
  refine WP.mono (batchTest_ok cc j hj ic) fun t ⟨kt, mt, zt⟩ => ?_
  refine ⟨ks.trans ((BatchKeep.of_ikeep cb kc).trans (BatchKeep.of_ikeep cc kt)), ?_, zt, ?_, ?_⟩
  · rw [mt]; exact ic
  · rw [mt]; exact pc
  · rw [mt]; exact dc

end VG.Proof.Ed25519.X86
