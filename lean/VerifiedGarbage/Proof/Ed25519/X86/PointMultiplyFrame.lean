import VerifiedGarbage.Proof.Ed25519.X86.PointMulCounter

/-! Merged from `Proof.Ed25519.X86.PointMulBatch`. -/
section
/-! Rebuild and consume one batch of sixteen exact powers. -/
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
end

/-! Complete point multiplication preserves API pointers and scalar bits. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 24 7144] s.mem t.mem

theorem MulKeep.refl (x : BitVec 32) (s : State) : MulKeep x s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
theorem MulKeep.ctx {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr
theorem MulKeep.trans {x : BitVec 32} {s t u : State} (h : MulKeep x s t) (k : MulKeep x t u) :
    MulKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem MulKeep.of_powers {x : BitVec 32} {s t : State} {o n : Nat} (hc : Ctx x s)
    (h : PowersKeep x o n s t) (ho : 24 ≤ o) (hn : o + n ≤ 7168) : MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  refine ⟨sub x 24 7144, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact sub_sub hc.fit ho (by omega) (by omega)

theorem MulKeep.of_batch {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : BatchKeep x s t) :
    MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  refine ⟨sub x 24 7144, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)

theorem MulKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : IKeep x s t) :
    MulKeep x s t := MulKeep.of_powers hc (PowersKeep.of_ikeep h 24 0) (by decide) (by decide)

theorem MulKeep.bit {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (sub x (7168 + i) 1).Disjoint (sub x 24 7144)) _ (Region.contains_self _ _)

theorem MulKeep.word {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 24) : wd t.mem x o = wd s.mem x o :=
  wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

end VG.Proof.Ed25519.X86
