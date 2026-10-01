import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport

/-! Untrusted: scratch counters are public by correctness, including after table stores. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem both_wp {P F : State → Prop} {c : Prog isa}
    (h : CT (fun x y => P x ∧ P y) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s F) :
    CT (fun x y => P x ∧ P y) c (fun x y => F x ∧ F y) :=
  (h.wp (fun x y hp => ⟨hw x hp.1, hw y hp.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

def BatchCTPre (base : Addr) (j : Nat) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1) ∧
    env s.mem base 16 = Spec.Ed25519.d

private def BatchCTReady (base : Addr) (j : Nat) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
    env s.mem base 16 = Spec.Ed25519.d ∧ s.gpr .x19 = BitVec.ofNat 64 j

def BatchCTOffset (base : Addr) (j : Nat) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j

private theorem begin_ct (base : Addr) (j : Nat) :
    CT (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      (.block batchBegin) (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y) := by
  apply both_wp
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  · intro s ⟨hs, hc, hd⟩
    refine WP.mono (batchBegin_ok hs j hc) fun t ⟨tc, tv, tg, tr, tw, _, tm⟩ => ?_
    refine ⟨⟨(tg _ (by decide)).trans hs.x0, ?_, hs.nowrap⟩, tv, ?_, tc⟩
    · rw [tw]; exact hs.wr
    · rw [header_env tm]; exact hd

private theorem prepare_ct (base : Addr) (j : Nat) (hj : j < 32) :
    CT (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y)
      prepareBatch (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y) := by
  apply both_wp
  · apply CT.taint (Taint.ofRegs [.x0, .x19]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨hs, hc, hd, hr⟩
    refine WP.mono (prepareBatch_ok hs j hj hr hd) fun t ⟨kt, _, _, _⟩ => ?_
    exact ⟨kt.scratch hs, ((tableFrame_outside kt.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans hc⟩

theorem offset_ct (base : Addr) (j : Nat) (hj : j < 32) :
    CT (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y)
      (.block batchBitOffset) (fun x y =>
        (x.gpr .x0 = base ∧ x.gpr .x1 = BitVec.ofNat 64 (16 * j)) ∧
        (y.gpr .x0 = base ∧ y.gpr .x1 = BitVec.ofNat 64 (16 * j))) := by
  apply both_wp
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  · intro s ⟨hs, hc⟩
    refine WP.mono (batchBitOffset_ok hs j hj hc) fun t ⟨tr, kt⟩ => ?_
    exact ⟨(kt.gpr _ (by decide)).trans hs.x0, tr⟩

theorem pointMulBatch_ct (base : Addr) (j : Nat) (hj : j < 32) :
    CT (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      pointMulBatch (fun _ _ => True) := by
  rw [pointMulBatch]
  refine CT.seq (begin_ct base j) (CT.seq (prepare_ct base j hj)
    (CT.seq (offset_ct base j hj) (CT.seq (R := fun (x y : State) => ∀ r ∈ ([.x0] : List Reg), x.gpr r = y.gpr r) ?_ ?_)))
  · apply CT.taintRegs (τ := Taint.ofRegs [.x0, .x1]) _ [.x0] (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs h

end VG.Proof.Ed25519.AArch64
