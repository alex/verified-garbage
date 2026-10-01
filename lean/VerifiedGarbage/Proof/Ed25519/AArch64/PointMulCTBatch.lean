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

def BatchCTOffset (base : Addr) (j : Nat) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j

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

end VG.Proof.Ed25519.AArch64
