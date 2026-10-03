import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport

/-! Scratch counters are public by correctness, including after table stores. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem both_wp {P F : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True))
    (hw : ∀ s, P s → WP isa c s F) :
    RelCT isa (fun x y => P x ∧ P y) c (fun x y => F x ∧ F y) :=
  (h.wp (fun x y hp => ⟨hw x hp.1, hw y hp.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

def BatchCTPre (base : Addr) (j : Nat) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1) ∧
    env s.mem base 16 = Spec.Ed25519.d

def BatchCTReady (base : Addr) (j : Nat) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
    env s.mem base 16 = Spec.Ed25519.d ∧ s.gpr .rbx = BitVec.ofNat 64 j

def BatchCTOffset (base : Addr) (j : Nat) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j

theorem begin_ct (base : Addr) (j : Nat) :
    RelCT isa (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      (.block batchBegin) (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  · intro s ⟨hs, hc, hd⟩
    refine WP.mono (batchBegin_ok hs j hc) fun t ⟨tc, tv, tg, tr, tw, tm⟩ => ?_
    refine ⟨⟨(tg _ (by decide)).trans hs.rdi, ?_, hs.nowrap⟩, tv, ?_, tc⟩
    · rw [tw]; exact hs.wr
    · rw [header_env tm]; exact hd

private theorem prepare_ct (base : Addr) (j : Nat) (hj : j < 32) :
    RelCT isa (fun x y => BatchCTReady base j x ∧ BatchCTReady base j y)
      (prepareBatch fld) (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨hs, hc, hd, hr⟩
    refine WP.mono (prepareBatch_ok hs j hj hr hd) fun t ⟨kt, _, _, _⟩ => ?_
    exact ⟨kt.scratch hs, ((tableFrame_outside kt.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans hc⟩

theorem offset_ct (base : Addr) (j : Nat) (hj : j < 32) :
    RelCT isa (fun x y => BatchCTOffset base j x ∧ BatchCTOffset base j y)
      (.block batchBitOffset) (fun x y =>
        (x.gpr .rdi = base ∧ x.gpr .rsi = BitVec.ofNat 64 (16 * j)) ∧
        (y.gpr .rdi = base ∧ y.gpr .rsi = BitVec.ofNat 64 (16 * j))) := by
  apply both_wp
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  · intro s ⟨hs, hc⟩
    refine WP.mono (batchBitOffset_ok hs j hj hc) fun t ⟨tr, kt⟩ => ?_
    exact ⟨(kt.1 _ (by decide)).trans hs.rdi, tr⟩

theorem pointMulBatch_ct (base : Addr) (j : Nat) (hj : j < 32) :
    RelCT isa (fun x y => BatchCTPre base j x ∧ BatchCTPre base j y)
      (pointMulBatch fld) (fun _ _ => True) := by
  rw [pointMulBatch]
  refine VG.RelCT.seq (begin_ct base j) (VG.RelCT.seq (prepare_ct base j hj)
    (VG.RelCT.seq (offset_ct base j hj) (VG.RelCT.seq (R := fun (x y : State) => ∀ r ∈ ([.rdi] : List Reg), x.gpr r = y.gpr r) ?_ ?_)))
  · apply taintRegsFld (τ := Taint.ofRegs [.rdi, .rsi]) _ [.rdi] (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  · apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs h

end VG.Proof.Ed25519.X86_64
