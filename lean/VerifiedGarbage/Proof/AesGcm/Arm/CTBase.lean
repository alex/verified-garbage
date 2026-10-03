import VerifiedGarbage.Proof.AesGcm.Arm.Open
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# AES-GCM on ARMv7: constant time, the combinators

Untrusted: everything here is checked by Lean. `CT I c`: two runs of `c` from
states that both satisfy `I` leak the same. The invariants `I` fix what is
public (pointers, lengths, rounds) as parameters and leave the secrets
(memory, the values the state represents) existential, so that the
correctness lemmas, applied to each run, give the invariant of the next
piece (`CT.seq`). Branches are on flags the invariants fix (`CT.ite`);
blocks are checked by the taint analysis from registers the invariants fix
(`CT.taint`, and `CT.argTaint` for blocks that read stack arguments); the
calls are constant time by their own proofs, with the same arguments in both
runs (`CT.gh`, `CT.ctr`).
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- Both runs satisfy `I`. -/
abbrev Both (I : State → Prop) : State → State → Prop := fun s₁ s₂ => I s₁ ∧ I s₂

/-- Two runs from states satisfying `I` leak the same. -/
abbrev CT (I : State → Prop) (c : Prog isa) : Prop := RelCT isa (Both I) c fun _ _ => True

namespace CT

theorem mono {I J : State → Prop} {c : Prog isa} (h : CT I c) (hi : ∀ s, J s → I s) : CT J c :=
  RelCT.mono h (fun _ _ hh => ⟨hi _ hh.1, hi _ hh.2⟩) fun _ _ _ => trivial

theorem seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT J c₂) : CT I (.seq c₁ c₂) :=
  (rel_wp (F := I) (F' := I) h₁ w w).seq h₂

theorem ite {I : State → Prop} {t e : Prog isa} (b : Bool) (hz : ∀ s, I s → s.z = b)
    (ht : b = true → CT I t) (he : b = false → CT I e) : CT I (.ite .eq t e) := by
  have ev : ∀ s, I s → isa.eval .eq s = some b := fun s hs => eval_eq' (hz s hs)
  refine RelCT.ite (fun _ _ h => by rw [ev _ h.1, ev _ h.2]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [ev _ hp.1] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [ev _ hp.1] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

theorem taint {I : State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {h : Taint.Hint VG.Arm.Taint.T}
    (hc : (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs rs) c h).isSome = true) : CT I c :=
  RelCT.taint (A := VG.Arm.taint) _ (fun _ _ hh => Taint.agree_ofRegs (hp _ _ hh.1 hh.2)) hc

/-- A block, with the stack arguments: `n` bytes of them, the same in both runs and apart
from the writable regions. -/
theorem argTaint {I : State → Prop} {c : Prog isa} (rs : List Reg) (n : Nat)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp)
    (hw : ∀ s, I s → s.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, n⟩ r)
    (hm : ∀ s₁ s₂, I s₁ → I s₂ → ∀ k < n, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k))
    {h : Taint.Hint VG.Arm.Taint.T}
    (hc : (VG.Taint.check VG.Arm.taint (argTaint rs n) c h).isSome = true) : CT I c :=
  RelCT.taint (A := VG.Arm.taint) _ (fun _ _ hh => agree_argTaint (hp _ _ hh.1 hh.2) (hsp _ _ hh.1 hh.2)
    (hw _ hh.1) (hw _ hh.2) (hm _ _ hh.1 hh.2)) hc

theorem skip {I : State → Prop} : CT I (.block []) :=
  taint [] (fun _ _ _ _ _ h => by simp at h) (h := .block []) rfl

theorem gh {I : State → Prop}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ H Y D S : BitVec 32, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) : CT I ghFrame :=
  gh_rel fun _ _ hh => h _ _ hh.1 hh.2

theorem ctr {I : State → Prop}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C D S : BitVec 32, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) : CT I ctrFrame :=
  ctr_rel fun _ _ hh => h _ _ hh.1 hh.2

end CT

end VG.Proof.AesGcm.Arm
