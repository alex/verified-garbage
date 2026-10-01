import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Input
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.NextCT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Space

/-! # H′: public input bounds and constant-time absorption -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure OutputReady (s : State) : Prop where
  space : Space s (s.gpr .r15).toNat
  positive : 1 ≤ (s.gpr .r15).toNat
  bound : (s.gpr .r15).toNat < 2 ^ 32

theorem output_stable : Stable OutputReady where
  ready _ h := ⟨h.space.work, h.space.stackWork⟩
  keeps s t h k := by
    have n := k.regs .r15 (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [n]; exact h.space.keeps k
    · rw [n]; exact h.positive
    · rw [n]; exact h.bound

structure FirstReady (s : State) : Prop extends OutputReady s where
  length : (s.gpr .r13).toNat < 2 ^ 32
  data : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr)
  dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩

theorem first_stable : Stable FirstReady where
  ready _ h := output_stable.ready _ h.toOutputReady
  keeps s t h k := by
    have ptr := k.regs .r12 (by decide)
    have len := k.regs .r13 (by decide)
    refine ⟨output_stable.keeps s t h.toOutputReady k, ?_, ?_, ?_, ?_⟩
    · rw [len]; exact h.length
    · rw [ptr, len, k.rd, k.wr]; exact h.data
    · rw [ptr, len, k.rbx]; exact h.dataWork
    · rw [ptr, len, k.rsp]; exact h.stackData

theorem input_ready {s t : State} (ready : FirstReady s) (h : InputArgs s t) : UpdateReady t := by
  have k := h.keeps
  refine ⟨(first_stable.ready _ (first_stable.keeps _ _ ready k)).work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.data, h.size, h.rd, h.wr]; exact ready.data
  · rw [h.data, h.size, k.rbx]; exact ready.dataWork.sub_right (Region.sub_prefix (by decide))
  · rw [h.data, h.size, k.rbx]; exact ready.dataWork.sub_right (Offset.sub_base _ (by decide))
  · rw [k.rbx, k.rsp]; exact ready.space.stackWork
  · rw [h.data, h.size, k.rsp]; exact ready.stackData

theorem absorbInput_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : FirstReady s) :
    WP isa (absorbInput (hash v)) s (Keeps s) := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  exact (update_keeps v u (input_ready h hu)).mono fun _ ht => hu.keeps.trans ht

theorem absorbInput_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (Related FirstReady) (absorbInput (hash v)) (Related FirstReady) := by
  have args := (RelCT.taint (A := taint) (P := Related FirstReady) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block inputArgs) (by taint_decide)).wpDep
    (F := InputArgs) fun s₁ s₂ _ => ⟨inputArgs_ok s₁, inputArgs_ok s₂⟩
  have call := update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, Related FirstReady σ₁ σ₂ ∧ InputArgs σ₁ s₁ ∧ InputArgs σ₂ s₂)
    fun _ _ ⟨_, _, _, hp, h₁, h₂⟩ => by
      exact ⟨input_ready hp.1 h₁, input_ready hp.2.1 h₂,
        by rw [h₁.keeps.rbx, h₂.keeps.rbx]; exact hp.2.2 _ (by decide),
        by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data]; exact hp.2.2 _ (by decide),
        by rw [h₁.size, h₂.size]; exact hp.2.2 _ (by decide),
        by rw [h₁.keeps.rsp, h₂.keeps.rsp]; exact hp.2.2 _ (by decide)⟩
  exact keeps_rel first_stable (args.seq call)
    (fun s₁ s₂ hp => ⟨absorbInput_keeps v s₁ hp.1, absorbInput_keeps v s₂ hp.2.1⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
