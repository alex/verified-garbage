import VerifiedGarbage.Proof.Argon2.X86_64.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.Lit

/-! # Constant time of Argon2 block compression -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64

def initialTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false,
    lens := [1024, 4096], bases := [(.rdx, 0, 0), (.rcx, 1, 0)] }

theorem initial_agree {s t : State} (hs : compressLocal.pre s) (ht : compressLocal.pre t)
    (hp : compressLocal.pub s t) : X86_64.Taint.Agree initialTaint s t := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  have wf : ∀ s, compressLocal.pre s → X86_64.Taint.Wf initialTaint s := by
    intro s hs
    obtain ⟨_, hw, hd, _⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, initialTaint], by simp [hw, hd], ?_⟩, fun p hp => ?_⟩
    · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> dsimp only <;> decide
    · simp only [initialTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ hs, wf _ ht,
    ?_, ?_, ?_⟩
  · simp only [initialTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hs.2.1, ht.2.1, p3, p4]
  · intro sl h; simp [initialTaint] at h
  · intro sl h; simp [initialTaint] at h
  · intro r h; simp [initialTaint] at h

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.X86_64.compress :=
  VG.Taint.constantTime (A := taint) initialTaint (fun _ _ hs ht hp => initial_agree hs ht hp)
    (by taint_decide)

end VG.Proof.Argon2.X86_64
