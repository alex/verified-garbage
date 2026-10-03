import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Merged from `Proof.Argon2.X86_64.Lit`. -/
section
/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.X86_64

materialize_code compress := Impl.Argon2.X86_64.compress

end VG.Proof.Argon2.X86_64
end

/-! Merged from `Proof.Argon2.X86_64.Contract`. -/
section
/-! # A local contract for Argon2 block compression -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .rdi, 1024⟩
    let y : Region := ⟨s.gpr .rsi, 1024⟩
    let out : Region := ⟨s.gpr .rdx, 1024⟩
    let scratch : Region := ⟨s.gpr .rcx, 4096⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch
  post s t := blockAt t.mem (s.gpr .rdx) =
    compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (compressContract X86_64.abi) := by
  sig_implies [compressContract, compressSig, compressLocal, X86_64.abi, X86_64.argRegs]
    [satState] using satState

end VG.Proof.Argon2.X86_64
end

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
