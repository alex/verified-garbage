import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified

/-!
# ECDSA verification over P-256 on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Proof.P256.good` for its
group law), so `verify_ok` gives the contract's postcondition; the
callee-saved registers are restored, `rsp` is never written, and every store
is to `scratch`, which the return address is apart from (`abiPreserved`).
Constant time by taint tracking: the only branches are on loop counters, and
every address is an argument plus a constant or a counter, so only the
pointers affect timing (the contract would let the key, the hash and the
signature affect it too).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h7⟩

theorem verify_x86 (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok p256_ok Proof.P256.good (pre_of hs)
  have hsp : ∀ i ∈ instrs verifyP256, Taint.clobbers i .rsp = false := by
    have h : verifyP256.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      exact hrs) (by decide)

theorem verify_ct : ConstantTime isa verifyX86_64.pre verifyX86_64.pub verifyP256 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem verify_verified :
    Verified X86_64.target verifyP256 (Spec.Ecdsa.P256.inst.verifyContract X86_64.abi) :=
  Verified.of_correct verify_x86 verify_ct implies

end VG.Proof.Ecdsa.Verify.X86_64
