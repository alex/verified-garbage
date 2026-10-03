import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.Contract
import VerifiedGarbage.Proof.Ecdh.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified

/-!
# ECDH over P-256 on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`), so `exchange_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is
never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking:
the only branches are on loop counters, and every address is an argument
plus a constant or a counter, so not even the peer's key (which the
contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64

theorem pre_of {s : State} (h : ecdhX86_64.pre s) : EPre p256 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, -, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h11⟩

theorem post_of {s s' : State} (h : EPost p256 s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 32 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 32 = List.replicate 32 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p256.C (dk p256 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 16 * p256.n)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_x86 (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP256 s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok p256_ok (pre_of hs)
  have hsp : ∀ i ∈ instrs exchangeP256, Taint.clobbers i .rsp = false := by
    have h : exchangeP256.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
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
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)

theorem ecdh_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ecdh_verified :
    Verified X86_64.target exchangeP256 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi) :=
  Verified.of_correct ecdh_x86 ecdh_ct implies

end VG.Proof.Ecdh.X86_64
