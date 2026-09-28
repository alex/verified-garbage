import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# ChaCha20-Poly1305 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time, and a state satisfying the precondition.

The taint analysis runs through the callees' code: it knows `x21`–`x25`
(the context, the data, the additional data and their lengths) for public
after each call because no callee writes them (unlike `x19` and `x20`, which
`vg_chacha20_xor` restores from memory, and which the analysis therefore
treats as secret afterwards).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64

/-- The public registers on entry: the pointers and the lengths. -/
def τ₀ : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]

theorem agree₀ {s₁ s₂ : State} (hpub : pubAArch64 s₁ s₂) : VG.AArch64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [τ₀, VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no additional data and no
data). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩]

theorem sat_pre : preAArch64 sat := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

theorem seal_verified : Verified AArch64.target Impl.ChaCha20Poly1305.AArch64.«seal» sealAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ⟨sat, sat_pre⟩⟩
  · obtain ⟨t, s', he, h, hpost⟩ := seal_correct (APre.of s hs)
    exact ⟨t, s', he, h, hpost⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem open_verified : Verified AArch64.target Impl.ChaCha20Poly1305.AArch64.«open» openAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ⟨sat, sat_pre⟩⟩
  · obtain ⟨t, s', he, h, hpost⟩ := open_correct (APre.of s hs)
    exact ⟨t, s', he, h, hpost⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

end VG.Proof.ChaCha20Poly1305.AArch64
