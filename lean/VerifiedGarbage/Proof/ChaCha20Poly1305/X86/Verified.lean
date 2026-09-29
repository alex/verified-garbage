import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.CT

/-!
# ChaCha20-Poly1305 on x86 (32-bit): `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time (from `CT.lean`), and a state satisfying the
precondition.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86

/-- Memory whose five argument slots (at `0x5004`) hold `0x1000`, `0x2000`,
`0`, `0x3000` and `0`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x20 else if a = 0x5011 then 0x30 else 0

/-- A state satisfying the precondition (with no additional data and no
data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩, ⟨0x5004, 20⟩]

theorem sat_pre : preX86 sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 0x2000 := by decide
  have a2 : arg sat 2 = 0 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have e : argAddr sat 0 = 0x5004 := by decide
  simp only [preX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

theorem seal_verified : Verified X86.target Impl.ChaCha20Poly1305.X86.«seal» sealX86 :=
  ⟨fun s hs => by
    obtain ⟨t, s', he, h, hpost⟩ := seal_correct (APre.of s hs)
    exact ⟨t, s', he, h, hpost⟩, seal_ct, ⟨sat, sat_pre⟩⟩

theorem open_verified : Verified X86.target Impl.ChaCha20Poly1305.X86.«open» openX86 :=
  ⟨fun s hs => by
    obtain ⟨t, s', he, h, hpost⟩ := open_correct (APre.of s hs)
    exact ⟨t, s', he, h, hpost⟩, open_ct, ⟨sat, sat_pre⟩⟩

end VG.Proof.ChaCha20Poly1305.X86
