import VerifiedGarbage.Proof.Ed25519.X86.PointTable

/-! A public table index is multiplied by the point's 128 bytes. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem tableAddr_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (off j : Nat)
    (hj : j < 2 ^ 25) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block (tableAddr off)) s fun t =>
      Keep s t ∧ t.mem = s.mem ∧ t.gpr .edx = x + BitVec.ofNat 32 (off + 128 * j) := by
  refine Wp.wp_mov fun s₁ h₁ => Wp.wp_movi fun s₂ h₂ => wp_mul fun s₃ h₃ => ?_
  refine Wp.wp_add fun s₄ h₄ _ => Wp.wp_addi fun s₅ h₅ => Wp.wp_mov fun s₆ h₆ => WP.block_nil ?_
  have hk : Keep s s₆ := (updKeep h₁).trans ((updKeep h₂).trans (h₃.keep.trans
    ((updKeep h₄).trans ((updKeep h₅).trans (updKeep h₆)))))
  have hv : s₃.gpr .eax = BitVec.ofNat 32 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    change v s₃ .eax = _
    rw [h₃.eax]
    simp only [v, h₂.other .eax (by decide), h₁.gpr, hb, h₂.gpr, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show j < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm j 128)
  refine ⟨hk, by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_⟩
  rw [h₆.gpr, h₅.gpr, h₄.gpr, hv, h₃.other .edi (by decide) (by decide),
    h₂.other .edi (by decide), h₁.other .edi (by decide), hc.edi]
  rw [BitVec.add_comm (BitVec.ofNat 32 (128 * j)) x, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.add_comm (128 * j) off]

end VG.Proof.Ed25519.X86
