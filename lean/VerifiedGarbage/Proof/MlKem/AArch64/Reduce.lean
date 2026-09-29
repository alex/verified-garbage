import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: reductions modulo `q`

Untrusted: everything here is checked by Lean. The conditional subtraction
`csub` (`Impl/MlKem/AArch64/Basic.lean`), for any registers.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)
open VG.Proof.MlKem (condSub q_eq)

theorem not_mem_one {a b : Reg} (h : a ≠ b) : a ∉ [b] := by simpa using h

theorem not_mem_two {a b c : Reg} (h₁ : a ≠ b) (h₂ : a ≠ c) : a ∉ [b, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h₁, h₂⟩

/-- The arithmetic of `csub`: for `x < 2q`, `x - q`, plus `q` if it is
negative, is `x mod q`. -/
theorem csub_arith {x : Nat} (hx : x < 2 * q) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 q) +
      ((BitVec.ofNat 64 x - BitVec.ofNat 64 q) >>> 63) * BitVec.ofNat 64 q).toNat = condSub x := by
  rw [q_eq] at hx
  rw [BitVec.toNat_add, BitVec.toNat_mul, toNat_lsr, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, condSub, q_eq]
  split <;> omega

/-- `csub d t qr`: `d ← d mod q` for `d < 2q`. -/
theorem csub_ok {d t qr : Reg} (hdt : d ≠ t) (hdq : d ≠ qr) (htq : t ≠ qr)
    {is : List Instr} {s : State} {Q : State → Prop} {x : Nat}
    (hx : x < 2 * q) (hd : (s.gpr d).toNat = x) (hq : (s.gpr qr).toNat = q)
    (k : ∀ s', Only [d, t] s s' → (s'.gpr d).toNat = condSub x → WP isa (.block is) s' Q) :
    WP isa (.block (csub d t qr ++ is)) s Q := by
  refine wp_sub fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => wp_madd fun s₃ h₃ e₃ => ?_
  refine k s₃ (((h₁.trans h₂).trans h₃).mono (by simp)) ?_
  have hd' : s.gpr d = BitVec.ofNat 64 x := by
    rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hq' : s.gpr qr = BitVec.ofNat 64 q := by
    rw [← hq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have q₂ : s₂.gpr qr = s.gpr qr := by
    rw [h₂.get qr (not_mem_one htq.symm), h₁.get qr (not_mem_one hdq.symm)]
  have d₂ : s₂.gpr d = s₁.gpr d := h₂.get d (not_mem_one hdt)
  rw [e₃, d₂, e₂, q₂, e₁, hd', hq']
  exact csub_arith hx

end VG.Proof.MlKem.AArch64
