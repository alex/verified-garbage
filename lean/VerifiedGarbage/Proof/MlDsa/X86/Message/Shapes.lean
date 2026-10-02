import VerifiedGarbage.Proof.MlDsa.X86.Message.Entry
import VerifiedGarbage.Proof.MlDsa.X86.Message.Pre

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: the layouts' shapes

Untrusted: everything here is checked by Lean. The contracts' public data,
spelled out (`SPub`, `VPub`), and the layouts of `sign_message` and
`verify_message` (`slay`, `vlay`) meet what the proofs of the check, the
entry and the hashes need (`sShape`, `vShape`).
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- The public data of `signMessageContract p X86.abi 136`. -/
structure SPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : signMessageLeak p (bytesAt s.mem ((arg s 0).setWidth 64) p.skLen)
      (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
      (bytesAt s.mem ((arg s 5).setWidth 64) 32) =
    signMessageLeak p (bytesAt s'.mem ((arg s' 0).setWidth 64) p.skLen)
      (bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat)
      (bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat) (bytesAt s'.mem ((arg s' 5).setWidth 64) 32)
  args : ∀ i < 8, arg s i = arg s' i

theorem spub_of {p : Params} {s s' : State} (h : (signMessageContract p X86.abi 136).pub s s') : SPub p s s' := by
  sig_pub [signMessageContract, signMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The public data of `verifyMessageContract p X86.abi 132`. -/
structure VPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : leakBytes (bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen ++
      bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat ++
      bytesAt s.mem ((arg s 5).setWidth 64) p.sigLen) =
    leakBytes (bytesAt s'.mem ((arg s' 0).setWidth 64) p.pkLen ++
      bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat ++
      bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat ++ bytesAt s'.mem ((arg s' 5).setWidth 64) p.sigLen)
  args : ∀ i < 7, arg s i = arg s' i

theorem vpub_of {p : Params} {s s' : State} (h : (verifyMessageContract p X86.abi 132).pub s s') : VPub p s s' := by
  sig_pub [verifyMessageContract, verifyMessageSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6

/-- The leaf's frame, below the stack pointer on entry. -/
theorem frame_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    (⟨(E0 s).setWidth 64 - 16#64, 16⟩ : Region) = below (s.gpr .esp) 16 := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem sShape {p : Params} (hp : p ∈ params) : Shape (SPre p) (SPub p) (slay p) 7 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 7 < 8; decide
  E _ _ := rfl
  ok _ h₀ h8 := slay_ok hp h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega,
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega⟩
  fit _ h₀ := by show _ + 4 + 4 * 8 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega)]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  n5 _ _ := by show 5 ≤ 8; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 7 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [slay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)], by simp only [Lay.X32, slay, hq.args 7 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

theorem vShape {p : Params} (hp : p ∈ params) : Shape (VPre p) (VPub p) (vlay p) 6 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 6 < 7; decide
  E _ _ := rfl
  ok _ h₀ h8 := vlay_ok hp h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega,
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega⟩
  fit _ h₀ := by show _ + 4 + 4 * 7 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega)]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  n5 _ _ := by show 5 ≤ 7; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 6 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [vlay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide)], by simp only [Lay.X32, vlay, hq.args 6 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

end VG.Proof.MlDsa.X86.Message
