import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `x19` and
`x20`); the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) K S R
  x19 : s.gpr .x19 = K
  x20 : s.gpr .x20 = S
  sp : s.sp = s₀.sp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x3]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x2]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, x20₁, _, sp₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inS _ (by decide)) (inK _ (by decide)) (inK _ (by decide))
  exact WP.of_runBlock ⟨s₁, run₁,
    callPre_of hp x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ mem₁ rd₁ wr₁, by rw [x19₁, hp.x2], by rw [x20₁, hp.x3], sp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysAArch64.pre s₀)
    (h0' : subkeysAArch64.pre s₀') (hq : subkeysAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := SMid s₀ _ _ _ _) (F₂ := SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨smid_wp hp, smid_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      SMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₁ ∧
      SMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.1.x20], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.2.x20], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x2 ∧ s₁.gpr .x20 = s₀.gpr .x3 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .x19 = s₀.gpr .x2 ∧ s₂.gpr .x20 = s₀.gpr .x3 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2.2, h.2.2.2, q5]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysAArch64.pre subkeysAArch64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64
