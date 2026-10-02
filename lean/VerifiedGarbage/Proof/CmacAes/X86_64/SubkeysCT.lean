import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `rbx` and
`rbp`); the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) K S R
  rbx : s.gpr .rbx = K
  rbp : s.gpr .rbp = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.rcx]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .rdx + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.rdx]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, rbx₁, rbp₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inK _ (by decide)) (inK _ (by decide))
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := cs₁ .rsp (by simp [calleeSaved]) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₁, run₁,
    callPre_of hp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ rsp₁ mem₁ rd₁ wr₁, by rw [rbx₁, hp.rdx], by rw [rbp₁, hp.rcx], rsp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysX86_64.pre s₀)
    (h0' : subkeysX86_64.pre s₀') (hq : subkeysX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := SMid s₀ _ _ _ _) (F₂ := SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨smid_wp hp, smid_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      SMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat s₁ ∧
      SMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.pre, h.2.pre, by rw [h.1.rsp, h.2.rsp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .rbx = s₀.gpr .rdx ∧ s.gpr .rbp = s₀.gpr .rcx)
    (F₂ := fun (s : State) => s.gpr .rbx = s₀.gpr .rdx ∧ s.gpr .rbp = s₀.gpr .rcx) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.1.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.1.rbp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.2.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.2.rbp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .rbx = s₀.gpr .rdx ∧ s₁.gpr .rbp = s₀.gpr .rcx) ∧
      (s₂.gpr .rbx = s₀.gpr .rdx ∧ s₂.gpr .rbp = s₀.gpr .rcx)) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysX86_64.pre subkeysX86_64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64
