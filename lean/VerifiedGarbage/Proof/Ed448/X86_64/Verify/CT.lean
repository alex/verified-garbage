import VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Correct

/-!
# Ed448 verification on x86-64: constant time

Two runs from states that satisfy the contract and agree on its public data
leak the same: the branch on `ctx_len`, the moves and the frame depend only
on the pointers and the lengths; the hashing leaks only the layout
(`hash_tr`); and the calls of `vg_ed448_scalar_reduce` and
`vg_ed448_verify_equation` leak only their pointers (`red_tr`, `eq_tr`).
The contract makes the inputs public too, but no leak depends on them.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## The calls -/

theorem red_tr {Φ : Lay → Mem → State → Prop} :
    RelCT isa (Two I Φ) (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce redArgs)
      fun _ _ => True := by
  have regs : ∀ (L : Lay) g mx m₀ (t t1 : State), Ctx L g mx m₀ t → Moved redArgs t t1 →
      t1.gpr .rdi = L.K ∧ t1.gpr .rsi = L.H ∧ t1.gpr .rdx = L.scr ∧ t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3⟩ := argsIn3 hm.1.1
      rw [hc.sp] at e1 e2
      rw [hc.slot, hc.pScr] at e3
      exact ⟨e1, e2, e3, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine call_tr (by decide) Proof.Ed448.X86_64.scalarReduce_ok Proof.Ed448.X86_64.scalarReduce_ct
    (fun L => [⟨L.H, 114⟩]) (fun L => [⟨L.K, 57⟩, L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce, g1, g2, g3, g4,
      sp_sub8, State.withRegions_rd, State.withRegions_wr]
    refine ⟨trivial, trivial, ?_, ret_k, ret_x hL, k_x' hL, hL.nScr⟩
    have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 8192) (by omega) (by omega)
    rw [H_eq]; simpa only [x0] using this
  · obtain ⟨x1, x2, x3, x4⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp), rsp_ce,
      x1, x2, x3, x4, y1, y2, y3, y4, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, by simp, within_off _ (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨L.FR, by simp, within_off _ (by omega)⟩, w_scr hL (within_self _)]

theorem eq_tr (hv : EqOk) (hct : EqCT) {Φ : Lay → Mem → State → Prop} :
    RelCT isa (Two I Φ) (callA "vg_ed448_verify_equation" Impl.Ed448.X86_64.verifyEquation eqArgs)
      fun _ _ => True := by
  have regs : ∀ (L : Lay) g mx m₀ (t t1 : State), Ctx L g mx m₀ t → Moved eqArgs t t1 →
      t1.gpr .rdi = L.pk ∧ t1.gpr .rsi = L.sig ∧ t1.gpr .rdx = L.K ∧ t1.gpr .rcx = L.scr ∧
        t1.gpr .rsp = L.SP :=
    fun L g mx m₀ t t1 hc hm => by
      obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hm.1.1
      rw [hc.slot, hc.pPk] at e1
      rw [hc.slot, hc.pSig] at e2
      rw [hc.sp] at e3
      rw [hc.slot, hc.pScr] at e4
      exact ⟨e1, e2, e3, e4, (hm.2.gpr (by decide)).trans hc.rsp⟩
  refine call_tr (by decide) hv hct
    (fun L => [L.PK, L.SIG, ⟨L.K, 57⟩]) (fun L => [L.SCR])
    (fun L g mx m₀ t t1 hL hc _ hm => ?_)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 _ _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · obtain ⟨g1, g2, g3, g4, g5⟩ := regs L g mx m₀ t t1 hc hm
    simp only [Proof.Ed448.X86_64.verifyEquationLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), rsp_ce, g1, g2, g3, g4, g5, sp_sub8, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, hL.xPk.symm, hL.xSig.symm, k_x' hL, ret_x hL, hL.nScr⟩
  · obtain ⟨x1, x2, x3, x4, x5⟩ := regs L g₁ mx₁ m₁ a a1 c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5⟩ := regs L g₂ mx₂ m₂ b b1 c₂ f₂
    simp only [Proof.Ed448.X86_64.verifyEquationLocal, gpr_ce _ _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce _ _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce _ _ _ (by decide : Reg.rcx ≠ .rsp), rsp_ce, x1, x2, x3, x4, x5, y1, y2, y3, y4, y5, and_self]
  · refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩
      · exact ⟨L.SIG, List.mem_append_left _ hL.inSig, within_self _⟩
      · exact ⟨L.FR, by simp, within_off _ (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact w_scr hL (within_self _)

/-- The frame's body, after the header. -/
theorem rest_tr (hv : EqOk) (hct : EqCT) :
    RelCT isa (Two I fun _ _ _ => True)
      (.seq hash (.seq (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce redArgs)
        (callA "vg_ed448_verify_equation" Impl.Ed448.X86_64.verifyEquation eqArgs))) fun _ _ => True := by
  have h := two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) hash_tr
    fun L g mx m₀ t hL hc _ => WP.mono (hash_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have r := two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) red_tr
    fun L g mx m₀ t hL hc _ => WP.mono (reduce_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact h.seq (r.seq (eq_tr hv hct))

end

/-! ## The function -/

/-- The public data of the contract, spelled out. -/
structure VPub (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0

theorem vPub_of {s₁ s₂ : State} (h : (Spec.Ed448.verifyContract X86_64.abi 272).pub s₁ s₂) : VPub s₁ s₂ := by
  sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs,
    List.range, List.range.loop] at h
  obtain ⟨a, -, c, d, e, f, g, h, i⟩ := h
  exact ⟨a, c, d, e, f, g, h, i⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VPre s₁) (h₂ : VPre s₂) (h : VPub s₁ s₂) : vlay s₁ = vlay s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [vPk, vCtx, vMsg, vSig, vArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
      h.r9, h.rsp]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [vScr, h.a0]
  simp only [vlay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, e1, e2]

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (x y : State) : Prop :=
  (Spec.Ed448.verifyContract X86_64.abi 272).pre x ∧ (Spec.Ed448.verifyContract X86_64.abi 272).pre y ∧
    (Spec.Ed448.verifyContract X86_64.abi 272).pub x y

/-- After `cmp rdx, 256`. -/
abbrev ACmp (x x1 : State) : Prop :=
  x1.gpr = x.gpr ∧ x1.mem = x.mem ∧ x1.rd = x.rd ∧ x1.wr = x.wr ∧ x1.mxcsr = x.mxcsr ∧
    isa.eval .b x1 = some (decide ((x.gpr .rdx).toNat < 256))

/-- After the moves before the push. -/
abbrev VMov (x x2 : State) : Prop :=
  (x.gpr .rdx).toNat < 256 ∧ ((x2.gpr .r11 = stackArg x 0 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem hdr_spOnly : ∀ i ∈ hdr, SpOnly i := by
  intro i hi
  simp only [hdr, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hi
  rcases hi with ((rfl | rfl | rfl) | ⟨-, rfl⟩) | rfl
  · exact spOnly_nomem (fun _ => rfl) rfl
  · exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩
  · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
  · exact spOnly_nomem (fun _ => rfl) rfl
  · exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩

theorem verify_ct (hv : EqOk) (hct : EqCT) :
    ConstantTime isa (Spec.Ed448.verifyContract X86_64.abi 272).pre (Spec.Ed448.verifyContract X86_64.abi 272).pub
      verify := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => (Spec.Ed448.verifyContract X86_64.abi 272).pre s₁ ∧
      (Spec.Ed448.verifyContract X86_64.abi 272).pre s₂ ∧ (Spec.Ed448.verifyContract X86_64.abi 272).pub s₁ s₂) =
      Ghost VP2 (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verify
  -- `cmp rdx, 256`.
  have hcmp := ghost_step (P := VP2) (A := fun x a => a = x) (B := ACmp) (c := .block [.alu .cmp .rdx (.imm 256)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact (vPub_of hxy.2.2).rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨cmp_ok _, cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, (vPub_of hxy.2.2).rdx]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := ghost_step (P := VP2) (A := fun x a => ACmp x a ∧ (x.gpr .rdx).toNat < 256) (B := VMov)
      (c := .block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)])
      (block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact (vPub_of hxy.2.2).rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, (Spec.Ed448.verifyContract X86_64.abi 272).pre x → ACmp x a →
            (x.gpr .rdx).toNat < 256 → WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) a
              (VMov x) := fun hx f h8 =>
          WP.mono (verifyMov_ok (vPre_of hx) f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, (vPub_of hxy.2.2).rdx, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact (vPub_of hxy.2.2).rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, VMov x s₁ ∧ a = pushed regs s₁
    let B : State → State → Prop := fun x t => (x.gpr .rdx).toNat < 256 ∧ Ctx (vlay x) x.gpr x.mxcsr x.mem t
    have hh := ghost_step (P := VP2) (A := A) (B := B) (c := .block hdr)
      (block_rsp_tr hdr_spOnly
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), (vPub_of hxy.2.2).rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, (Spec.Ed448.verifyContract X86_64.abi 272).pre x → A x a →
            WP isa (.block hdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := vPre_of hx
          have hL := vlay_ok h f.1
          have hc := entry_ctx hL (by rw [f.2.2.1 _ (by decide), vlay_B]) (f.2.2.2.1.trans rfl)
            (f.2.2.2.2.trans rfl) f.2.1.1 (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide))
            (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide)) (f.2.2.1 _ (by decide))
          exact WP.mono (hdr_ok hL hc) fun t ⟨hc', _⟩ =>
            ⟨f.1, hc'.congr (fun r hr _ => f.2.2.1 r (cs_tmp r hr)) f.2.1.2.2.2 f.2.1.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hh (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨_, cb⟩⟩ => ?_)
      (rest_tr (I := fun _ _ _ => True) hv hct)
    have hx := vPre_of hxy.1
    have e := vlay_eq hx (vPre_of hxy.2.1) (vPub_of hxy.2.2)
    exact ⟨vlay x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, vlay_ok hx h8x, trivial, ca, e ▸ cb,
      trivial, trivial⟩
  · exact block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact (vPub_of hxy.2.2).rsp

end VG.Proof.Ed448.X86_64.Verify
