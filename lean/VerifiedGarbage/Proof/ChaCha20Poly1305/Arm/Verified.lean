import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Correct

/-!
# ChaCha20-Poly1305 on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from
`Correct.lean`), constant time, and a state satisfying the precondition.

Constant time relates two runs from states that agree on the public data
(`RelCT`), part by part. The taint analysis does not analyse frames, so it
runs on the code before the frame around `vg_poly1305_finalize` (`sealMain`,
`openMain`) and after it (`sealEnd`, `openEnd`), through the callees' code:
it knows `r7`–`r11` for public after each call because every callee saves
them in memory at known offsets of the context, which it tracks, and
restores them, and `r7` for the base of the context once it is set from the
callee's pointer that the callee keeps. The frame itself leaks only
addresses computed from the stack pointer, and `vg_poly1305_finalize` is
constant time (`RelCT.frame`, `RelCT.call`), given what the correctness
proof shows of the states on either side of it in each run (`RelCT.wp`):
the same stack pointer and arguments, whose values are computed from public
data only.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (macData)

/-! ## The taint on entry -/

/-- The initial taint: `r0`–`r3` (`ctx`, `aad`, `aad_len`, `data`) and the
stack argument (`len`) are public, and `r0` is the base of the context, the
first writable region (the second is the data). -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [1024, 0], bases := [(.r0, 0)],
    argLen := 4 }

theorem wf₀ {s : State} (hp : APre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hc := hp.fit_c; have hd := hp.fit_d; have hs := hp.spfit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.c_d, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.c_arg.symm
    · exact hp.d_arg.symm
  · intro p hp'; simp [τ₀] at hp'

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : APre s₁) (h₂ : APre s₂) (hpub : pubArm s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.wr, h₂.wr]
    simp only [ctxR, dR, cx, dp, cP, dP, L, p0, p3, a0]
  · simp only [τ₀] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-! ## The frame -/

theorem push_eq' {s a : State} (h : isa.push (.push [.r1, .r12]) s = some a) : a = pushed [.r1, .r12] s := by
  rw [push_pushed rfl (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

/-- `vg_poly1305_finalize`'s view of the state after the push, with the
regions given in terms of the stack pointer `sp`. -/
theorem finView_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) (P O Sc : BitVec 32) :
    (pushed [.r1, .r12] s).callEntry.withRegions [⟨State.addr sp - 8, 8⟩] (finWr P O Sc) = finView s P O Sc := by
  rw [← h]

/-- The frame around `vg_poly1305_finalize`, in two runs whose states before
it are `x₁` and `x₂`, with the same stack pointer, pointers and message
length. -/
theorem frame_ct {s₁ s₂ : State} (hp₁ : APre s₁) (hp₂ : APre s₂) (hpub : pubArm s₁ s₂)
    {F : State → State → Prop}
    (hF : ∀ x₁ x₂, F x₁ x₂ → Inv s₁ x₁ ∧ Inv s₂ x₂ ∧ x₁.gpr .r0 = cP s₁ ∧ x₁.gpr .r1 = ptr s₁ tagOff ∧
      x₁.gpr .r12 = ptr s₁ scrOff ∧ x₂.gpr .r0 = cP s₂ ∧ x₂.gpr .r1 = ptr s₂ tagOff ∧
      x₂.gpr .r12 = ptr s₂ scrOff ∧ Proof.Poly1305.countArm x₁ = Proof.Poly1305.countArm x₂) :
    RelCT isa F finalize fun _ _ => True := by
  obtain ⟨psp, p0, -, -, -, -⟩ := hpub
  refine RelCT.frame (fun x₁ x₂ h => by
    obtain ⟨i₁, i₂, -⟩ := hF x₁ x₂ h
    rw [i₁.sp, i₂.sp, psp]) ?_
  refine RelCT.call (k := Proof.Poly1305.finalizeArm) Proof.Poly1305.Arm.Fin.finalize_verified.1
    Proof.Poly1305.Arm.Fin.finalize_verified.2.1 [⟨State.addr s₁.sp - 8, 8⟩]
    (finWr (cP s₁) (ptr s₁ tagOff) (ptr s₁ scrOff)) fun a b ⟨x₁, x₂, h, pa, pb⟩ => ?_
  obtain ⟨i₁, i₂, a0, a1, a12, b0, b1, b12, hc⟩ := hF x₁ x₂ h
  rw [push_eq' pa, push_eq' pb]
  have f₁ := fin_args hp₁ i₁ a0 a1 a12
  have f₂ := fin_args hp₂ i₂ b0 b1 b12
  have e2 : cP s₂ = cP s₁ := p0.symm
  have ep : ∀ k, ptr s₂ k = ptr s₁ k := fun k => by simp only [ptr, e2]
  rw [ep, ep, e2] at f₂
  rw [finView_eq i₁.sp, finView_eq (i₂.sp.trans psp.symm)]
  refine ⟨f₁.pre, f₂.pre, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [fin_nsp, fin_nsp, i₁.sp, i₂.sp, psp]
  · rw [fin_ng _ _ _ _ .r0 (by decide), fin_ng _ _ _ _ .r0 (by decide), a0, b0, e2]
  · have := (BitVec.append_32_inj hc).2
    rw [fin_ng _ _ _ _ .r2 (by decide), fin_ng _ _ _ _ .r2 (by decide), this]
  · have := (BitVec.append_32_inj hc).1
    rw [fin_ng _ _ _ _ .r3 (by decide), fin_ng _ _ _ _ .r3 (by decide), this]
  · rw [f₁.arg0 _ (fin_nsp _ _ _ _) rfl, f₂.arg0 _ (fin_nsp _ _ _ _) rfl]
  · rw [f₁.arg1 _ (fin_nsp _ _ _ _) rfl, f₂.arg1 _ (fin_nsp _ _ _ _) rfl]
  · have e : finRd x₁ = [⟨State.addr s₁.sp - 8, 8⟩] := by simp [finRd, i₁.sp]
    rw [← e]; exact f₁.cov
  · exact f₁.covW
  · have e : finRd x₂ = [⟨State.addr s₁.sp - 8, 8⟩] := by simp [finRd, i₂.sp, psp]
    rw [← e]; exact f₂.cov
  · exact f₂.covW

/-! ## After the frame -/

/-- `open`'s taint after the frame: the context (the base of the first
writable region), the data and its length are public. -/
def τB : VG.Arm.Taint.T :=
  { regs := .ofList [.r7, .r10, .r11], flags := false, lens := [1024, 0], bases := [(.r7, 0)] }

theorem wfB {s₀ s : State} (hp : APre s₀) (h : Inv s₀ s) : VG.Arm.Taint.Wf τB s := by
  have hc := hp.fit_c; have hd := hp.fit_d
  refine ⟨fun _ => ⟨by simp [h.wr, hp.wr, τB], ?_, ?_⟩, ?_, fun h => absurd h (by decide), ?_⟩
  · simp only [h.wr, hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.c_d, fun _ h => h.elim⟩
  · simp only [h.wr, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τB, List.mem_singleton] at hp'
    subst hp'; simp [VG.Arm.Taint.region, h.wr, hp.wr, h.regs.r7]
  · intro p hp'; simp [τB] at hp'

theorem agreeB {s₁ s₂ a b : State} (hp₁ : APre s₁) (hp₂ : APre s₂) (hpub : pubArm s₁ s₂) (ha : Inv s₁ a)
    (hb : Inv s₂ b) : VG.Arm.Taint.Agree τB a b := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfB hp₁ ha, wfB hp₂ hb,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => by simp [τB] at hk⟩
  · simp only [τB, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ha.regs.r7, hb.regs.r7, cP, cP, p0]
    · rw [ha.regs.r10, hb.regs.r10, dP, dP, p3]
    · rw [ha.regs.r11, hb.regs.r11, a0]
  · rw [ha.wr, hb.wr, hp₁.wr, hp₂.wr]
    simp only [ctxR, dR, cx, dp, cP, dP, L, p0, p3, a0]

/-! ## Seal -/

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub Impl.ChaCha20Poly1305.Arm.«seal» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp₁ := APre.of s₁ h₁
  have hp₂ := APre.of s₂ h₂
  have hlen : (macData (A s₁) (Ct s₁)).length = (macData (A s₂) (Ct s₂)).length := by
    obtain ⟨-, -, -, p2, -, a0⟩ := hpub
    rw [length_macData, length_macData, length_encrypt, length_encrypt]
    simp only [VG.Proof.Poly1305.length_bytesAt, AL, L, p2, a0]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sealMain fun a b => True ∧ PreFs s₁ a ∧ PreFs s₂ b :=
    (RelCT.taint (A := taint) τ₀ (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact agree₀ hp₁ hp₂ hpub) (by taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨sealMain_ok hp₁, sealMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ PreFs s₁ a ∧ PreFs s₂ b) finalize
      fun a b => True ∧ PostFs s₁ a ∧ PostFs s₂ b :=
    (frame_ct hp₁ hp₂ hpub fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨finalize_seal_ok hp₁ h.2.1, finalize_seal_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ PostFs s₁ a ∧ PostFs s₂ b) (.block sealEnd) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r7]) (fun a b h => VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.2.1.inv.regs.r7, h.2.2.inv.regs.r7, cP, cP, hpub.2.1]) (by taint_decide)
  exact ((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Open -/

theorem open_ct : ConstantTime isa openArm.pre openArm.pub Impl.ChaCha20Poly1305.Arm.«open» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp₁ := APre.of s₁ h₁
  have hp₂ := APre.of s₂ h₂
  have hlen : (macData (A s₁) (D s₁)).length = (macData (A s₂) (D s₂)).length := by
    obtain ⟨-, -, -, p2, -, a0⟩ := hpub
    rw [length_macData, length_macData]
    simp only [VG.Proof.Poly1305.length_bytesAt, AL, L, p2, a0]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) openMain fun a b => True ∧ PreFo s₁ a ∧ PreFo s₂ b :=
    (RelCT.taint (A := taint) τ₀ (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact agree₀ hp₁ hp₂ hpub) (by taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨openMain_ok hp₁, openMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ PreFo s₁ a ∧ PreFo s₂ b) finalize
      fun a b => True ∧ PostFo s₁ a ∧ PostFo s₂ b :=
    (frame_ct hp₁ hp₂ hpub fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨finalize_open_ok hp₁ h.2.1, finalize_open_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ PostFo s₁ a ∧ PostFo s₂ b) openEnd fun _ _ => True :=
    RelCT.taint (A := taint) τB (fun a b h => agreeB hp₁ hp₂ hpub h.2.1.inv h.2.2.inv) (by taint_decide)
  exact ((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying the precondition (with no additional data and no
data): `ctx` at `0x1000`, `aad` at `0x2000`, `data` at `0x3000`, the stack
argument at `0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x3000, 0⟩]

theorem sat_pre : preArm sat := by
  have e0 : stackArg sat 0 = 0 := by decide
  simp only [preArm, e0]
  refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
    by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat, stackArgAddr, State.addr] at h₁ h₂
    bv_omega

theorem seal_verified : Verified Arm.target Impl.ChaCha20Poly1305.Arm.«seal» sealArm := by
  refine ⟨fun s hs => ?_, seal_ct, ⟨sat, sat_pre⟩⟩
  obtain ⟨t, s', he, h, hpost⟩ := seal_correct (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

theorem open_verified : Verified Arm.target Impl.ChaCha20Poly1305.Arm.«open» openArm := by
  refine ⟨fun s hs => ?_, open_ct, ⟨sat, sat_pre⟩⟩
  obtain ⟨t, s', he, h, hpost⟩ := open_correct (APre.of s hs)
  exact ⟨t, s', he, h, hpost⟩

end VG.Proof.ChaCha20Poly1305.Arm
