import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Impl.EcKey.X86_64

/-!
# Elliptic curve public keys on x86-64: the result

`finish` writes `04 ‖ x ‖ y` big-endian to `out`, or zeros, by the flag's
mask, returns the flag's low bit, and restores the callee-saved registers
(`finish_ok`): the leading byte (`lead_ok`), then the two coordinates as
the signature's `finish` writes `r ‖ s`.
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem ea_r14 (s : State) : s.ea { base := .r14 } = s.gpr .r14 := by
  show s.gpr .r14 + BitVec.ofInt 64 0 = _
  exact BitVec.add_zero _

theorem writeW8_self (m : Mem) (a : Addr) (v : Byte) : m.writeW a v a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem writeW8_outside (m : Mem) (a : Addr) (v : Byte) : Outside a 0 1 m (m.writeW a v) := by
  intro x hx
  have : ¬ (x - a).toNat < 1 := by simp only [ofs] at hx; omega
  simp only [Mem.writeW, Mem.write, Nat.reduceDiv, this, ite_false]

theorem mask4 (b : Bool) :
    (((4 : BitVec 32).setWidth 64 &&& (if b then BitVec.allOnes 64 else 0)).setWidth 8 : Byte) =
      if b then 4 else 0 := by
  cases b <;> decide

/-- `04` (or `0`) to `out`, by the mask in `rcx`. -/
theorem lead_ok {s : State} {out : Addr} (hr14 : s.gpr .r14 = out) (hw : InRegions s.wr out 1) (b : Bool)
    (hc : s.gpr .rcx = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block ([.mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx),
      .store8 { base := .r14, disp := 0 } .rax] : List Instr)) s fun s' =>
      s'.mem out = (if b then 4 else 0) ∧ Outside out 0 1 s.mem s'.mem ∧ KeepRegs [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
    State.store8, ea_r14, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, reduceCtorEq,
    ite_true, ite_false, hr14, hw, hc, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [writeW8_self, mask4], writeW8_outside _ _ _, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem finish_eq (c : Cfg) : Impl.EcKey.X86_64.Cfg.finish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (([.mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx), .store8 { base := .r14, disp := 0 } .rax] :
      List Instr) ++
    (storeBE c.n .r14 1 (c.sl X) ++ (storeBE c.n .r14 (1 + 8 * c.n) (c.sl Impl.EcKey.X86_64.Y) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved)))) := by
  simp only [Impl.EcKey.X86_64.Cfg.finish, List.append_assoc]; rfl

/-- The result, the return value and the callee-saved registers. -/
theorem pkFinish_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hr14 : s.gpr .r14 = out) (hw : (⟨out, 1 + 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 16 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.X86_64.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + 16 * c.n) =
        (if b then 4 :: (toBytes (8 * c.n) (sv c base s X) ++ toBytes (8 * c.n) (sv c base s Impl.EcKey.X86_64.Y))
          else List.replicate (1 + 16 * c.n) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have h7 := hc.n7
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hX := sl_le c h7 (i := X) (by decide)
  have hY := sl_le c h7 (i := Impl.EcKey.X86_64.Y) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h1 : ∀ e, out + BitVec.ofNat 64 1 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 (1 + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have h8 : ∀ e, out + BitVec.ofNat 64 (1 + 8 * c.n) + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (1 + 8 * c.n + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + 8 * c.n ≤ 1 + 16 * c.n →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d k : Nat}, d + k ≤ 1 + 16 * c.n →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, k⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  have hout : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hr14₁ : s₁.gpr .r14 = out := by rw [k₁.1 _ (by decide), hr14]
  rw [WP.block_append_iff]
  have hc0 : (⟨out, 1 + 16 * c.n⟩ : Region).Contains out 1 := by
    have := Offset.contains_base out (d := 0) (n := 1) (k := 1 + 16 * c.n) (by omega) (by omega)
    rwa [hout] at this
  refine WP.mono (lead_ok hr14₁ ⟨_, by rw [k₁.2.2.2]; exact hw, hc0⟩ b (by rw [e₁, hf]))
    fun s₂ ⟨e₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far (by have := hscd (d := 0) (k := 1) (by omega); rwa [hout] at this)
  have hr14₂ : s₂.gpr .r14 = out := by rw [k₂.gpr _ (by decide), hr14₁]
  have hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have x₂ : wordsVal s₂.mem base (c.sl X) c.n = sv c base s X := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok hs₂ (dst := .r14) (d := 1) (a := c.sl X) (by decide) b
    hrcx₂ hX (fun e he => ⟨_, by rw [k₂.wr, k₁.2.2.2]; exact hw, by
      rw [hr14₂, h1]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr14₂]; exact hdsc hX (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr14₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 1) (by omega))
  have hr14₃ : s₃.gpr .r14 = out := by rw [k₃.gpr _ (by decide), hr14₂]
  have hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hrcx₂]
  have y₃ : wordsVal s₃.mem base (c.sl Impl.EcKey.X86_64.Y) c.n = sv c base s Impl.EcKey.X86_64.Y := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok hs₃ (dst := .r14) (d := 1 + 8 * c.n) (a := c.sl Impl.EcKey.X86_64.Y) (by decide) b
    hrcx₃ hY (fun e he => ⟨_, by rw [k₃.wr, k₂.wr, k₁.2.2.2]; exact hw, by
      rw [hr14₃, h8]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr14₃]; exact hdsc hY (by omega))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hr14₃] at e₄ O₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have U₄ := O₄.unch_far (hscd (d := 1 + 8 * c.n) (by omega))
  have hrcx₄ : s₄.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₄.gpr _ (by decide), hrcx₃]
  have lead : Spec.Ecdsa.bytesAt s₄.mem out 1 = [if b then 4 else 0] := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
      bytesAt_keep O₃ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, hout, e₂]
  have first : Spec.Ecdsa.bytesAt s₄.mem (out + BitVec.ofNat 64 1) (8 * c.n) =
      if b then toBytes (8 * c.n) (sv c base s X) else List.replicate (8 * c.n) 0 := by
    rw [bytesAt_keep O₄ (Offset.disjoint out (by omega) (by omega) (by omega)) (by omega) (by omega), e₃, x₂]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hsv₅ : Spill.Saved s₅.mem base g Cfg.saved := by
    rw [k₅.2.1]
    have h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (Saved.unch (hm₁ ▸ hsv) h48 U₂) h48 U₃) h48 U₄
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₅ (by decide) (fun p hp => ?_)
    (by rw [hs₅.rdi]; exact hsv₅)) fun s₆ ⟨g₆, r₆, m₆, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₅.rdi]; exact ⟨_, List.mem_append_right _ hs₅.wr, hs₅.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine ⟨?_, ?_, g₆, fun r hr => ?_⟩
  · rw [m₆, k₅.2.1, bytesAt_add, show 16 * c.n = 8 * c.n + 8 * c.n by omega, bytesAt_add, lead, first,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, e₄, y₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_add]; rfl
    · simp only [ite_true]; rfl
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₆ _ hra, e₅, hrcx₄, mask_bit]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [r₆ r (by simp [Cfg.saved, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      k₅.1 r (by simp [hr.1]), k₄.gpr r (by simp [hr.1]), k₃.gpr r (by simp [hr.1]),
      k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2.1])]

end VG.Proof.EcKey.X86_64
