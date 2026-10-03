import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar

/-!
# ECDSA on x86-64: the result

`finish` writes `r ‖ s` big-endian to `out`, or zeros, by the flag's mask,
returns the flag's low bit, and restores the callee-saved registers
(`finish_ok`). The stores are outside the working space, so it keeps its
numbers and the saved registers (`Outside.unch_far`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

/-- Bytes that changed only in a region apart from the working space. -/
theorem _root_.VG.Proof.Mont.X86_64.Outside.unch_far {q base : Addr} {len : Nat} {m m' : Mem}
    (h : Outside q 0 len m m') (hd : Region.Disjoint ⟨base, size⟩ ⟨q, len⟩) :
    Unch base [(size, 2 ^ 64)] m m' := by
  intro x hx
  have hx' := hx _ (List.mem_singleton_self _)
  have hlt := (x - base).isLt
  refine h x (Or.inr (Nat.le_of_not_lt fun hl => ?_))
  simp only [ofs] at hx' hl
  exact hd x (show (x - base).toNat + 1 ≤ size by omega) (show (x - q).toNat + 1 ≤ len by omega)

/-- The bytes of a range apart from the one that changed. -/
theorem bytesAt_keep {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p k = Spec.Ecdsa.bytesAt m p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact keep_of_disjoint' h hd hl hi hk

theorem movRcx_mem_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rcx (.mem (sc d))]) s fun s' =>
      s'.gpr .rcx = word s.mem base d ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    State.load64, ea_sc, RegUpd.gpr_setReg, ite_true, hs.rdi, ld_sc hs hd,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem raxBit_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)]) s fun s' =>
      s'.gpr .rax = s.gpr .rcx &&& 1 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨by rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem mask_bit (b : Bool) :
    ((if b then BitVec.allOnes 64 else 0) &&& 1 : BitVec 64).setWidth 32 = if b then 1 else 0 := by
  cases b <;> decide

theorem finish_eq (c : Cfg) : c.finish = ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (storeBE c.n .r14 0 (c.sl RR) ++ (storeBE c.n .r14 (8 * c.n) (c.sl SS) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved))) := by
  simp only [Cfg.finish, List.append_assoc]; rfl

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 8 ≤ 48 := by decide

theorem Saved.unch {base : Addr} {g : Reg → BitVec 64} {m m' : Mem}
    (h : Spill.Saved m base g Cfg.saved) {W : List (Nat × Nat)} (hW : ∀ w ∈ W, 48 ≤ w.1)
    (hu : Unch base W m m') : Spill.Saved m' base g Cfg.saved := fun p hp => by
  have := saved_lt p hp
  exact (hu.word (d := p.2) (fun w hw => Or.inl (by have := hW w hw; omega)) (by omega)).trans (h p hp)

/-- The result, the return value and the callee-saved registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hr14 : s.gpr .r14 = out) (hw : (⟨out, 16 * c.n⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 16 * c.n⟩ ⟨base, size⟩)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (16 * c.n) =
        (if b then toBytes (8 * c.n) (sv c base s RR) ++ toBytes (8 * c.n) (sv c base s SS)
          else List.replicate (16 * c.n) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have h7 := hc.n7
  have hn0 := hc.n0
  have hn := hs.nowrap
  have hRR := sl_le c h7 (i := RR) (by decide)
  have hSS := sl_le c h7 (i := SS) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h0 : ∀ e, out + BitVec.ofNat 64 0 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 e := fun e =>
    congrArg (· + BitVec.ofNat 64 e) (BitVec.add_zero out)
  have h8 : ∀ e, out + BitVec.ofNat 64 (8 * c.n) + BitVec.ofNat 64 e =
      out + BitVec.ofNat 64 (8 * c.n + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + 8 * c.n ≤ 16 * c.n →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d : Nat}, d + 8 * c.n ≤ 16 * c.n →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, 8 * c.n⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hr14₁ : s₁.gpr .r14 = out := by rw [k₁.1 _ (by decide), hr14]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok hs₁ (dst := .r14) (d := 0) (a := c.sl RR) (by decide) b
    (by rw [e₁, hf]) hRR (fun e he => ⟨_, by rw [k₁.2.2.2]; exact hw, by
      rw [hr14₁, h0]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr14₁]; exact hdsc hRR (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hr14₁] at e₂ O₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far (hscd (d := 0) (by omega))
  have hr14₂ : s₂.gpr .r14 = out := by rw [k₂.gpr _ (by decide), hr14₁]
  have hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have ss₂ : wordsVal s₂.mem base (c.sl SS) c.n = sv c base s SS := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok hs₂ (dst := .r14) (d := 8 * c.n) (a := c.sl SS) (by decide) b
    hrcx₂ hSS (fun e he => ⟨_, by rw [k₂.wr, k₁.2.2.2]; exact hw, by
      rw [hr14₂, h8]; exact Offset.contains_base out (by omega) (by omega)⟩)
    (by rw [hr14₂]; exact hdsc hSS (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr14₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 8 * c.n) (by omega))
  have hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hrcx₂]
  have first : Spec.Ecdsa.bytesAt s₃.mem out (8 * c.n) =
      if b then toBytes (8 * c.n) (sv c base s RR) else List.replicate (8 * c.n) 0 := by
    rw [bytesAt_keep O₃ (Offset.base_disjoint out (Nat.le_refl _) (by omega)) (by omega) (by omega)]
    have e₂' := e₂
    rw [(BitVec.add_zero out : out + BitVec.ofNat 64 0 = out)] at e₂'
    rw [e₂', hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hsv₄ : Spill.Saved s₄.mem base g Cfg.saved := by
    rw [k₄.2.1]
    have h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (hm₁ ▸ hsv) h48 U₂) h48 U₃
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₄ (by decide) (fun p hp => ?_)
    (by rw [hs₄.rdi]; exact hsv₄)) fun s₅ ⟨g₅, r₅, m₅, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₄.rdi]; exact ⟨_, List.mem_append_right _ hs₄.wr, hs₄.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine ⟨?_, ?_, g₅, fun r hr => ?_⟩
  · rw [m₅, k₄.2.1, show 16 * c.n = 8 * c.n + 8 * c.n by omega, bytesAt_add, first, e₃, ss₂]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_add]
    · simp only [ite_true]
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₅ _ hra, e₄, hrcx₃, mask_bit]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [r₅ r (by simp [Cfg.saved, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      k₄.1 r (by simp [hr.1]), k₃.gpr r (by simp [hr.1]), k₂.gpr r (by simp [hr.1]),
      k₁.1 r (by simp [hr.2.1])]

end VG.Proof.Ecdsa.X86_64
