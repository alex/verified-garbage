import VerifiedGarbage.Proof.MlKem.X86.TopSeq

/-!
# ML-KEM on x86 (32-bit): the calls of three and four arguments, with their arguments

As `TopSeq.lean`, for `vg_mlkem_multiply_ntts`, `vg_mlkem_sample_ntt`,
`vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem mulC_piece (oa oo fa fo ga go sa so : Nat)
    (hc : (Y.okW ⟨oa, oo, 1024⟩ && Y.ok ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ && Y.sep ⟨oa, oo, 1024⟩ ⟨ga, go, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩ &&
      Y.sep ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) = true) (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨oa, oo, 1024⟩ ++
      ptrTo Y.sc .ecx ⟨fa, fo, 1024⟩ ++ ptrTo Y.sc .edx ⟨ga, go, 1024⟩ ++ ptrTo Y.sc .edi ⟨sa, so, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (multiplyNTTs (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (mulC Y.sc ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨oa, oo, 1024⟩ ∧
      s₁.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨sa, so, 1024⟩) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (mul_call oa oo fa fo ga go sa so hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2.1, m₁ ▸ (hA s₀ s hp ha).2.2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc]
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ h1 fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ h2 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h3).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem sampleC_piece (da dO aa ao ca co : Nat)
    (hc : (Y.ok ⟨da, dO, 34⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨ca, co, 2048⟩ && Y.sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 34⟩ ⟨ca, co, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true) (hN : 88 ≤ Y.stk)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨da, dO, 34⟩ ++
      ptrTo Y.sc .ecx ⟨aa, ao, 1024⟩ ++ ptrTo Y.sc .edx ⟨ca, co, 2048⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 72]) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun iters => sampleNTT iters (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (sampleC Y.sc ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      s₁.gpr .ecx = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨ca, co, 2048⟩)
      (fun s₀ s hp h => ?_) hA tt)
    (sample_call da dO aa ao ca co hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃⟩ => ⟨h₁, e₁, e₂, e₃⟩)
      (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, _, m₁, _⟩ ⟨s', ha', _, m₁', _⟩ => by
        rw [m₁, m₁']; exact hseed s₀ s₀' s s' hp hp' hq ha ha')
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ out => ?_)
  · simp only [List.append_assoc]
    rw [← List.append_nil (ptrTo Y.sc .edx _)]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ (Lay.okW_iff.mp h1).1 fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ (Lay.okW_iff.mp h2).1 fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  · rw [m₁] at fr out
    exact hQ s₀ s s' hp ha h' fr r₁ out

theorem ceC_piece (d : Nat) (hd : d ∈ compressWidths) (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ceC Y.sc d ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 d ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s₁.gpr .edi = BitVec.ofNat 32 (32 * d)) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (ce_call d hd fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ (Lay.okW_iff.mp h1).1 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem ddC_piece (d : Nat) (hd : d ∈ compressWidths) (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ddC Y.sc d ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s₁.gpr .edx = BitVec.ofNat 32 d ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩) (fun s₀ s hp h => ?_) hA tt)
    (dd_call d hd ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃, e₄⟩ => ⟨h₁, e₁, e₂, e₃, e₄⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h1).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top
