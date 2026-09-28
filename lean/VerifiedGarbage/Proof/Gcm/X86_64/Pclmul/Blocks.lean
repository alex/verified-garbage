import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Clmul
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# GHASH with PCLMULQDQ: the instruction groups

Untrusted: everything here is checked by Lean. What each group of
instructions of `Impl.Gcm.X86_64.Pclmul` does to the state, each proved by
one symbolic execution for any registers it is used with.
-/

namespace VG.Proof.Gcm.X86_64.Pclmul

open VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly xInv)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem psrldq8 (v : BitVec 128) : XShiftOp.eval .psrldq v 8 = v >>> 64 := rfl

theorem pslldq8 (v : BitVec 128) : XShiftOp.eval .pslldq v 8 = v <<< 64 := rfl

theorem rev_eq : Impl.Gcm.X86_64.Pclmul.revMask = revMask := rfl

/-- `s'` differs from `s` at most in `rax` and the SSE registers `rs`. -/
structure Only (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem Only.trans {rs rs' : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs' s' s'') :
    Only (rs ++ rs') s s'' :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Only.weaken {rs rs' : List XReg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Only rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- The product registers. -/
def prod (s : State) : Prod := ⟨s.xmm .xmm8, s.xmm .xmm9, s.xmm .xmm10⟩

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Pclmul.zero) s fun s' =>
      prod s' = Prod.zero ∧ Only [.xmm8, .xmm9, .xmm10] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.zero]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_false, eval_pxor, BitVec.xor_self, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (a b : XReg) (s : State) (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10)
    (ha11 : a ≠ .xmm11) (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc a b)) s fun s' =>
      prod s' = (prod s).acc (s.xmm a) (s.xmm b) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.acc]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_true, ite_false, eval_pxor, eval_movdqa, ha8, ha9, ha10, ha11, hb8, hb9,
    hb10, hb11, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [prod, Prod.acc, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (d : XReg) (s : State) (hd8 : d ≠ .xmm8) (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10)
    (hd11 : d ≠ .xmm11) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.reduce d)) s fun s' =>
      s'.xmm d = reduce (prod s) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11, d] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.reduce, Impl.Gcm.X86_64.Pclmul.fold, List.cons_append,
    List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_true, ite_false, eval_pxor, eval_movdqa, hd8, hd9, hd10, hd11, h1,
    Ne.symm hd8,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [psrldq8, pslldq8]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `d ← mul(a, b)`, a block of class `x · a · b`. -/
theorem mul_ok (d a b : XReg) (s : State) (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10)
    (ha11 : a ≠ .xmm11) (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11)
    (hd8 : d ≠ .xmm8) (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10) (hd11 : d ≠ .xmm11)
    (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.mul d a b)) s fun s' =>
      φ (s'.xmm d) = x * φ (s.xmm a) * φ (s.xmm b) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11, d] s s' := by
  rw [Impl.Gcm.X86_64.Pclmul.mul, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (acc_ok a b s₁ ha8 ha9 ha10 ha11 hb8 hb9 hb10 hb11) fun s₂ ⟨p₂, o₂⟩ => ?_
  have e1 : s₂.xmm .xmm1 = poly := by rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1]
  refine WP.mono (reduce_ok d s₂ hd8 hd9 hd10 hd11 e1) fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, φ_reduce, p₂, p₁, Prod.val_acc, Prod.val_zero, zero_add,
      o₁.xmm a (by simp [ha8, ha9, ha10]), o₁.xmm b (by simp [hb8, hb9, hb10])]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

/-- A block, loaded from `[b + d]` into `x` and byte-reversed. -/
theorem ldrev_ok (x : XReg) (b : Reg) (d : Nat) (s : State) (hx : x ≠ .xmm0)
    (h0 : s.xmm .xmm0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad x (at_ b d), .xop (.bin .pshufb x .xmm0)]) s fun s' =>
      s'.xmm x = Spec.Gcm.blockAt s.mem (s.gpr b + BitVec.ofInt 64 (d : Int)) ∧ Only [x] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, ea_at, hin, ite_true, ite_false, Ne.symm hx, h0,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

/-- A 128-bit constant into `x`. -/
theorem const_ok (x : XReg) (c : BitVec 128) (s : State) (hx : x ≠ .xmm12) :
    WP isa (.block (Impl.Gcm.X86_64.Pclmul.const x c)) s fun s' =>
      s'.xmm x = c ∧ Only [x, .xmm12] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.const]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.setReg, ite_true, ite_false, hx, movq_const, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, fun r hr => by simp [hr], rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

/-- `H' = H · x⁻¹` into `xmm3`, from `H` in `xmm7`. -/
theorem hInv_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Pclmul.hInv) s fun s' =>
      x * φ (s'.xmm .xmm3) = φ (s.xmm .xmm7) ∧
      Only [.xmm3, .xmm11, .xmm12, .xmm13, .xmm14] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86_64.Pclmul.hInv, Impl.Gcm.X86_64.Pclmul.const, List.cons_append,
    List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.setReg, ite_true, ite_false, movq_const, eval_movdqa, eval_pxor,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp [hr], rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [show XBinOp.eval .por (XShiftOp.eval .psllq (s.xmm .xmm7) 1)
        (XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) =
        XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
          XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8 from rfl,
      shl1, mask_eq, x_φ_hInv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Gcm.X86_64.Pclmul
