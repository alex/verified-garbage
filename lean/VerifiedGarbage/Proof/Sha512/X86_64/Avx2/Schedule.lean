import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Impl.Sha512.X86_64.Avx2
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# SHA-512 with AVX2 on x86-64: the message schedule of one lane

Each 256-bit instruction of the schedule acts on the two 128-bit lanes alike,
so it is proved once, on one lane (`xupd`): the next two words of a block's
schedule from its previous sixteen.
-/

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (Word Block W ssig0 ssig1)

/-- Words `2i` (in quadword 0) and `2i+1` (in quadword 1) of the schedule of `M`. -/
def pair (M : Block) (i : Nat) : BitVec 128 := W M (2 * i + 1) ++ W M (2 * i)

/-! ## The instructions, on quadwords -/

theorem qword_append_0 (hi lo : Word) : qword (hi ++ lo) 0 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add,
    decide_true, Bool.true_and, hi', ite_true]

theorem qword_append_1 (hi lo : Word) : qword (hi ++ lo) 1 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_one,
    decide_eq_true hi', Bool.true_and, show ¬ 64 + i < 64 by omega, ite_false,
    show 64 + i - 64 = i by omega]

theorem psrlq_eq (hi lo : Word) (n : BitVec 8) (h : n.toNat < 64) :
    XShiftOp.eval .psrlq (hi ++ lo) n = (hi >>> n.toNat) ++ (lo >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false, qword_append_0, qword_append_1]

theorem psllq_eq (hi lo : Word) (n : BitVec 8) (h : n.toNat < 64) :
    XShiftOp.eval .psllq (hi ++ lo) n = (hi <<< n.toNat) ++ (lo <<< n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false, qword_append_0, qword_append_1]

theorem pxor_eq (a b c d : Word) : XBinOp.eval .pxor (a ++ b) (c ++ d) = (a ^^^ c) ++ (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, BitVec.getLsbD_xor, BitVec.getLsbD_append]
  split <;> rfl

theorem paddq_eq (a b c d : Word) : XBinOp.eval .paddq (a ++ b) (c ++ d) = (a + c) ++ (b + d) := by
  simp only [XBinOp.eval, qword_append_0, qword_append_1]

theorem alignRight_8 (a b c d : Word) : alignRight (a ++ b) (c ++ d) 8 = b ++ c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [alignRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    decide_eq_true hi, Bool.true_and, Nat.zero_add, show (8 : BitVec 8).toNat * 8 = 64 from rfl]
  by_cases h1 : i < 64
  · simp only [h1, ite_true, show 64 + i < 128 by omega, show ¬ 64 + i < 64 by omega, ite_false,
      show 64 + i - 64 = i by omega]
  · simp only [h1, ite_false, show ¬ 64 + i < 64 + 64 by omega, show 64 + i - (64 + 64) = i - 64 by omega,
      show i - 64 < 64 by omega, ite_true]

theorem xor_left_comm (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

/-- A rotation as the xor of a shift each way. -/
theorem rotateRight_eq_xor (x : Word) {n : Nat} (h0 : 0 < n) (h : n < 64) :
    x.rotateRight n = x >>> n ^^^ x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [Proof.Sha512.getLsbD_rotateRight _ _ hi]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    decide_eq_true hi, Bool.true_and]
  by_cases hl : i < 64 - n
  · rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm, decide_eq_true hl]
    simp only [Bool.not_true, Bool.false_and, Bool.xor_false]
  · rw [BitVec.getLsbD_of_ge x (n + i) (by omega), decide_eq_false hl, Bool.not_false, Bool.true_and,
      Bool.false_xor]
    exact congrArg x.getLsbD (by omega)

/-- `σ₀`, as `schedule` computes it: rotations by 1 and 8 as shifts each way, and a shift by 7. -/
theorem ssig0_shifts (x : Word) :
    (x >>> 1 ^^^ x <<< 63 ^^^ x >>> 8 ^^^ x <<< 56 ^^^ x >>> 7) = ssig0 x := by
  rw [Spec.Sha512.ssig0, rotateRight_eq_xor x (n := 1) (by decide) (by decide),
    rotateRight_eq_xor x (n := 8) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

/-- `σ₁`, as `schedule` computes it: rotations by 19 and 61 as shifts each way, and a shift by 6. -/
theorem ssig1_shifts (x : Word) :
    (x >>> 19 ^^^ x <<< 45 ^^^ x >>> 61 ^^^ x <<< 3 ^^^ x >>> 6) = ssig1 x := by
  rw [Spec.Sha512.ssig1, rotateRight_eq_xor x (n := 19) (by decide) (by decide),
    rotateRight_eq_xor x (n := 61) (by decide) (by decide)]
  simp only [Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

/-! ## One lane of `schedule` -/

/-- What `schedule` computes in one lane, from the lane's message registers
`x₀, x₁, x₄, x₅, x₇` (the words `2i-16 … 2i-15`, `2i-14 … 2i-13`, `2i-8 …
2i-7`, `2i-6 … 2i-5` and `2i-2 … 2i-1`), as its instructions do. -/
def xupd (x₀ x₁ x₄ x₅ x₇ : BitVec 128) : BitVec 128 :=
  let t₀ := alignRight x₁ x₀ 8
  let t₁ := alignRight x₅ x₄ 8
  let y := XBinOp.eval .paddq x₀ t₁
  let t₂ := XShiftOp.eval .psrlq t₀ 1
  let t₃ := XShiftOp.eval .psllq t₀ 63
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq t₀ 8
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psllq t₀ 56
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq t₀ 7
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let y := XBinOp.eval .paddq y t₂
  let t₂ := XShiftOp.eval .psrlq x₇ 19
  let t₃ := XShiftOp.eval .psllq x₇ 45
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq x₇ 61
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psllq x₇ 3
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq x₇ 6
  let t₂ := XBinOp.eval .pxor t₂ t₃
  XBinOp.eval .paddq y t₂

/-- `schedule`, on one lane: the next two words from the words it reads. -/
theorem xupd_eq (w₀ w₁ w₂ w₃ w₈ w₉ w₁₀ w₁₁ w₁₄ w₁₅ : Word) :
    xupd (w₁ ++ w₀) (w₃ ++ w₂) (w₉ ++ w₈) (w₁₁ ++ w₁₀) (w₁₅ ++ w₁₄) =
      (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅) ++ (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄) := by
  simp only [xupd, alignRight_8, paddq_eq,
    psrlq_eq _ _ _ (by decide : (1 : BitVec 8).toNat < 64), psllq_eq _ _ _ (by decide : (63 : BitVec 8).toNat < 64),
    psrlq_eq _ _ _ (by decide : (8 : BitVec 8).toNat < 64), psllq_eq _ _ _ (by decide : (56 : BitVec 8).toNat < 64),
    psrlq_eq _ _ _ (by decide : (7 : BitVec 8).toNat < 64), psrlq_eq _ _ _ (by decide : (19 : BitVec 8).toNat < 64),
    psllq_eq _ _ _ (by decide : (45 : BitVec 8).toNat < 64), psrlq_eq _ _ _ (by decide : (61 : BitVec 8).toNat < 64),
    psllq_eq _ _ _ (by decide : (3 : BitVec 8).toNat < 64), psrlq_eq _ _ _ (by decide : (6 : BitVec 8).toNat < 64),
    pxor_eq, BitVec.reduceToNat, ssig0_shifts, ssig1_shifts]

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = ssig1 (W M (t + 14)) + W M (t + 9) + ssig0 (W M (t + 1)) + W M t := by
  rw [Proof.Sha512.W_ge M (by omega)]
  simp only [show t + 16 - 2 = t + 14 by omega, show t + 16 - 7 = t + 9 by omega,
    show t + 16 - 15 = t + 1 by omega, Nat.add_sub_cancel]

/-- `schedule` computes the next two words of a block's schedule. -/
theorem xupd_pair (M : Block) (i : Nat) :
    xupd (pair M i) (pair M (i + 1)) (pair M (i + 4)) (pair M (i + 5)) (pair M (i + 7)) = pair M (i + 8) := by
  simp only [pair, Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
  rw [xupd_eq]
  have w0 : W M (2 * i + 16) = ssig1 (W M (2 * i + 14)) + W M (2 * i + 9) +
      ssig0 (W M (2 * i + 1)) + W M (2 * i) := W_ge' M (2 * i)
  have w1 : W M (2 * i + 17) = ssig1 (W M (2 * i + 15)) + W M (2 * i + 10) +
      ssig0 (W M (2 * i + 2)) + W M (2 * i + 1) := by
    rw [show 2 * i + 17 = 2 * i + 1 + 16 by omega, W_ge']
  rw [w0, w1]
  simp only [BitVec.add_assoc, BitVec.add_comm, Proof.Sha512.add_left_comm]

end VG.Proof.Sha512.X86_64.Avx2

/-!
# SHA-512 with AVX2 on x86-64: running the message schedule

`schedule i` computes, in each lane of `msg i`, what `xupd` says, and stores
the register.
-/

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2

theorem msg_add8 (n : Nat) : msg (n + 8) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The vector registers of `schedule i` are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 4), msg (n + 5), msg (n + 7), t0, t1, t2, t3, mBswap, tmp].Nodup := by
  have key : ∀ c < 8,
      [msg c, msg (c + 1), msg (c + 4), msg (c + 5), msg (c + 7), t0, t1, t2, t3, mBswap, tmp].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 8 + k) := fun k => by
    simp only [msg]; rw [show (n % 8 + k) % 8 = (n + k) % 8 by omega]
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod], e 1, e 4, e 5, e 7]
  exact key _ (Nat.mod_lt _ (by decide))

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The schedule of words `2i, 2i+1`, from lanes 0 (`a …`) and 1 (`a' …`) of
`msg i`, `msg (i+1)`, `msg (i+4)`, `msg (i+5)` and `msg (i+7)`. -/
theorem schedule_ok (i : Nat) (s : State) (a b c d e a' b' c' d' e' : BitVec 128)
    (ha : s.xmm (msg i) = a) (hb : s.xmm (msg (i + 1)) = b) (hc : s.xmm (msg (i + 4)) = c)
    (hd : s.xmm (msg (i + 5)) = d) (he : s.xmm (msg (i + 7)) = e)
    (ha' : s.ymmHi (msg i) = a') (hb' : s.ymmHi (msg (i + 1)) = b') (hc' : s.ymmHi (msg (i + 4)) = c')
    (hd' : s.ymmHi (msg (i + 5)) = d') (he' : s.ymmHi (msg (i + 7)) = e')
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int)) 32) :
    WP isa (.block (schedule i)) s fun s' =>
      s'.xmm (msg i) = xupd a b c d e ∧ s'.ymmHi (msg i) = xupd a' b' c' d' e' ∧
      (∀ r, r ≠ msg i → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int))
        (xupd a' b' c' d' e' ++ xupd a b c d e) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup i
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [schedule, vb, vs]
  generalize msg i = x₀ at *
  generalize msg (i + 1) = x₁ at *
  generalize msg (i + 4) = x₄ at *
  generalize msg (i + 5) = x₅ at *
  generalize msg (i + 7) = x₇ at *
  simp only [t0, t1, t2, t3, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.ymm, State.store256, ea_at, hout, ite_true, ite_false, hn, hn',
    ha, hb, hc, hd, he, ha', hb', hc', hd', he', Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, rfl, trivial⟩

end VG.Proof.Sha512.X86_64.Avx2
