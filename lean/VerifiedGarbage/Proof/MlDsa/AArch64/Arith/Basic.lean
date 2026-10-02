import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA on AArch64: symbolic execution, and reduction modulo `q`

It uses the weakest preconditions and loops of ML-KEM's AArch64 proofs
(`Keep`, `count_loop`, `Proof/MlKem/AArch64/Wp.lean`), which are about the
ISA, not ML-KEM.

* `arun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), with the state a chain of `State.write`s and memory
  updates whose registers `RegUpd.gpr_write` reads, so that a register of
  the result is the value last written to it. A block lemma takes the
  accesses it makes as hypotheses on the registers of its initial state.
* `WP.keep`: the registers no instruction of the code writes are kept
  (`writesOnly`, checked by evaluation).
* `wp_countdown`: a loop on `cbnz` of a counter that its body decrements.
* `csub` leaves `csubX v` of `v`, which is `v mod q` for `v < 2q`
  (`csubX_toNat`); `reduce` leaves `redX x` of any `x`, which is `x mod q`
  for `x < q²` (`redX_toNat`): a Barrett reduction with 64-bit products
  (`barrett64_bounds`), then `csub`.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## The instructions, for `simp` -/

section
variable {s : State}

theorem exec_sub {sz : Size} {d n m : Reg} :
    exec (.sub sz d n m) s = some (s.write sz d (s.read sz n - s.read sz m)) := rfl

theorem exec_mul {sz : Size} {d n m : Reg} :
    exec (.mul sz d n m) s = some (s.write sz d (s.read sz n * s.read sz m)) := rfl

theorem exec_madd {sz : Size} {d n m a : Reg} :
    exec (.madd sz d n m a) s = some (s.write sz d (s.read sz a + s.read sz n * s.read sz m)) := rfl

theorem exec_lsl_x {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp [exec, Size.bits, h]

theorem exec_addImm_w {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d (s.read .w n + BitVec.ofNat _ imm)) := by
  simp [exec, h]

theorem exec_movz_x {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.shiftLeft_zero _)

theorem exec_movk_x {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64) :
    exec (.movk .x d imm hw) s = some (s.write .x d ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) |||
      (imm.setWidth 64 <<< (16 * hw)))) := by
  simp [exec, Size.bits, h, State.read]

end

/-- `arun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
syntax "arun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| arun) => `(tactic| arun [])
  | `(tactic| arun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec_ldr_w, exec_str_w, exec_add, exec_sub, exec_logic, exec_mul, exec_madd, exec_addImm_x,
        exec_subImm_x, exec_addImm_w, exec_lsr_x, exec_lsl_x, exec_movz_w, exec_movk_w, exec_movz_x,
        exec_movk_x, State.read, Size.bits, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.sp_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left',
        ite_true, ite_false, reduceCtorEq, true_and, and_true, List.cons_append, List.nil_append,
        BitVec.add_zero, BitVec.setWidth_setWidth_of_le, movz_movk,
        $ls,*]))

/-! ## What a block keeps -/

/-- Whether every instruction of `c` writes, if any register, one of `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => match dstOf i with
    | none => true
    | some d => rs.contains d

/-- A register that no instruction writes keeps its value (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide)
    (hv : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2, Exec.preservedV he hv⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := hc i hi
  intro e
  rw [e] at this
  simp only [List.contains_iff_mem] at this
  exact hr (by simpa using this)


/-! ## Loops -/

/-- A do-while loop on `cbnz cnt` whose body decrements `cnt`, from `N > 0`:
it runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero .x cnt)) s (Inv N) := by
  refine WP.mono (count_loop (cr := cnt) hN0 (fun k s => Inv k s ∧ s.gpr cnt = BitVec.ofNat 64 (N - k))
    (fun k hk s ⟨hI, hc⟩ => WP.mono (hbody k hk s hI hc) fun s' ⟨hI', hc'⟩ => ⟨⟨hI', ?_⟩, ?_⟩)
    ⟨h0, by rw [hc, Nat.sub_zero]⟩) fun _ h => h.1
  · rw [hc', hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [hc', hc, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-! ## `csub` -/

/-- `q`, as a 64-bit value. -/
abbrev Qv : BitVec 64 := BitVec.ofNat 64 8380417

/-- What `csub` leaves of `v`, with `q` in the register of `q`. -/
def csubX (v : BitVec 64) : BitVec 64 := v - Qv + ((v - Qv) >>> 63) * Qv

theorem csubX_toNat {v : BitVec 64} (h : v.toNat < 2 * q) : (csubX v).toNat = condSub v.toNat := by
  unfold csubX condSub
  rw [q_eq] at *
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  split <;> omega

/-- The low word of a 64-bit value less than `2³²`. -/
theorem toNat_setWidth32 {v : BitVec 64} (h : v.toNat < 2 ^ 32) : (v.setWidth 32).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem toNat_setWidth64 (v : BitVec 32) : (v.setWidth 64).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

/-- `csub` of a value less than `2q`, stored as a word. -/
theorem csubX32 {v : BitVec 64} (h : v.toNat < 2 * q) :
    ((csubX v).setWidth 32).toNat = v.toNat % q := by
  have h1 := csubX_toNat h
  have h2 : condSub v.toNat < q := condSub_lt h
  rw [toNat_setWidth32 (by rw [h1]; rw [q_eq] at h2; omega), h1, condSub_eq h]

/-- The sum of two words of values `x` and `y`, reduced. -/
theorem csubX_add {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((csubX (a.setWidth 64 + b.setWidth 64)).setWidth 32).toNat = (x + y).val := by
  have hx := x.isLt; have hy := y.isLt; have := a.isLt; have := b.isLt
  have e : (a.setWidth 64 + b.setWidth 64).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add, toNat_setWidth64, toNat_setWidth64]; omega
  rw [csubX32 (by rw [e, ha, hb]; omega), e, ha, hb, val_add']

/-- The difference of two words of values `x` and `y` (`x + q - y`), reduced. -/
theorem csubX_sub {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((csubX (a.setWidth 64 + Qv - b.setWidth 64)).setWidth 32).toNat = (x - y).val := by
  have hx := x.isLt; have hy := y.isLt; have := a.isLt; have := b.isLt
  have hQ : Qv.toNat = q := rfl
  have e1 : (a.setWidth 64 + Qv).toNat = a.toNat + q := by
    rw [VG.Proof.MlKem.AArch64.toNat_add_n (by rw [toNat_setWidth64, hQ, q_eq]; omega), toNat_setWidth64,
      hQ]
  have e : (a.setWidth 64 + Qv - b.setWidth 64).toNat = a.toNat + q - b.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [e1, toNat_setWidth64, hb]; omega), e1,
      toNat_setWidth64]
  rw [csubX32 (by rw [e, ha, hb]; omega), e, ha, hb, val_sub, condSub_eq (by omega)]

/-! ## `reduce` -/

/-- `M`, as a 64-bit value. -/
abbrev Mv : BitVec 64 := BitVec.ofNat 64 550293143936

theorem Mv_toNat : Mv.toNat = 550293143936 := rfl

theorem negQ_toNat : negQ.toNat = 2 ^ 64 - 8380417 := rfl

/-- The quotient estimate of `reduce`: `⌊⌊x / 2²²⌋ · M / 2⁴⁰⌋`. -/
def barrett64 (x : Nat) : Nat := x / 2 ^ 22 * 550293143936 / 2 ^ 40

/-- For `x < q²`, the estimate is `⌊x / q⌋` or one less. -/
theorem barrett64_bounds {x : Nat} (hx : x < q * q) :
    barrett64 x * q ≤ x ∧ x < barrett64 x * q + 2 * q := by
  unfold barrett64
  rw [q_eq] at *
  constructor <;> omega

/-- What `reduce` leaves of `x`. -/
def redX (x : BitVec 64) : BitVec 64 := csubX (x + (((x >>> 22) * Mv) >>> 40) * negQ)

/-- The arithmetic of `reduce`, on natural numbers. -/
theorem barrett64_nat {x : Nat} (hx : x < q * q) :
    x / 2 ^ 22 * 550293143936 < 2 ^ 64 ∧
      (x + barrett64 x * (2 ^ 64 - 8380417)) % 2 ^ 64 = x - barrett64 x * q ∧
      x - barrett64 x * q < 2 * q ∧ (x - barrett64 x * q) % q = x % q := by
  have hb := barrett64_bounds hx
  refine ⟨?_, ?_, by omega, by rw [Nat.mul_comm, Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact hb.1)]⟩
  · rw [q_eq] at hx; omega
  rw [q_eq] at hb hx ⊢
  generalize barrett64 x = B at hb
  rw [show x + B * (2 ^ 64 - 8380417) = (x - B * 8380417) + B * 2 ^ 64 by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem redX_toNat {x : BitVec 64} (hx : x.toNat < q * q) : (redX x).toNat = x.toNat % q := by
  obtain ⟨hm, h2, hl, h4⟩ := barrett64_nat hx
  have e1 : (((x >>> 22) * Mv) >>> 40).toNat = barrett64 x.toNat := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Mv_toNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hm]
    rfl
  have e2 : (x + (((x >>> 22) * Mv) >>> 40) * negQ).toNat = x.toNat - barrett64 x.toNat * q := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, e1, negQ_toNat,
      Nat.add_mod_mod, h2]
  unfold redX
  rw [csubX_toNat (by rw [e2]; exact hl), e2, condSub_eq hl, h4]

/-- `redX x` stored as a word: `x mod q`. -/
theorem redX32 {x : BitVec 64} (hx : x.toNat < q * q) : ((redX x).setWidth 32).toNat = x.toNat % q := by
  have h := redX_toNat hx
  have : x.toNat % q < q := Nat.mod_lt _ (by decide)
  rw [toNat_setWidth32 (by rw [h]; exact Nat.lt_of_lt_of_le this (by decide)), h]

/-- The product of a word of value `x` and a register of value `z`, reduced:
the value of `z · x`. -/
theorem redX_mul {u : BitVec 32} {x z : Zq} (hu : u.toNat = x.val) :
    ((redX (u.setWidth 64 * BitVec.ofNat 64 z.val)).setWidth 32).toNat = (z * x).val := by
  have hz := z.isLt
  have hx := x.isLt
  have e : (u.setWidth 64 * BitVec.ofNat 64 z.val).toNat = x.val * z.val := by
    rw [BitVec.toNat_mul, toNat_setWidth64, hu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := z.val)
      (Nat.lt_of_lt_of_le hz (by decide))]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hx hz) (by decide))
  rw [redX32 (by rw [e]; exact Nat.mul_lt_mul_of_lt_of_lt hx hz), e, val_mul, Nat.mul_comm]

/-! ## Constants -/

theorem q32 : (BitVec.ofNat 32 8380417).setWidth 64 = Qv := by decide

theorem toNat_Qv : Qv.toNat = q := rfl

/-- A 16-bit immediate. -/
theorem imm16 {k : Nat} (h : k < 65536) : (BitVec.ofNat 16 k).setWidth 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `movW d v`: `d ← v`. -/
theorem movW_ok (d : Reg) (v : BitVec 32) (s : State) :
    WP isa (.block (movW d v)) s fun s' => (s'.gpr d = v.setWidth 64 ∧ s'.mem = s.mem) ∧ Keep [d] s s' := by
  refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, movW, dstOf]) (hv := by simp [Code.allInstrs, movW, keepsV, vdstOf])
  unfold movW
  arun
  exact congrArg (BitVec.setWidth 64) (movz_movk v)

/-- `movImm d v`: `d ← v`. -/
theorem movImm_ok (d : Reg) (v : BitVec 64) (s : State) :
    WP isa (.block (Impl.MlKem.AArch64.movImm d v)) s fun s' => (s'.gpr d = v ∧ s'.mem = s.mem) ∧
      Keep [d] s s' := by
  refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, Impl.MlKem.AArch64.movImm, dstOf]) (hv := by simp [Code.allInstrs, Impl.MlKem.AArch64.movImm, keepsV, vdstOf])
  unfold Impl.MlKem.AArch64.movImm
  arun
  have := movz_movk64' v
  rw [BitVec.shiftLeft_zero] at this
  exact this

/-! ## The contracts -/

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mldsa_ntt(f = x0, scratch = x1)` and `vg_mldsa_inv_ntt`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .x0), pR (s.gpr .x1)] ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0)
  post s s' := PolyIs s'.mem (s.gpr .x0) (t (polyAt s.mem (s.gpr .x0)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_add(f = x0, g = x1)` and `vg_mldsa_sub(f = x0, g = x1)`: `f`
becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x1)] ∧ s.wr = [pR (s.gpr .x0)] ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1)
  post s s' := PolyIs s'.mem (s.gpr .x0) (t (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_multiply_ntt(h = x0, f = x1, g = x2)` and
`vg_mldsa_multiply_add_ntt`: `h` becomes `t h f g`, if `hPre` of `h` (for
`vg_mldsa_multiply_add_ntt`, that it is reduced). -/
def mulK (t : Poly → Poly → Poly → Poly) (hPre : Mem → Addr → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x1), pR (s.gpr .x2)] ∧ s.wr = [pR (s.gpr .x0)] ∧
    (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)) ∧
    hPre s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1) ∧ Reduced s.mem (s.gpr .x2)
  post s s' := PolyIs s'.mem (s.gpr .x0)
    (t (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

/-- The pointers `rs` and the stack pointer are public. -/
theorem agree_regs {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  VG.Proof.MlKem.AArch64.agree_of hsp h

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "mldsa_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mldsa_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact VG.Proof.MlDsa.Round.reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlDsa.AArch64.Arith
