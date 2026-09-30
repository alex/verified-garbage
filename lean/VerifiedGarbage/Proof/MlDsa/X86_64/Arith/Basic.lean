import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Common
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# ML-DSA on x86-64: reduction modulo `q`, and the contracts

Untrusted: everything here is checked by Lean. It uses the symbolic
execution of ML-KEM's x86-64 proofs (`xrun`, `Keep`, `WP.keep`, the counted
loops, `Proof/MlKem/X86_64/Wp.lean`), which are about the ISA, not ML-KEM.

* `csubQ` leaves `csubD v` of `v`, `v mod q` for `v < 2q` (`csubD_toNat`);
* `reduce` leaves `redD x` in `r10` of any `x` in `rax`, which is `x mod q`
  (`reduce_ok`, `redD_toNat`): `barrett` of `Arith/Zq.lean` then `csubQ`;
* for each function, a contract with the facts of its shared contract
  (`Spec/MlDsa/Poly.lean`) spelled out for x86-64: the arguments in their
  registers, the permitted regions, their disjointness, and the
  postcondition. The proofs are written against these, and
  `Verified.of_correct` moves them to the shared contracts, which imply them
  (`mldsa_implies`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of wp_countdown wp_counted ifp ifn
  toNat_setWidth64 toNat_setWidth32_64 read_zero)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## Immediates -/

theorem qImm_toNat : qImm.toNat = 8380417 := rfl

theorem sxQD : BitVec.signExtend 64 qImm = 8380417 := by decide

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ea_atD (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

/-- `xrun` (`Proof/MlKem/X86_64/Wp.lean`) for this code's memory operands
and immediates. -/
syntax "xrund" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| xrund) => `(tactic| xrund [])
  | `(tactic| xrund [$ls,*]) => `(tactic| xrun [ea_atD, sxQD, $ls,*])

/-! ## `csubQ` -/

/-- What `csubQ` leaves of `v`. -/
def csubD (v : BitVec 32) : BitVec 32 :=
  v - qImm + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < qImm.toNat))) &&& qImm)

theorem csubD_toNat (v : BitVec 32) : (csubD v).toNat = condSub v.toNat := by
  unfold csubD condSub
  rw [qImm_toNat]
  by_cases h : 8380417 ≤ v.toNat
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < 8380417))) &&& qImm) = 0 := by
      rw [decide_eq_false (by omega)]; decide
    rw [e, ifp (by rw [q_eq]; exact h)]
    unfold qImm
    rw [q_eq]
    bv_omega
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < 8380417))) &&& qImm) = qImm := by
      rw [decide_eq_true (by omega)]; decide
    rw [e, ifn (by rw [q_eq]; exact h)]
    unfold qImm
    bv_omega

theorem csubD_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (csubD (a + b)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add]; rw [q_eq] at *; omega
  rw [csubD_toNat, e]

theorem csubD_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (csubD (a + qImm - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a + qImm - b).toNat = a.toNat + q - b.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, qImm_toNat]; rw [q_eq] at *; omega
  rw [csubD_toNat, e]

/-- `csubQ` after adding two words of values `x` and `y`. -/
theorem csubD_add_val {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (csubD (a + b)).toNat = (x + y).val := by
  rw [csubD_add (by rw [ha]; exact x.isLt) (by rw [hb]; exact y.isLt), ha, hb, val_add]

/-- `csubQ` after subtracting a word of value `y` from one of value `x`. -/
theorem csubD_sub_val {a b : BitVec 32} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (csubD (a + qImm - b)).toNat = (x - y).val := by
  rw [csubD_sub (by rw [ha]; exact x.isLt) (by rw [hb]; exact y.isLt), ha, hb, val_sub]

/-! ## `reduce` -/

/-- What `reduce` leaves in `r10`, of `x`. -/
def redD (x : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (csubD (BitVec.setWidth 32 (x - BitVec.ofNat 64
    ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat * BitVec.toNat (8380417 : BitVec 64)))))

theorem redD_toNat (x : BitVec 64) : (redD x).toNat = x.toNat % q := by
  have hx := x.isLt
  have hb := barrett_bounds hx
  have e1 : (BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat = barrettQuot x.toNat := by
    rw [BitVec.toNat_ofNat, show barrettImm.toNat = barrettM from rfl, Nat.mod_eq_of_lt]; rfl
    unfold barrettM; omega
  have e2 : (BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat *
      BitVec.toNat (8380417 : BitVec 64))).toNat = barrettQuot x.toNat * q := by
    rw [e1, show BitVec.toNat (8380417 : BitVec 64) = q from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have e3 : (x - BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat / 2 ^ 64)).toNat *
      BitVec.toNat (8380417 : BitVec 64))).toNat = barrett x.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e2]; exact hb.1), e2]; rfl
  have hl : barrett x.toNat < 2 * q := barrett_lt hx
  have e4 := toNat_setWidth32_64 (show (x - BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * barrettImm.toNat /
    2 ^ 64)).toNat * BitVec.toNat (8380417 : BitVec 64))).toNat < 2 ^ 32 by rw [e3]; rw [q_eq] at hl; omega)
  rw [e3] at e4
  rw [redD, toNat_setWidth64, csubD_toNat, e4, reduce_barrett hx]

/-- The low half of `redD x`, whose value is `x mod q`. -/
theorem redD32_toNat (x : BitVec 64) : (BitVec.setWidth 32 (redD x)).toNat = x.toNat % q := by
  have h := redD_toNat x
  have : x.toNat % q < q := Nat.mod_lt _ (by decide)
  rw [toNat_setWidth32_64 (by rw [h]; exact Nat.lt_of_lt_of_le this (by decide)), h]

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' => (s'.gpr .r10 = redD (s.gpr .rax) ∧ s'.mem = s.mem) ∧
      Keep [.rax, .rdx, .r10, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold reduce csubQ
  xrund [List.cons_append, List.nil_append, csubD, redD]

/-- The product of a word and `r`, as `mul` leaves it. -/
abbrev prodW (a : BitVec 32) (r : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * r.toNat)

/-- The product of a word of value `x` and a register of value `z`, reduced:
the value of `z · x`. -/
theorem redD_prodW {u : BitVec 32} {x z : Zq} (hu : u.toNat = x.val) :
    (BitVec.setWidth 32 (redD (prodW u (BitVec.ofNat 64 z.val)))).toNat = (z * x).val := by
  have hz := val_lt z
  have hx := val_lt x
  have e : (prodW u (BitVec.ofNat 64 z.val)).toNat = x.val * z.val := by
    rw [prodW, BitVec.toNat_ofNat, toNat_setWidth64, hu, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := z.val) (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (mul_lt_q2 hx hz) (by decide))
  rw [redD32_toNat, e, val_mul, Nat.mul_comm]

/-! ## The contracts -/

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mldsa_ntt(f = rdi, scratch = rsi)` and `vg_mldsa_inv_ntt`: `f`
becomes `t f`. -/
def inPlaceK (t : Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mldsa_add(f = rdi, g = rsi)` and `vg_mldsa_sub(f = rdi, g = rsi)`:
`f` becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mldsa_multiply_ntt(h = rdi, f = rsi, g = rdx)` and
`vg_mldsa_multiply_add_ntt`: `h` becomes `t h f g`, if `hPre` of `h` (for
`vg_mldsa_multiply_add_ntt`, that it is reduced). -/
def mulK (t : Poly → Poly → Poly → Poly) (hPre : Mem → Addr → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rdx)) ∧ hPre s.mem (s.gpr .rdi) ∧
    Reduced s.mem (s.gpr .rsi) ∧ Reduced s.mem (s.gpr .rdx)
  post s s' := PolyIs s'.mem (s.gpr .rdi)
    (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)) (polyAt s.mem (s.gpr .rdx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Satisfiability -/

/-- In memory of zeros, every polynomial is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, read_zero]
  decide

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
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlDsa.X86_64.Arith
