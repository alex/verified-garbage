import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Impl.X25519.X86_64.Adx

/-!
# X25519 on x86-64: the steps of the BMI2/ADX field arithmetic

The steps `mulX`, `sqrX` and `a24X` are made of (see
`Impl/X25519/X86_64/Adx.lean`), each run symbolically once, for any registers:
a product whose low half is added through CF (`mulAcc`), or through OF while
its high half is added through CF (`madd`), the last of a row (`maddLast`), a
word doubled through CF while another is added through OF (`dblAdd`), and the
instructions around them. Each states what it computes as an equation on
numbers, the carries in and out included, which `omega` composes.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

theorem of_setReg (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).of = s.of := rfl
theorem of_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).of = b := rfl

/-- `mulx hi, lo, src` runs as `setReg lo` then `setReg hi`. -/
theorem execMulx_eq {s : State} {hi lo : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) :
    execMulx hi lo src s = some ((s.setReg lo (BitVec.ofNat 64 ((s.gpr .rdx).toNat *
      v.toNat))).setReg hi (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64))) := by
  cases src with
  | imm n => exact absurd rfl (himm n)
  | reg r => simp only [execMulx, hsrc, Option.map_some]
  | mem m => simp only [execMulx, hsrc, Option.map_some]

/-- `xor ebp, ebp`. -/
theorem clear_ok (s : State) :
    WP isa (.block [clear]) s fun s' =>
      s'.gpr .rbp = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [.rbp] s s' := by
  apply WP.of_runBlock
  simp only [clear, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self, BitVec.xor_self,
    RegUpd.cf_setReg, of_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mov rdx, src`. -/
theorem movRdx_ok (s : State) {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v) :
    WP isa (.block [.mov .rdx src]) s fun s' =>
      s'.gpr .rdx = v ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hsrc, Option.map_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mov edx, k`. -/
theorem movRdxImm_ok (s : State) (k : BitVec 32) :
    WP isa (.block [.mov32 .rdx (.imm k)]) s fun s' =>
      (s'.gpr .rdx).toNat = k.toNat ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, of_setReg, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le k.isLt (by decide))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mulx hi, lo, src`: `lo + 2⁶⁴ hi = rdx · src`, the flags unchanged. -/
theorem mulx_ok (s : State) {hi lo : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo src]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * v.toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [hi, lo] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execMulx_eq hsrc himm,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), RegUpd.cf_setReg, of_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨mulx_arith _ _, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `adcx x, rbp` with `rbp = 0`: the carry CF added into `x`. -/
theorem carryC_ok (s : State) {x : Reg} {c : Bool} (hc : s.cf = some c) (hz : s.gpr .rbp = 0) :
    WP isa (.block [.adcx x (.reg .rbp)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ s'.of = s.of ∧
        (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + c.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdcx, readSrc, hz, hc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, of_setReg, of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have := adc_carry (s.gpr x) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `mulx y, rax, src`, `adcx x, rax`: `rdx · src` added at `x` through CF,
its high half into `y`. -/
theorem mulAcc_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (hxa : x ≠ .rax) (hya : y ≠ .rax) (hxy : x ≠ y) :
    WP isa (.block (mulAcc x y src)) s fun s' =>
      ∃ c', s'.cf = some c' ∧ s'.of = s.of ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * c'.toNat =
          (s.gpr x).toNat + c.toNat + (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [mulAcc, runBlock_cons, runStep_some, runBlock_nil, exec, execMulx_eq hsrc himm,
    execAdcx, readSrc, Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hya), RegUpd.gpr_setReg_of_ne _ _ hxy,
    RegUpd.gpr_setReg_of_ne _ _ hxa, RegUpd.cf_setReg, RegUpd.cf_setFlags, of_setReg,
    of_setFlags, hc, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy),
      RegUpd.gpr_setFlags]
    have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) c
    have e2 := mulx_arith (s.gpr .rdx) v
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.1, RegUpd.gpr_setFlags,
      RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `mulx rcx, rax, src`, `adox x, rax`, `adcx y, rcx`: the product
`rdx · src` added at `x` (with the carry OF) and `y` (the next word, with the
carry CF), the carries out in OF (into `y`'s word) and CF (into the next). -/
theorem madd_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c o : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (ho : s.of = some o) (hxh : x ≠ .rcx) (hxl : x ≠ .rax) (hyh : y ≠ .rcx) (hyl : y ≠ .rax)
    (hxy : x ≠ y) :
    WP isa (.block (madd x y src)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * o'.toNat + 2 ^ 128 * c'.toNat =
          (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat + o.toNat + 2 ^ 64 * c.toNat +
            (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rcx, .rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [madd, runBlock_cons, exec, execMulx_eq hsrc himm, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxh,
    RegUpd.gpr_setReg_of_ne _ _ hxl, RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rax ≠ .rcx),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxh),
    RegUpd.gpr_setReg_of_ne _ _ hyh, RegUpd.gpr_setReg_of_ne _ _ hyl,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy), RegUpd.gpr_setFlags, of_setReg, of_setFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxy, RegUpd.gpr_setFlags]
    have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) o
    have e2 := adc_carry (s.gpr y) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64)) c
    have e3 := mulx_arith (s.gpr .rdx) v
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
      RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1]

/-- `mulx y, rax, src`, `adox x, rax`, `adcx y, rbp`, `adox y, rbp`, with
`rbp = 0`: the product added at `x` (with the carry OF), its high half into
`y` (overwritten) with the carry CF, and the carry out of `x` into `y` too. -/
theorem maddLast_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c o : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (ho : s.of = some o) (hz : s.gpr .rbp = 0) (hxa : x ≠ .rax) (hya : y ≠ .rax)
    (hxb : x ≠ .rbp) (hyb : y ≠ .rbp) (hxy : x ≠ y) :
    WP isa (.block (maddLast x y src)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 128 * (c'.toNat + o'.toNat) =
          (s.gpr x).toNat + o.toNat + 2 ^ 64 * c.toNat + (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [maddLast, runBlock_cons, exec, execMulx_eq hsrc himm, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxy,
    RegUpd.gpr_setReg_of_ne _ _ hxa, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hya),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy), RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hyb),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxb), RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rbp ≠ .rax),
    hz, RegUpd.gpr_setFlags, of_setReg, of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) o
    have e2 := adc_carry (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64)) 0 c
    have e3 := adc_carry (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64) + 0 +
      (BitVec.ofBool c).setWidth 64) 0 (decide (2 ^ 64 ≤ (s.gpr x).toNat +
        (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)).toNat + o.toNat))
    have e4 := mulx_arith (s.gpr .rdx) v
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e2 e3 ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
      RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `adcx x, x`, `adox x, s`: `x` doubled (with the carry CF), `s` added
(with the carry OF), both carries out into the next word. -/
theorem dblAdd_ok (s : State) {x y : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hxy : x ≠ y) :
    WP isa (.block (dblAdd x y)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
          2 * (s.gpr x).toNat + (s.gpr y).toNat + c.toNat + o.toNat ∧
        Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [dblAdd, runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy),
    RegUpd.gpr_setFlags, of_setReg, of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) (s.gpr x) c
    have e2 := adc_carry (s.gpr x + s.gpr x + (BitVec.ofBool c).setWidth 64) (s.gpr y) o
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adcx x, rbp`, `adox x, rbp` with `rbp = 0`: both carries added into `x`. -/
theorem carries_ok (s : State) {x : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hz : s.gpr .rbp = 0) (hxb : x ≠ .rbp) :
    WP isa (.block [.adcx x (.reg .rbp), .adox x (.reg .rbp)]) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) = (s.gpr x).toNat + c.toNat + o.toNat ∧
        Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxb), hz, RegUpd.gpr_setFlags, of_setReg, of_setFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) 0 c
    have e2 := adc_carry (s.gpr x + 0 + (BitVec.ofBool c).setWidth 64) 0 o
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e1 e2 ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

end VG.Proof.X25519.X86_64
