import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.PointSelect

/-!
# The comb's signed digits

`combSign` turns the nibble `n` into the digit `n - 8`'s magnitude, in `rax`,
and the mask of its sign, at byte `combSignMask`; `combNeg` negates the
selected cached point in slots 4–7 under that mask.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

/-- The mask of the digit `n - 8`'s sign: all ones if it is negative. -/
def signMask (n : Nat) : BitVec 64 := if n < 8 then BitVec.allOnes 64 else 0

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - (8 : BitVec 32).signExtend 64 ^^^
        0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
          ((8 : BitVec 32).signExtend 64).toNat))).setWidth 64) -
      (0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
        ((8 : BitVec 32).signExtend 64).toNat))).setWidth 64) = BitVec.ofNat 64 (mag n)) ∧
    0#64 - (BitVec.ofBool (decide ((BitVec.ofNat 64 n).toNat <
      ((8 : BitVec 32).signExtend 64).toNat))).setWidth 64 = signMask n := by
  decide +kernel

theorem combSign_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat} (hn : n < 16)
    (hax : s.gpr .rax = BitVec.ofNat 64 n) :
    WP isa (.block combSign) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (mag n) ∧ t.mem.readW (off base combSignMask) 64 = signMask n ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base combSignMask 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base combSignMask) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  apply WP.of_runBlock
  simp only [combSign, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_setReg, RegUpd.cf_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hax, hw, ite_true, ite_false, reduceCtorEq,
    BitVec.sub_self, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, ?_, fun r h1 h2 => ?_, rfl, trivial, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact (sign_fact n hn).2
  · simp only [h1, h2, ite_false]
  · exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by simp only [combSignMask]; omega)

/-! ## The negation -/

/-- The cached point `c` negated: `[Y + X, Y - X, -2dT, 2Z]` for `[Y - X, Y + X, 2dT, 2Z]`. -/
def negCached (c : Spec.Ed25519.Point) : Spec.Ed25519.Point := ⟨c.Y, c.X, 0 - c.Z, c.T⟩

theorem negCached_cache (q : Spec.Ed25519.Point) : negCached (cache q) = cache (negPoint q) := by
  simp only [negCached, cache, negPoint, Spec.Ed25519.Point.mk.injEq]
  refine ⟨toZ_inj.1 ?_, toZ_inj.1 ?_, toZ_inj.1 ?_, trivial⟩ <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_zero] <;> ring

variable {fld : Arith} [EdArith fld]

theorem loadSignMask_ok {s : State} {base : Addr} (hs : Scratch s base) {m : BitVec 64}
    (hm : s.mem.readW (off base combSignMask) 64 = m) :
    WP isa (.block [.mov .rcx (.mem (Impl.X25519.X86_64.sc combSignMask))]) s fun t =>
      t.gpr .rcx = m ∧ Keeps [.rcx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base combSignMask) 8 :=
    ⟨_, List.mem_append_right _ hs.wr,
      Offset.contains_base _ (by simp only [combSignMask]; omega) (by simp only [combSignMask]; omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, hs.rdi, hr, hm, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem signMask_eq (n : Nat) : signMask n = Proof.X25519.X86_64.mask (decide (n < 8)) := by
  by_cases h : n < 8 <;> simp [signMask, Proof.X25519.X86_64.mask, h]

theorem combNeg_ok {s : State} {base : Addr} (hs : Scratch s base) {n : Nat}
    (hm : s.mem.readW (off base combSignMask) 64 = signMask n) :
    WP isa (.block (combNeg fld)) s fun t =>
      point (env t.mem base) 4 5 6 7 = (if n < 8 then negCached (point (env s.mem base) 4 5 6 7)
        else point (env s.mem base) 4 5 6 7) ∧ Keep base s t ∧
      (∀ i : Slot, (i.val < 4 ∨ 10 ≤ i.val) → env t.mem base i = env s.mem base i) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs _) fun a ⟨ka, va⟩ => ?_
  have hsa := hs.of_keep ka
  rw [WP.block_append_iff]
  refine WP.mono (loadSignMask_ok hsa (m := signMask n) (by
    rw [← hm]; exact ka.mem.word (Or.inr (by simp only [combSignMask]; omega))
      (by simp only [combSignMask]; omega))) fun b ⟨bc, kb⟩ => ?_
  have hsb := hsa.of_keeps kb (by decide)
  refine WP.mono (swapFieldsWide_ok hsb [(4, 5), (6, 8)]
    (fun ab h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    (sw := decide (n < 8))
    (by rw [bc, signMask_eq])) fun t ⟨kt, _, vt⟩ => ?_
  have kbk : Keep base a b := ⟨fun r hr => kb.1 r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; decide)),
    kb.2.2.1, kb.2.2.2, by rw [kb.2.1]; exact Outside.refl _ _ _ _⟩
  have ev : env t.mem base = swapEnvs [(4, 5), (6, 8)] (decide (n < 8))
      (evalOps [.const 9 0, .sub 8 9 6] (env s.mem base)) := by rw [vt, kb.2.1, va]
  refine ⟨?_, (ka.trans kbk).trans kt, fun i hi => ?_⟩
  · rw [ev]
    by_cases h : n < 8
    · simp [h, swapEnvs, swapEnv, evalOps, evalOp, point, negCached]
    · simp [h, swapEnvs, swapEnv, evalOps, evalOp, point]
  · rw [ev]
    have h4 : i ≠ 4 := fun h => by subst h; simp at hi
    have h5 : i ≠ 5 := fun h => by subst h; simp at hi
    have h6 : i ≠ 6 := fun h => by subst h; simp at hi
    have h8 : i ≠ 8 := fun h => by subst h; simp at hi
    have h9 : i ≠ 9 := fun h => by subst h; simp at hi
    simp [swapEnvs, swapEnv, evalOps, evalOp, h4, h5, h6, h8, h9]

end VG.Proof.Ed25519.X86_64
