import VerifiedGarbage.Proof.Mont.X86_64.Ops

/-!
# Short Weierstrass curves on x86-64: loops counted down in `rbx`

The ladder and the powers loop with `rbx` counting down: the body starts with
`sub rbx, 1` and ends with `test rbx, rbx`, and the loop runs while `rbx ≠ 0`.
`countLoop_ok` runs such a loop `n ≥ 1` times from an invariant indexed by
`rbx`; `decRbx_ok` and `testRbx_ok` are its first and last instruction.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- A loop whose body takes the invariant from `j` to `j - 1` and sets `ZF`
when `j - 1 = 0`, run from `n ≥ 1`. -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.zf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show s'.zf.map (!·) = some false
    rw [hz, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega, by omega, by omega, hi'⟩
    show s'.zf.map (!·) = some true
    rw [hz]; simp [hj]

theorem decRbx_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (j - 1) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left', hb]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega : j - 1 < 2 ^ 64)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem testRbx_ok (s : State) {j : Nat} (hj' : j < 2 ^ 64) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun s' =>
      s'.zf = some (decide (j = 0)) ∧ Keeps [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb, BitVec.and_self]
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl⟩
  congr 1
  by_cases h : j = 0
  · subst h; rfl
  · simp only [h, decide_false]
    apply beq_false_of_ne
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj'] at this
    exact h this

end VG.Proof.Weierstrass.X86_64
