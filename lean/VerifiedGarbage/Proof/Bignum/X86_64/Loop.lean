import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-!
# Multiword arithmetic on x86-64: loops over the words

`wordLoop start body` runs `body` for `r14 = start, …, w - 1`, with `w` in
`r12`: each iteration ends with `add r14, 1; cmp r14, r12`, and the loop
continues while they differ. `wp_upto` is the loop rule for an invariant
indexed by the counter, and `count_ok` the effect of those two
instructions.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- A loop whose body ends with ZF set when its count `j + 1` reaches `N`:
from `j = a`, the body runs for `j = a, …, N - 1`. -/
theorem wp_upto {body : Prog isa} {a N : Nat} (haN : a < N) (Inv : Nat → State → Prop)
    {Q : State → Prop}
    (hbody : ∀ j, a ≤ j → j < N → ∀ s, Inv j s →
      WP isa body s fun s' => s'.zf = some (decide (j + 1 = N)) ∧ Inv (j + 1) s')
    (hQ : ∀ s, Inv N s → Q s) {s : State} (h0 : Inv a s) : WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = N - j ∧ a ≤ j ∧ j < N ∧ Inv j s) ?_ (N - a) s
    ⟨a, rfl, Nat.le_refl _, haN, h0⟩
  rintro n s ⟨j, rfl, hj, hjN, hI⟩
  refine WP.mono (hbody j hj hjN s hI) fun s' ⟨hz, hI'⟩ => ?_
  by_cases he : j + 1 = N
  · exact .inl ⟨by simp [eval, hz, he], hQ s' (he ▸ hI')⟩
  · exact .inr ⟨by simp [eval, hz, he], N - (j + 1), by omega, j + 1, rfl, by omega, by omega, hI'⟩

theorem ofNat_add_one (j : Nat) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_beq_zero (a b : BitVec 64) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem ofNat_sub_beq {j N : Nat} (hj : j < 2 ^ 64) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 N == 0) = decide (j = N) := by
  rw [sub_beq_zero]
  by_cases h : j = N
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hN] at this

/-- `add r14, 1; cmp r14, r12`. -/
theorem count_ok (s : State) {j N : Nat} (hj : s.gpr .r14 = BitVec.ofNat 64 j)
    (hN : s.gpr .r12 = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)]) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ Keep [.r14] s s' := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hj, hN, ofNat_add_one, ofNat_sub_beq hjN hN']

/-- `add r13, 1; cmp r13, r12`. -/
theorem count13_ok (s : State) {j N : Nat} (hj : s.gpr .r13 = BitVec.ofNat 64 j)
    (hN : s.gpr .r12 = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r12)]) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ Keep [.r13] s s' := by
  refine WP.mono (WP.keep [.r13] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hj, hN, ofNat_add_one, ofNat_sub_beq hjN hN']

/-- `wordLoop start body`: `r14 := start`, then the body and the count for
`r14 = start, …, N - 1`. -/
theorem wordLoop_ok {start N : Nat} {body : List Instr} (hst : start < N) (hN : N < 2 ^ 31)
    (Inv : Nat → State → Prop) {s : State}
    (h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 start → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      Inv start t)
    (hstep : ∀ j, start ≤ j → j < N → ∀ t, Inv j t →
      WP isa (.block (body ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
        t'.zf = some (decide (j + 1 = N)) ∧ Inv (j + 1) t') :
    WP isa (wordLoop start body) s (Inv N) := by
  unfold wordLoop
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 start ∧
    t.mem = s.mem ∧ t.cf = s.cf) (by xrun [sx_ofNat (show start < 2 ^ 31 by omega)]) rfl)
    fun t ⟨⟨h14, hm, hc⟩, k⟩ => ?_)
  exact wp_upto hst Inv hstep (fun _ h => h) (h0 t h14 hm k hc)

end VG.Proof.Bignum.X86_64
