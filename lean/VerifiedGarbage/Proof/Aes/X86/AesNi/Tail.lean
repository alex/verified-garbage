import VerifiedGarbage.Proof.Aes.X86.AesNi.Invariant

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre datP nBlk)

/-- Bounded natural counts are zero exactly when their word is zero. -/
theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have he : BitVec.ofNat 32 k ≠ 0 := fun e => h (by
      have he := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at he)
    rw [beq_eq_false_iff_ne.mpr he]
    simp [h]

/-- Public pointer and remaining-count advancement, without changing memory. -/
theorem advance_ok {s₀ : State} (hp : CPre s₀) {c p n : Nat}
    (hn : p + n ≤ nBlk s₀) {s : State} (hI : Inv s₀ c p s) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (16 * n))),
      .alu .sub .edi (.imm (BitVec.ofNat 32 n))]) s fun s' =>
      Inv s₀ c (p + n) s' ∧ s'.zf = some (decide (nBlk s₀ - (p + n) = 0)) := by
  have hw := hp.fD
  have hsub : BitVec.ofNat 32 (nBlk s₀ - p) - BitVec.ofNat 32 n =
      BitVec.ofNat 32 (nBlk s₀ - (p + n)) := by
    rw [Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 32) (by omega)
  have hadd : (datP s₀ + BitVec.ofNat 32 (16 * p)) + BitVec.ofNat 32 (16 * n) =
      datP s₀ + BitVec.ofNat 32 (16 * (p + n)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun k => datP s₀ + BitVec.ofNat 32 k) (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    isa, exec, execAlu, readSrc, gpr_setReg, gpr_arithFlags, hI.esi, hI.edi,
    ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with esi := ?_, edi := ?_ }, ?_⟩
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hI.esi]
    exact hadd
  · simp only [gpr_setReg_self]
    exact hsub
  · rw [zf_setReg, zf_arithFlags, hsub, beq_ofNat_zero (by omega)]

/-- The bulk-loop branch depends only on the public remaining count. -/
theorem cmpEdi_ok {s₀ : State} {c p n : Nat} (hn : n < 2 ^ 32)
    (hp : p ≤ nBlk s₀) {s : State} (hI : Inv s₀ c p s) :
    WP isa (.block [.alu .cmp .edi (.imm (BitVec.ofNat 32 n))]) s fun s' =>
      Inv s₀ c p s' ∧ s'.cf = some (decide (nBlk s₀ - p < n)) := by
  have hnb : nBlk s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu,
    readSrc, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hI.le, hI.ebx, hI.esp, hI.ecx, hI.edx, hI.ebp, hI.esi, hI.edi,
    hI.rd, hI.wr, hI.frame, hI.saved, hI.scratchPrefix, hI.blocks⟩, ?_⟩
  simp only [cf_arithFlags, hI.edi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show nBlk s₀ - p < 2 ^ 32 by omega)]

/-- Zero detection between the bulk and tail loops also uses only the count. -/
theorem testEdi_ok {s₀ : State} {c p : Nat} {s : State} (hI : Inv s₀ c p s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      Inv s₀ c p s' ∧ s'.zf = some (decide (nBlk s₀ - p = 0)) := by
  have hnb : nBlk s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu,
    readSrc, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hI.le, hI.ebx, hI.esp, hI.ecx, hI.edx, hI.ebp, hI.esi, hI.edi,
    hI.rd, hI.wr, hI.frame, hI.saved, hI.scratchPrefix, hI.blocks⟩, ?_⟩
  rw [zf_arithFlags, BitVec.and_self, hI.edi, beq_ofNat_zero (by omega)]

end VG.Proof.Aes.X86.AesNi
