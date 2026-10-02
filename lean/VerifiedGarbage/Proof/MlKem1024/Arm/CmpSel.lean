import VerifiedGarbage.Proof.MlKem1024.Arm.Prf
import VerifiedGarbage.Proof.MlKem.Arm.CmpSel

/-!
# ML-KEM-1024 on 32-bit ARM: comparing `c` with `c'`

`compare_ok` of `Proof/MlKem/Arm/CmpSel.lean` for the 1568 bytes of an
ML-KEM-1024 ciphertext (`compare4`); the mask and the selection of the key are
those of ML-KEM-768.
-/

namespace VG.Proof.MlKem1024.Arm

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm

theorem cmpArgs_ok {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C) :
    WP isa (.block [.mov .r0 (.reg .r6), ptrTo .r1 .r7 oCt4, .mov .r12 (.imm 0), .mov .r9 (.imm 1568)]) s
      fun s' => s'.gpr .r0 = C ∧ s'.gpr .r1 = P + BitVec.ofNat 32 oCt4 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r9 = BitVec.ofNat 32 1568 ∧ (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e1 : encodable (BitVec.ofNat 32 oCt4) = true := by decide
  have e2 : encodable (0 : BitVec 32) = true := by decide
  have e3 : encodable (1568 : BitVec 32) = true := by decide
  run_block [ptrTo, e1, e2, e3, h7, h6, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-- `compare`: `r12` is 0 exactly when the 1568 bytes at `C` (in `r6`) and at
`P + 22528` (`r7 = P`) are equal. -/
theorem compare_ok {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C)
    (fC : C.toNat + 1568 ≤ 2 ^ 32) (fD : (P + BitVec.ofNat 32 oCt4).toNat + 1568 ≤ 2 ^ 32)
    (cr : Covers [⟨State.addr C, 1568⟩, ⟨State.addr (P + BitVec.ofNat 32 oCt4), 1568⟩] (s.rd ++ s.wr)) :
    WP isa compare4 s fun s' => (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (s'.gpr .r12).toNat < 256 ∧
      (s'.gpr .r12 = 0 ↔ bytesAt s.mem (State.addr C) 1568 = bytesAt s.mem (State.addr (P + BitVec.ofNat 32 oCt4)) 1568) := by
  refine WP.seq (WP.mono (cmpArgs_ok h7 h6) fun s₁ ⟨g0, g1, g12, g9, cs, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_ne (CmpInv C (P + BitVec.ofNat 32 oCt4) 1568 s₁) (N := 1568) (by decide)
    (fun k hk s h => cmp_step fC fD (by decide) (by rw [rd, wr]; exact cr) hk h)
    (fun s' h => ⟨fun r hr h9 => (h.cs r hr h9).trans (cs r hr h9), h.mem.trans m, h.rd.trans rd, h.wr.trans wr,
      h.sp.trans sp, h.lt, ?_⟩)
    ⟨by rw [g0]; simp, by rw [g1]; simp, by rw [g9], fun _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by rw [g12]; decide, by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  rw [h.eq, ← m]
  constructor
  · intro he
    exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [he t ht, bytesAt_getElem]
  · intro he t ht
    have := congrArg (fun L : List Byte => L[t]!) he
    simp only [bytesAt_getElem! _ _ ht] at this
    exact this

end VG.Proof.MlKem1024.Arm
