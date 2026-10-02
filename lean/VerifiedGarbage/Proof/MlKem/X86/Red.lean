import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Impl.MlKem.X86.Ntt

/-!
# ML-KEM on x86 (32-bit): Barrett reduction and products

`red r` reduces `x < 2³²`, held in `eax` and in `r`, modulo `q` (`red_spec`):
`barrett64` with the quotient estimate the high half of a `mul`, then
`condSub`. `mul r` multiplies (`wp_mul`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- `mul r` -/
theorem wp_mul {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (execMul r s) Q) : WP isa (.block (.mul r :: is)) s Q :=
  wp_cons rfl k

theorem execMul_eax (r : Reg) (s : State) :
    (execMul r s).gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) := by
  simp [execMul, State.setReg, State.setFlags]

theorem execMul_other (r : Reg) (s : State) {x : Reg} (h1 : x ≠ .eax) (h2 : x ≠ .edx) :
    (execMul r s).gpr x = s.gpr x := by
  simp [execMul, State.setReg, State.setFlags, h1, h2]

theorem execMul_only (r : Reg) (s : State) : Only [.eax, .edx] s (execMul r s) :=
  ⟨fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact execMul_other r s hx.1 hx.2, rfl, rfl, rfl⟩

/-- `red r` leaves `x mod q` in `r` from `eax = r = x`, changing only `eax`, `edx`, `r` and the
flags. -/
theorem red_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (ha : (s.gpr .eax).toNat = x) (hr : (s.gpr r).toNat = x)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = x % q → WP isa (.block is) s' P) :
    WP isa (.block (red r ++ is)) s P := by
  have hx : x < 2 ^ 32 := by rw [← ha]; exact (s.gpr .eax).isLt
  have h2' : Reg.edx ≠ r := fun e => h2 e.symm
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [red, csub, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left', h1, h2,
    h2']
  refine k _ ⟨fun q hq => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [hq.1, hq.2.1, hq.2.2]
  · simp only [ite_true]
    have hb := barrett64_bounds hx
    have hq1 : (BitVec.ofNat 32 (x * 1290167 / 2 ^ 32)).toNat = barrett64Quot x := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold barrett64Quot at *; omega)]; rfl
    have hm : (BitVec.ofNat 32 (3329 * barrett64Quot x)).toNat = barrett64Quot x * q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [q_eq] at hb; omega), q_eq, Nat.mul_comm]
    have e : (s.gpr r - BitVec.ofNat 32 ((3329 : BitVec 32).toNat *
        (BitVec.ofNat 32 ((s.gpr .eax).toNat * (1290167 : BitVec 32).toNat / 2 ^ 32)).toNat)).toNat =
        barrett64 x := by
      rw [ha, show (1290167 : BitVec 32).toNat = 1290167 from rfl, hq1,
        show (3329 : BitVec 32).toNat = 3329 from rfl]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hm, hr]; exact hb.2), hm, hr]
      rfl
    rw [csub_eq _ _ (by rw [e]; exact barrett64_lt hx), e, toNat_ofNat32 (by
      have := barrett64_lt hx; rw [q_eq] at this ⊢; omega), barrett64_mod hx]

end VG.Proof.MlKem.X86
