import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableLoad

/-! Public point-table address arithmetic. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps)

theorem tableAddr_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (o j : Nat) (hj : j < 64) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (tableAddr o)) s fun t =>
      t.gpr .rax = off base (o + 128 * j) ∧ Keeps [.rax, .rcx, .rdx] s t := by
  have hval : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [tableAddr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hc, hp, hval,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change BitVec.ofNat 64 (j * 128) + base + BitVec.ofNat 64 o = _
    rw [BitVec.add_comm (BitVec.ofNat 64 (j * 128)), BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun n => off base n) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Ed25519.X86_64
