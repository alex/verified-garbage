import VerifiedGarbage.Proof.CmacAes.AArch64.Contract
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update`, the blocks before and in the loop

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64

/-- The memory after saving the registers. -/
def savedMem (s : State) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (s.gpr .x5 + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2120 → InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save ++ setup) s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧ s'.gpr .x21 = s.gpr .x2 ∧
      s'.gpr .x22 = s.gpr .x3 ∧ s'.gpr .x23 = s.gpr .x4 ∧ s'.gpr .x24 = s.gpr .x5 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [save, setup, saved, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some,
      hw 2064 (by decide) (by decide), hw 2072 (by decide) (by decide), hw 2080 (by decide) (by decide),
      hw 2088 (by decide) (by decide), hw 2096 (by decide) (by decide), hw 2104 (by decide) (by decide),
      hw 2112 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, rfl, ?_, rfl, rfl⟩
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  · simp only [mem_write, savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem chainIn_ok (s : State) {C P Q : Addr} (hc : s.gpr .x24 + BitVec.ofNat 64 2048 = C)
    (hp : s.gpr .x21 = P) (hq : s.gpr .x22 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (chainIn ++ updArgs) s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = C ∧ s'.gpr .x3 = P ∧
      s'.gpr .x4 = 1 ∧ s'.gpr .x5 = s.gpr .x24 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = Proof.Cmac.chainMem s.mem C P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : s.gpr .x24 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [← hc, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp (config := {decide := true}) only [chainIn, updArgs, ctrArgs, cOff, mov, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, ite_true, ite_false,
      Option.bind_some, Option.map_some, hc, hc', hp, hq, BitVec.add_zero, BitVec.setWidth_eq,
      rp, rp8, rq, rq8, wc, wc8, wp, wp8]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_write, mem_write, rd_write, wr_write, sp_write,
    ite_true, ite_false, BitVec.setWidth_eq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [Proof.Cmac.chainMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]
    rfl

end VG.Proof.CmacAes.AArch64
