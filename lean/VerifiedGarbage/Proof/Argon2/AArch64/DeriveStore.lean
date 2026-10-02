import VerifiedGarbage.Proof.Argon2.AArch64.DeriveNormalize

/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (aligned : d % 8 = 0) (bound : d < 32768)
    (write : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.str .x r .x19 d]) s (Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store,
    addr, Size.bytes, Size.bits, aligned, bound, and_self, write,
    BitVec.setWidth_eq, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    Frame [⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Stored.other_word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 ≤ 2 ^ 64) (dd : d + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate ed dd) (by decide)

end VG.Proof.Argon2.AArch64.Derive
