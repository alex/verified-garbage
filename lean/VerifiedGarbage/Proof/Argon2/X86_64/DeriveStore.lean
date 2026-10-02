import VerifiedGarbage.Proof.Argon2.X86_64.DeriveNormalize

/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (Impl.Argon2.X86_64.at_ .rbp d) r]) s (Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast, write,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Stored.other_word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 ≤ 2 ^ 64) (dd : d + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate ed dd) (by decide)

end VG.Proof.Argon2.X86_64.Derive
