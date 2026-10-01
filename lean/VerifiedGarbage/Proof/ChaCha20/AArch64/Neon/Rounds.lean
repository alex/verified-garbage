import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Quarter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.RoundSpec

namespace VG.Proof.ChaCha20.AArch64.Neon

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon
open VG.Spec.ChaCha20 (innerBlock)

theorem rowReg_0 : rowReg 0 = .v0 := rfl
theorem rowReg_1 : rowReg 1 = .v1 := rfl
theorem rowReg_2 : rowReg 2 = .v2 := rfl
theorem rowReg_3 : rowReg 3 = .v3 := rfl

def Holds (v : CState) (s : State) : Prop :=
  ∀ r (hr : r < 4), ∀ e (he : e < 4), vword (s.v (rowReg r)) e = v[4 * r + e]'(by omega)

structure Keeps (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s s' s'' : State} (h : Keeps s s') (h' : Keeps s' s'') : Keeps s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem columns_ok {s : State} {v : CState} (h : Holds v s) :
    WP isa (.block qr) s fun s' => Holds (columns v) s' ∧ Keeps s s' := by
  refine (qr_ok s).mono fun s' ⟨hq, hg, hm, hr, hw, hp⟩ => ⟨?_, hg, hm, hr, hw, hp⟩
  intro r hr e he
  have hq' := hq e he
  have hc := columns_get v e he
  have h0 := h 0 (by decide) e he
  have h1 := h 1 (by decide) e he
  have h2 := h 2 (by decide) e he
  have h3 := h 3 (by decide) e he
  simp only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, Nat.reduceMul, Nat.zero_add] at h0 h1 h2 h3
  rw [h0, h1, h2, h3] at hq'
  interval_cases r <;> simp only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, Nat.reduceMul, Nat.zero_add]
  · exact hq'.1.trans hc.1.symm
  · exact hq'.2.1.trans hc.2.1.symm
  · exact hq'.2.2.1.trans hc.2.2.1.symm
  · exact hq'.2.2.2.trans hc.2.2.2.symm

theorem diagonal_ok {s : State} {v : CState} (h : Holds v s) :
    WP isa (.block diagonal) s fun s' => Holds (align v) s' ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [diagonal, runBlock_cons, runBlock_nil, exec, VOp.eval,
    ite_true, ite_false, Option.map_some, isa, runStep_some, Option.some.injEq, exists_eq_left',
    RegUpd.v_setV]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  intro r hr e he
  interval_cases r <;>
    simp (config := {decide := true}) only [rowReg_0, rowReg_1, rowReg_2, rowReg_3,
      RegUpd.v_setV, ite_true, ite_false, align_get, Nat.reduceMul, Nat.zero_add]
  · simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, Nat.div_eq_of_lt he, Nat.mod_eq_of_lt he, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero] using h 0 (by decide) e he
  · rw [vword_ext _ 1 e (by decide) he]
    simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, show (4 + e) / 4 = 1 by omega, show (4 + e) % 4 = e by omega,
      Nat.reduceMul] using h 1 (by decide) ((e + 1) % 4) (by omega)
  · rw [vword_ext _ 2 e (by decide) he]
    simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, show (8 + e) / 4 = 2 by omega, show (8 + e) % 4 = e by omega,
      Nat.reduceMul] using h 2 (by decide) ((e + 2) % 4) (by omega)
  · rw [vword_ext _ 3 e (by decide) he]
    simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, show (12 + e) / 4 = 3 by omega, show (12 + e) % 4 = e by omega,
      Nat.reduceMul] using h 3 (by decide) ((e + 3) % 4) (by omega)

theorem undiagonal_ok {s : State} {v : CState} (h : Holds v s) :
    WP isa (.block undiagonal) s fun s' => Holds (unalign v) s' ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [undiagonal, runBlock_cons, runBlock_nil, exec, VOp.eval,
    ite_true, ite_false, Option.map_some, isa, runStep_some, Option.some.injEq, exists_eq_left',
    RegUpd.v_setV]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  intro r hr e he
  interval_cases r <;>
    simp (config := {decide := true}) only [rowReg_0, rowReg_1, rowReg_2, rowReg_3,
      RegUpd.v_setV, ite_true, ite_false, unalign_get, Nat.reduceMul, Nat.zero_add]
  · simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, Nat.div_eq_of_lt he, Nat.mod_eq_of_lt he, Nat.mul_zero, Nat.zero_add,
      Nat.sub_zero, show (e + 4) % 4 = e by omega] using h 0 (by decide) e he
  · rw [vword_ext _ 3 e (by decide) he]
    simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, show (4 + e) / 4 = 1 by omega, show (4 + e) % 4 = e by omega,
      Nat.reduceMul, show e + 4 - 1 = e + 3 by omega] using h 1 (by decide) ((e + 3) % 4) (by omega)
  · rw [vword_ext _ 2 e (by decide) he]
    simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, show (8 + e) / 4 = 2 by omega, show (8 + e) % 4 = e by omega,
      Nat.reduceMul, show e + 4 - 2 = e + 2 by omega] using h 2 (by decide) ((e + 2) % 4) (by omega)
  · rw [vword_ext _ 1 e (by decide) he]
    simpa only [rowReg_0, rowReg_1, rowReg_2, rowReg_3, show (12 + e) / 4 = 3 by omega, show (12 + e) % 4 = e by omega,
      Nat.reduceMul, show e + 4 - 3 = e + 1 by omega] using h 3 (by decide) ((e + 1) % 4) (by omega)

theorem doubleRound_ok {s : State} {v : CState} (h : Holds v s) :
    WP isa doubleRound s fun s' => Holds (innerBlock v) s' ∧ Keeps s s' := by
  unfold doubleRound
  refine WP.seq ((columns_ok h).mono fun s₁ ⟨h₁, k₁⟩ => ?_)
  refine WP.seq ((diagonal_ok h₁).mono fun s₂ ⟨h₂, k₂⟩ => ?_)
  refine WP.seq ((columns_ok h₂).mono fun s₃ ⟨h₃, k₃⟩ => ?_)
  exact (undiagonal_ok h₃).mono fun s' ⟨h', k'⟩ =>
    ⟨innerBlock_eq v ▸ h', ((k₁.trans k₂).trans k₃).trans k'⟩

theorem rounds_ok {s : State} {v : CState} (h : Holds v s) :
    ∀ n, WP isa (rounds n) s fun s' => Holds (Nat.repeat innerBlock n v) s' ∧ Keeps s s'
  | 0 => WP.block_nil ⟨h, Keeps.refl s⟩
  | n + 1 => WP.seq ((rounds_ok h n).mono fun _ ⟨h', k⟩ =>
      (doubleRound_ok h').mono fun _ ⟨h'', k'⟩ => ⟨h'', k.trans k'⟩)

end VG.Proof.ChaCha20.AArch64.Neon
