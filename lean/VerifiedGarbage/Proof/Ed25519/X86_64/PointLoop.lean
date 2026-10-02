import VerifiedGarbage.Impl.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points

/-! Sixteen exact doublings, preserving the saved accumulator. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (clob Outside Keeps)

variable {fld : Arith} [EdArith fld]

structure DoubleKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rsi → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem DoubleKeep.refl (base : Addr) (s : State) : DoubleKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem DoubleKeep.trans {base : Addr} {s t u : State} (h : DoubleKeep base s t)
    (k : DoubleKeep base t u) : DoubleKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem DoubleKeep.scratch {base : Addr} {s t : State} (h : DoubleKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem point_counter_zero : ∀ n < 16,
    (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem doubleDec_ok (s : State) (n : Nat) (hn : n < 16)
    (hc : s.gpr .rsi = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rsi (.imm 1)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧ Keeps [.rsi] s t := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags,
    hc, point_counter_zero n hn, e, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem doubleBody_ok {s : State} {base : Addr} (hs : Scratch s base) (n : Nat) (hn : n < 16)
    (hc : s.gpr .rsi = BitVec.ofNat 64 (n + 1)) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (doubleBody fld)) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (point (env s.mem base) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (pointDoubleWide_ok hs hd) fun t ⟨hk, hv, hi⟩ => ?_
  refine WP.mono (doubleDec_ok t n hn ((hk.gpr _ (by decide)).trans hc)) fun u ⟨hcu, hzu, ku⟩ => ?_
  refine ⟨hcu, hzu, ?_, ?_, ?_⟩
  · rw [ku.2.1]; exact hv
  · rw [ku.2.1]; exact hi
  · exact ⟨fun r hr hc => (ku.1 r (by simpa using hr)).trans (hk.gpr r hc),
      ku.2.2.1.trans hk.rd, ku.2.2.2.trans hk.wr, by rw [ku.2.1]; exact hk.mem⟩

structure DoubleInv (s₀ : State) (base : Addr) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scratch s base
  counter : s.gpr .rsi = BitVec.ofNat 64 n
  value : point (env s.mem base) 0 1 2 3 =
    powerPoint (point (env s₀.mem base) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem base i = env s₀.mem base i
  keep : DoubleKeep base s₀ s

theorem doubleLoop_ok {s₀ : State} {base : Addr} (hs : Scratch s₀ base)
    (hc : s₀.gpr .rsi = 16) (hd : env s₀.mem base 16 = Spec.Ed25519.d) :
    WP isa (.loop (.block (doubleBody fld)) .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s₀.mem base i) ∧ DoubleKeep base s₀ t := by
  apply WP.loop (DoubleInv s₀ base) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega
    refine WP.mono (doubleBody_ok hi.scratch k hk hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htv, hthi, htk⟩ => ?_
    have hv : point (env t.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s₀.mem base i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, htz, decide_true, Option.map_some, Bool.not_true], hv, hh, hkeep⟩
    · exact Or.inr ⟨by simp only [eval, htz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hs, hc, rfl, fun _ _ => rfl, DoubleKeep.refl _ _⟩

theorem doubleInit_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.imm 16)]) s fun t => t.gpr .rsi = 16 ∧ Keeps [.rsi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem double16_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (double16 fld) s fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s.mem base) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double16]
  refine WP.seq (WP.mono (doubleInit_ok s) fun t ⟨hc, hk⟩ => ?_)
  have hs' : Scratch t base := ⟨(hk.1 _ (by decide)).trans hs.rdi, hk.2.2.2 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (doubleLoop_ok hs' hc (by rw [hk.2.1]; exact hd)) fun u ⟨hv, hh, hu⟩ => ?_
  have hkeep : DoubleKeep base s t := ⟨fun r hr _ => hk.1 r (by simpa using hr),
    hk.2.2.1, hk.2.2.2, by rw [hk.2.1]; exact Outside.refl _ _ _ _⟩
  rw [hk.2.1] at hv hh
  exact ⟨hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.X86_64
