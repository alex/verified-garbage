import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulate

/-! Untrusted: the descending-bit loop follows the specification exactly. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)

theorem accumulateDec_ok (s : State) (n : Nat)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s t := by
  have e : BitVec.ofNat 64 (n + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hc, e, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem accumulateTest_ok (s : State) (n : Nat) (hn : n < 16)
    (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (n = 0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, BitVec.and_self, point_counter_zero n hn,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem accumulateBody_ok {s : State} {base : Addr} (hs : Scratch s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem base (5376 + 128 * n) = powerPoint p (start + n)) :
    WP isa (.block accumulateBody) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s t := by
  rw [accumulateBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAccumulate_ok (hs.of_keeps ka (by decide)) n start ((scalar / 2 ^ (start + n)) % 2) hn hi (by omega) ac
    ((ka.1 _ (by decide)).trans hstart) (by rw [ka.2.1]; exact hb) (by rw [ka.2.1]; exact hd))
    fun b ⟨kb, bp, bd⟩ => ?_
  have bc : b.gpr .rbx = BitVec.ofNat 64 n := (kb.gpr _ (by decide)).trans ac
  refine WP.mono (accumulateTest_ok b n hn bc) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kt.1 _ (by simp)).trans bc, tz, ?_, ?_, ?_⟩
  · rw [kt.2.1, bp, ka.2.1, hp, ht, ← after_step]
  · rw [kt.2.1]; exact bd
  · exact ((RbxKeep.of_keeps ka (by decide)).trans (RbxKeep.of_keep kb)).trans
      (RbxKeep.of_keeps kt (by decide))

structure AccumulateInv (s₀ : State) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  startReg : s.gpr .rsi = BitVec.ofNat 64 start
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = powerPoint p (start + i)
  keep : RbxKeep base s₀ s

theorem RbxKeep.refl (base : Addr) (s : State) : RbxKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem accumulateLoop_ok {s₀ : State} {base : Addr} (hs : Scratch s₀ base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hc : s₀.gpr .rbx = 16) (hstart : s₀.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s₀.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : env s₀.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s₀.mem base (5376 + 128 * i) = powerPoint p (start + i)) :
    WP isa (.loop (.block accumulateBody) .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s₀ t := by
  apply WP.loop (AccumulateInv s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok h.scratch k start scalar p hk (by omega) h.counter h.startReg
      (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tz, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (off base (768 + (start + i))) =
        BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2) := by
      intro i hi'
      rw [tk.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits i hi']
    have ht' : ∀ i < 16, tablePoint t.mem base (5376 + 128 * i) = powerPoint p (start + i) := by
      intro i hi'
      rw [workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, td, h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, tk.scratch h.scratch, tc,
          (tk.gpr _ (by decide) (by decide)).trans h.startReg, td, tv, hb', ht', h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hs, hc, hstart, hd, hp, hb, ht, RbxKeep.refl _ _⟩

theorem accumulateInit_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 16)]) s fun t => t.gpr .rbx = 16 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem accumulate16_ok {s : State} {base : Addr} (hs : Scratch s base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = powerPoint p (start + i)) :
    WP isa accumulate16 s fun t => point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s t := by
  rw [accumulate16]
  refine WP.seq (WP.mono (accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  refine WP.mono (accumulateLoop_ok (hs.of_keeps ka (by decide)) start scalar p hi ac
    ((ka.1 _ (by decide)).trans hstart) (by rw [ka.2.1]; exact hb)
    (by rw [ka.2.1]; exact hd) (by rw [ka.2.1]; exact hp) (by rw [ka.2.1]; exact ht))
    fun t ⟨tv, td, tk⟩ => ?_
  exact ⟨tv, td, (RbxKeep.of_keeps ka (by decide)).trans tk⟩

end VG.Proof.Ed25519.X86_64
