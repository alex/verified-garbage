import VerifiedGarbage.Proof.Rc4.AArch64.KsaSetup
import VerifiedGarbage.Proof.Rc4.AArch64.ApplyFinish
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The key schedule

`init_ok`: `vg_rc4_init` checks the key length, and for a valid one leaves
the key schedule with both indices zero at `ctx`, preserving the low halves
of `v8`–`v15`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ctxRegs_ok (a : State) :
    WP isa (.block [.addImm .x .x0 .x2 0, .movz .x .x9 255 0]) a fun b =>
      b.gpr .x0 = a.gpr .x2 ∧ b.gpr .x9 = 255#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x9 → b.gpr r = a.gpr r) ∧
      b.v = a.v ∧ b.mem = a.mem ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  rrun
  refine ⟨fun r h0 h9 => by simp [h0, h9], ?_⟩
  simp [State.write]

theorem zeros_ok {b : State} (hp : InRegions b.wr (b.gpr .x0) 258) :
    WP isa (.block [.movz .w .x6 0 0, .strb .x6 .x0 256, .strb .x6 .x0 257, .movz .w .x0 0 0]) b
      fun c => c.mem = (b.mem.write (b.gpr .x0 + 256#64) 1 0).write (b.gpr .x0 + 257#64) 1 0 ∧
        c.gpr .x0 = 0#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x6 → c.gpr r = b.gpr r) ∧ c.v = b.v ∧
        c.rd = b.rd ∧ c.wr = b.wr ∧ c.sp = b.sp := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hz : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 0#16))) =
    0#8 := by decide
  rrun [State.store, h256, h257]
  refine ⟨by rw [hz], fun r a b => by simp [a, b], by simp [State.write]⟩

theorem ksaFinish_ok {g : KGlob} {u : State} (h : KsaInv g 256 0 u)
    (hp : InRegions u.wr (u.gpr .x2) 258) :
    WP isa (.block scheduleFinish) u fun t =>
      t.gpr .x0 = 0#64 ∧
      contextAt t.mem (u.gpr .x2) = { table := (schedulePrefix g.key 256).1, i := 0, j := 0 } ∧
      (∀ p ∈ saved false, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved false, p.1 ≠ v) → t.v v = u.v v) ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  unfold scheduleFinish
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ctxRegs_ok u) fun a ⟨a0, a9, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff, storeTable_eq]
  have a8 : a.gpr .x8 = BitVec.ofNat 64 256 := by rw [ag _ (by decide) (by decide)]; exact h.x8
  have hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  have hpa' : InRegions a.wr (a.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpa
  refine WP.mono (storeN_ok (by decide) a8 a9 hpa' (Nat.le_refl 16))
    fun b ⟨brow, _, bv, bg, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  have b0 : b.gpr .x0 = a.gpr .x0 := bg _ (by decide) (by decide)
  refine WP.mono (zeros_ok (by rw [bwr, b0]; exact hpa)) fun c ⟨cm, c0, cg, cv, crd, cwr, csp⟩ => ?_
  refine WP.mono (restore_ok false c) fun t ⟨tsv, tv, tg, tm, trd, twr, tsp⟩ => ?_
  have hT : TableIn a 256 (schedulePrefix g.key 256).1 := fun k hk => by
    rw [show tbyte a.v = tbyte u.v by rw [av]]; exact h.table k hk
  refine ⟨?_, ?_, fun p hp => ?_, fun v hv => ?_, ?_, ?_, ?_⟩
  · rw [tg, c0]
  · rw [tm, cm, b0, a0, context_finish, ← a0, stored_table (by decide) hT brow]
  · have ⟨n0, n6, n7, n9⟩ : p.2 ≠ .x0 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧ p.2 ≠ .x9 := by revert p; decide
    rw [tsv p hp, cg _ n0 n6, bg _ n6 n7, ag _ n0 n9]
  · rw [tv v hv, cv, bv, av]
  · rw [trd, crd, brd, ard]
  · rw [twr, cwr, bwr, awr]
  · rw [tsp, csp, bsp, asp]

theorem savedK_v : ∀ r ∈ preservedV, r = .v14 ∨ r = .v15 ∨ ∃ p ∈ saved false, p.1 = r := by decide

theorem savedK_kept : ∀ p ∈ saved false, p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧
    p.2 ≠ .x8 := by decide

theorem initValid_ok (s : State) (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa initValid s fun t => t.gpr .x0 = 0#64 ∧
      contextAt t.mem (s.gpr .x2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat), i := 0, j := 0 } ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  unfold initValid
  refine WP.seq (WP.mono (ksaSetup_ok hL hk)
    fun t ⟨hok, hi, tsv, tg, t14, t15, _, _, twr, _⟩ => ?_)
  refine WP.seq (WP.mono (ksaLoop_ok hok 16 ⟨0, rfl, rfl, by decide, hi⟩) fun u hu => ?_)
  have u2 : u.gpr .x2 = s.gpr .x2 := by
    rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact tg _ (by decide)
  have hpu : InRegions u.wr (u.gpr .x2) 258 := by
    rw [hu.wr, u2]; show InRegions t.wr _ _; rw [twr]; exact hp
  refine WP.mono (ksaFinish_ok hu hpu) fun w ⟨w0, wc, wsv, wv, _, _, _⟩ => ?_
  refine ⟨w0, ?_, fun r hr => ?_⟩
  · rw [← u2, wc, keySchedule_eq]; rfl
  · have hn : ∀ p ∈ saved false, p.1 ≠ .v14 ∧ p.1 ≠ .v15 := by decide
    rcases savedK_v r hr with rfl | rfl | ⟨p, hp, rfl⟩
    · rw [wv _ fun p hp => (hn p hp).1, hu.vkept _ (by decide)]; exact congrArg _ t14
    · rw [wv _ fun p hp => (hn p hp).2, hu.vkept _ (by decide)]; exact congrArg _ t15
    · obtain ⟨a4, a5, a6, a7, a8⟩ := savedK_kept p hp
      rw [wsv p hp, hu.gpr _ a4 a5 a6 a7 a8]
      exact tsv p hp

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = 0#64 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa VG.Impl.Rc4.AArch64.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
      | .ok ctx => t.gpr .x0 = 0#64 ∧ contextAt t.mem (s.gpr .x2) = ctx
      | .error .invalidKeyLength => t.gpr .x0 = 1#64) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have hcheck : WP isa (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x4 = (s.gpr .x1 - 1#64) >>> 8 := by rrun
  unfold VG.Impl.Rc4.AArch64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htv, ht0, ht1, ht2, ht4⟩ := ht
  let good := 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256
  have hcond : isa.eval (.nonzero .x .x4) t = some (decide (¬ good)) := by
    simp only [eval, State.read, BitVec.setWidth_eq, ht4, BitVec.ofNat_eq_ofNat, bne]
    apply congrArg some
    by_cases hg : good
    · have hz := (valid_length (s.gpr .x1)).mpr hg
      rw [hz, beq_self_eq_true]
      simp only [hg, not_true_eq_false, decide_false, Bool.not_true]
    · have hn : (s.gpr .x1 - 1#64) >>> 8 ≠ 0#64 := fun hz => hg ((valid_length _).mp hz)
      rw [beq_eq_false_iff_ne.mpr hn]
      simp only [hg, not_false_eq_true, decide_true, Bool.not_false]
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
    exact fun r _ => by rw [htv]
  · have hg : good := by
      have hnn := of_decide_eq_false hy
      exact Classical.not_not.mp hnn
    change 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hpt : InRegions t.wr (t.gpr .x2) 258 := by rw [htw, ht2]; exact hp
    have hkt : InRegions (t.rd ++ t.wr) (t.gpr .x0) (t.gpr .x1).toNat := by
      rw [htr, htw, ht0, ht1]; exact hk
    have hlt : 0 < (t.gpr .x1).toNat ∧ (t.gpr .x1).toNat ≤ 256 := by rw [ht1]; omega
    refine WP.mono (initValid_ok t hlt hpt hkt) fun u ⟨u0, uc, uv⟩ => ?_
    refine ⟨⟨u0, ?_⟩, fun r hr => by rw [uv r hr, htv]⟩
    rw [← ht2, uc, htm, ht0, ht1]

end VG.Proof.Rc4.AArch64
