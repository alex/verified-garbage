import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowConstants
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch

/-!
# Verification's tables: `[1]A … [15]A` and cached `-[1]B … -[15]B`

Untrusted. The table of multiples of `A` is built by repeated addition of
`A`, each entry representing its multiple (`Rep`); the table of negated
multiples of `B` is stored from constants.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

theorem tableStart_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base) (o : Nat) :
    WP isa (.block (tableStart o)) s fun t => t.gpr .rax = off base o ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [tableStart, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hp, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-! ## Cached `-[i]B` -/

theorem bTablePrefix_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = off base 2048) (n : Nat) (hn : n ≤ 15) :
    WP isa (.block ((List.range n).flatMap fun i => cachedPointStore (negBaseCached i) (128 * i))) s
      fun t => (∀ i < n, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i) ∧
        TableKeep base 2048 (128 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedPointStore_ok (hk.scratch hs) ((hk.gpr _ (by decide)).trans hp)
      (negBaseCached n) (128 * n) (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun i hi => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : i < n
    · rw [(TableFrame.table ku.mem).point (by omega) (Or.inl (by omega)) (by omega), hv i h]
    · obtain rfl : i = n := by omega
      exact hu

/-- What the table of `B`'s multiples leaves. -/
structure BTableStored (base : Addr) (s t : State) : Prop where
  table : ∀ i < 15, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i
  gpr : ∀ r, r ∉ [Reg.rax, .r8, .r9, .r10, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 2048 1920 s.mem t.mem

theorem bTable_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block bTable) s (BTableStored base s) := by
  rw [bTable, WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 2048) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (bTablePrefix_ok (hs.of_keeps ka (by decide)) ap 15 (by decide)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨tv, fun r hr => ?_, kt.rd.trans ka.2.2.1, kt.wr.trans ka.2.2.2, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), ka.1 r (by simp [hr.1])]
  · rw [← ka.2.1]; exact kt.mem

/-! ## `[i]A` -/

theorem rbxNext_ok (s : State) (n : Nat) (hn : n < 15) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 15)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 15)) ∧ Keeps [.rbx] s t := by
  have ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (n + 1) - (15 : BitVec 32).signExtend 64 == 0) = decide (n + 1 = 15) := by
    rw [show (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 15 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    hc, ha, hz, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem rbxSet_ok (s : State) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- The table of `A`'s multiples, with `n` entries and `[n]A` in slots 0–3. -/
structure ATableInv (s₀ : State) (base : Addr) (A : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem base) 0 1 2 3) (n • A)
  table : ∀ j < n, Rep (tablePoint s.mem base (5376 + 128 * j)) ((j + 1) • A)
  a : tablePoint s.mem base 7424 = tablePoint s₀.mem base 7424
  keep : PowersKeep base 5376 1920 s₀ s

theorem aTableBody_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {n : Nat} (hn : n < 15)
    (hA : Rep (tablePoint s₀.mem base 7424) A) (h : ATableInv s₀ base A n s) :
    WP isa (.block (aTableBody fld)) s fun t => t.zf = some (decide (n + 1 = 15)) ∧
      ATableInv s₀ base A (n + 1) t := by
  rw [aTableBody, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (tableStart_ok h.scratch.rdi 7424) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (h.scratch.of_keep kae) ap (by decide) (by decide))
    fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  have b16 : env b.mem base 16 = env s.mem base 16 := by
    change Proof.X25519.X86_64.F b.mem base (offset 16) = Proof.X25519.X86_64.F s.mem base (offset 16)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega)), ka.2.1]
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  have kab := kae.trans kbe
  rw [WP.block_append_iff]
  refine WP.mono (pointAddWide_ok (h.scratch.of_keep kab) (b16.trans h.d)) fun c ⟨kc, cp, ch⟩ => ?_
  have crep : Rep (point (env c.mem base) 0 1 2 3) ((n + 1) • A) := by
    rw [cp, bp, pb, ka.2.1, h.a, succ_nsmul]
    exact pointAdd_rep h.value hA
  have kabc := kab.trans kc
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (h.scratch.of_keep kabc).rdi 5376 n (by omega)
    ((kabc.gpr _ (by decide)).trans h.counter)) fun d ⟨dp, kd⟩ => ?_
  have kde : Keep base c d := Keep.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok (h.scratch.of_keep (kabc.trans kde)) dp (by omega) (by omega))
    fun e ⟨ep, ke⟩ => ?_
  refine WP.mono (rbxNext_ok e n hn ((ke.gpr _ (by decide)).trans ((kde.gpr _ (by decide)).trans
    ((kabc.gpr _ (by decide)).trans h.counter)))) fun t ⟨tc, tz, kt⟩ => ?_
  have kall : PowersKeep base 5376 1920 s t :=
    ((PowersKeep.of_keep (kabc.trans kde)).trans ⟨fun r _ _ hr => ke.gpr r (fun hm => hr (by
      revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl) <;> decide)), ke.rd, ke.wr,
      (TableFrame.table ke.mem).mono (by omega) (by omega)⟩).trans
      (PowersKeep.of_keeps kt (by decide))
  have te : env t.mem base = env e.mem base := by rw [kt.2.1]
  have ee : env e.mem base = env d.mem base := table_env ke.mem (by omega)
  refine ⟨tz, by omega, by omega, kall.scratch h.scratch, tc, ?_, ?_, ?_, ?_, h.keep.trans kall⟩
  · rw [te, ee, kd.2.1]; exact (ch 16 (by decide)).trans (b16.trans h.d)
  · rw [te, ee, kd.2.1]; exact crep
  · intro j hj
    rw [kt.2.1]
    by_cases hjn : j < n
    · rw [(TableFrame.table ke.mem).point (by omega) (Or.inl (by omega)) (by omega), kd.2.1,
        workspace_tablePoint kc.mem (by omega) (by omega), workspace_tablePoint kab.mem (by omega) (by omega)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega
      rw [ep, kd.2.1]; exact crep
  · rw [kt.2.1, (TableFrame.table ke.mem).point (by omega) (Or.inr (by omega)) (by omega), kd.2.1,
      workspace_tablePoint kc.mem (by omega) (by omega), workspace_tablePoint kab.mem (by omega) (by omega)]
    exact h.a

theorem aTableInit_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (.block aTableInit) s (ATableInv s base A 1) := by
  rw [aTableInit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7424) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTable_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  have kab := kae.trans (Keep.of_table kb)
  rw [WP.block_append_iff]
  refine WP.mono (rbxSet_ok b 0 (by decide)) fun c ⟨cc, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok ((hs.of_keep kab).of_keeps kc (by decide)).rdi 5376 0 (by decide) cc)
    fun d ⟨dp, kd⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok (((hs.of_keep kab).of_keeps kc (by decide)).of_keeps kd (by decide))
    dp (by decide) (by decide)) fun e ⟨ep, ke⟩ => ?_
  refine WP.mono (rbxSet_ok e 1 (by decide)) fun t ⟨tc, kt⟩ => ?_
  have hcd : d.mem = b.mem := kd.2.1.trans kc.2.1
  have hbs : env b.mem base 16 = env s.mem base 16 := by
    rw [tableLoad_high kb 16 (by decide), ka.2.1]
  have bA : Rep (point (env b.mem base) 0 1 2 3) A := by rw [pb, ka.2.1]; exact hA
  have kall : PowersKeep base 5376 1920 s t := by
    refine ((((PowersKeep.of_keep kab).trans (PowersKeep.of_keeps kc (by decide))).trans
      (PowersKeep.of_keeps kd (by decide))).trans ⟨fun r _ _ hr => ke.gpr r (fun hm => hr (by
        revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl | rfl | rfl) <;> decide)), ke.rd, ke.wr,
        (TableFrame.table ke.mem).mono (by omega) (by omega)⟩).trans (PowersKeep.of_keeps kt (by decide))
  have ee : env e.mem base = env d.mem base := table_env ke.mem (by omega)
  refine ⟨by decide, by decide, kall.scratch hs, tc, ?_, ?_, ?_, ?_, kall⟩
  · rw [kt.2.1, ee, hcd, hbs, hd]
  · rw [kt.2.1, ee, hcd, one_nsmul]; exact bA
  · intro j hj
    obtain rfl : j = 0 := by omega
    rw [kt.2.1, ep, hcd, zero_add, one_nsmul]; exact bA
  · rw [kt.2.1, (TableFrame.table ke.mem).point (by omega) (Or.inr (by omega)) (by omega), hcd,
      workspace_tablePoint (Keep.of_table kb).mem (by omega) (by omega), ka.2.1]

theorem aTable_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (aTable fld) s (ATableInv s base A 15) := by
  rw [aTable]
  refine WP.seq (WP.mono (aTableInit_ok hs hd hA) fun a ha => ?_)
  apply WP.loop (fun n t => ATableInv s base A (15 - n) t ∧ 0 < n) (n := 14)
  · intro n t ⟨h, hn⟩
    have hp := h.positive
    refine WP.mono (aTableBody_ok (n := 15 - n) (by omega) hA h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 15 - n + 1 = 15
    · exact Or.inl ⟨by simp only [eval, uz, he, decide_true, Option.map_some, Bool.not_true],
        by rw [← he]; exact hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false he, Option.map_some, Bool.not_false],
        n - 1, by omega, by rw [show 15 - (n - 1) = 15 - n + 1 by omega]; exact hu,
        by have := hu.bound; omega⟩
  · exact ⟨ha, by decide⟩

end VG.Proof.Ed25519.X86_64
