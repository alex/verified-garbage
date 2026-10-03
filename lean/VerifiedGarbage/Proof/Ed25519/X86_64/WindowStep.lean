import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarStep
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Framework.RelCT

/-! Merged from `Proof.Ed25519.X86_64.WindowTables`. -/
section
/-!
# Verification's tables: `[1]A … [15]A` and cached `-[1]B … -[15]B`

The table of multiples of `A` is built by repeated addition of `A`, each entry
representing its multiple (`Rep`); the table of negated multiples of `B` is
stored from constants.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)
open VG.Impl.Ed25519 (negBaseCached)

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
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyFrame`. -/
section
/-! Verification preserves input buffers and its saved pointers. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside)

theorem tableFrame_work {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : o ≤ 64) (hn : 768 ≤ o + n) : Outside base o n m m' :=
  fun p hp => h p (by omega) hp

theorem outside_bytes {base p : Addr} {o n len : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192)
    (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt m' p len = Spec.Ed25519.bytesAt m p len := by
  apply List.map_congr_left
  intro i hi
  apply h
  change ofs base (off p i) < o ∨ o + n ≤ ofs base (off p i)
  have := hf i (List.mem_range.mp hi)
  omega

theorem PowersKeep.header {base : Addr} {o n d : Nat} {s t : State}
    (h : PowersKeep base o n s t) (hd : 7936 ≤ d) (hb : d + 8 ≤ 8192) (hn : o + n ≤ 7936) :
    t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (by omega) (Or.inr (by omega)) (by omega)

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.VerifyInputs`. -/
section
/-! Reload verification pointers and check the complete unsigned scalar S. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Proof.X25519.X86_64 (off Keeps ea_at ea_sc val4)

theorem loadPointer_ok {s : State} {base : Addr} (hs : Scratch s base) (r : Reg) (d : Nat)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, hs.rdi, hr, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)

theorem add32_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.imm 32)]) s fun t => t.gpr r = off (s.gpr r) 32 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨rfl, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem loadScalarWords_ok (s : State) (p : Addr) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadScalarWords) s fun t =>
      scalarValue t = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [loadScalarWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hp, hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left', scalarValue]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact (decodeLE_inputWords s.mem p).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem verifyScalar_ok {s : State} {base sig : Addr} (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8) :
    WP isa (.block verifyScalar) s fun t => Keep base s t ∧ t.mem = s.mem ∧
      t.cf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) < Spec.Ed25519.L)) := by
  change WP isa (.block (([.mov .rdx (.mem (sc 7944))] : List Instr) ++
    ([.alu .add .rdx (.imm 32)] : List Instr) ++ loadScalarWords ++ scalarSubtract)) s _
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rdx 7944 (by decide)) fun a ⟨ap, ka⟩ => ?_
  rw [hp] at ap
  rw [WP.block_append_iff]
  refine WP.mono (add32_ok a .rdx) fun b ⟨bp, kb⟩ => ?_
  rw [ap] at bp
  rw [WP.block_append_iff]
  refine WP.mono (loadScalarWords_ok b (off sig 32) bp (by
    intro d hd; rw [kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun c ⟨cv, kc⟩ => ?_
  refine WP.mono (scalarSubtract_ok c) fun t ⟨tc, _, _, kt⟩ => ?_
  refine ⟨(((Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kb (by decide))).trans
    (Keep.of_keeps kc (by decide))).trans (Keep.of_keeps kt (by decide)),
    kt.2.1.trans (kc.2.1.trans (kb.2.1.trans ka.2.1)), ?_⟩
  rw [tc, cv, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's windows: doublings, digits and table additions

The accumulator in slots 0–3 always represents a point of the group (`Rep`):
four doublings multiply it by 16, and a nonzero digit `v` adds entry `v - 1`
of a table, which represents `[v]X`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

/-- What a window may change: the field workspace and the doublings' (below
byte 1888), and the registers it computes with. -/
structure WinKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 1824 s.mem t.mem

theorem WinKeep.refl (base : Addr) (s : State) : WinKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem WinKeep.trans {base : Addr} {s t u : State} (h : WinKeep base s t) (k : WinKeep base t u) :
    WinKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem WinKeep.scratch {base : Addr} {s t : State} (h : WinKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : WinKeep base s t :=
  ⟨fun r hr _ _ => h.gpr r hr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : WinKeep base s t := by
  refine ⟨fun r hr hb hs => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, by rw [h.2.1]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact hb h
  · exact hs h
  · exact hr h

theorem WinKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : WinKeep base s t :=
  ⟨fun r hr _ hs => h.gpr r hs hr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.of_rbx {base : Addr} {s t : State} (h : RbxKeep base s t) : WinKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

theorem WinKeep.counter {base : Addr} {s t : State} (h : WinKeep base s t) :
    t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64 :=
  h.mem.word (Or.inl (by decide)) (by decide)

/-! ## Four doublings -/

theorem dblOps_eval (e : Env) :
    point (evalOps (dblOps true) e) 0 1 2 3 = dblPoint (point e 0 1 2 3) ∧
    evalOps (dblOps false) e 0 = (dblPoint (point e 0 1 2 3)).X ∧
    evalOps (dblOps false) e 1 = (dblPoint (point e 0 1 2 3)).Y ∧
    evalOps (dblOps false) e 2 = (dblPoint (point e 0 1 2 3)).Z :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dbl_ok {s : State} {base : Addr} (hs : Scratch s base) (t : Bool) {a : EPoint dZ}
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa (.block (fieldCode fld (dblOps t))) s fun u => Keep base s u ∧
      RepP (point (env u.mem base) 0 1 2 3) (a + a) ∧
      (t = true → Rep (point (env u.mem base) 0 1 2 3) (a + a)) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i := by
  refine WP.mono (fieldCodeWide_ok hs _) fun u ⟨ku, vu⟩ => ?_
  have hr := dblPoint_rep ha
  refine ⟨ku, ?_, fun ht => ?_, fun i hi => by
    rw [vu]; exact point_ops_high _ (by cases t <;> decide) _ i hi⟩
  · rw [vu]
    cases t
    · obtain ⟨_, ex, ey, ez⟩ := dblOps_eval (env s.mem base)
      refine ⟨?_, ?_, ?_⟩
      · show toZ (evalOps _ _ 2) ≠ 0
        rw [ez]; exact hr.z
      · show toZ (evalOps _ _ 0) = _ * toZ (evalOps _ _ 2)
        rw [ex, ez]; exact hr.x
      · show toZ (evalOps _ _ 1) = _ * toZ (evalOps _ _ 2)
        rw [ey, ez]; exact hr.y
    · rw [(dblOps_eval _).1]; exact hr.proj
  · subst ht
    rw [vu, (dblOps_eval _).1]; exact hr

theorem double4_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (double4 fld) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double4]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rsi (.imm 3)]) s
      (fun t => t.gpr .rsi = 3 ∧ Keeps [.rsi] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨c1, k1⟩ => ?_)
  have hs₁ : Scratch s₁ base := hs.of_keeps k1 (by decide)
  have k1d : DoubleKeep base s s₁ := ⟨fun r hr _ => k1.1 r (by simpa using hr), k1.2.2.1, k1.2.2.2,
    by rw [k1.2.1]; exact Outside.refl _ _ _ _⟩
  have keepD {x y : State} (k : Keep base x y) : DoubleKeep base x y :=
    ⟨fun r _ hc => k.gpr r hc, k.rd, k.wr, k.mem⟩
  refine WP.seq ?_
  apply WP.loop (fun (n : Nat) (t : State) => 0 < n ∧ n ≤ 3 ∧ Scratch t base ∧
    t.gpr .rsi = BitVec.ofNat 64 n ∧ RepP (point (env t.mem base) 0 1 2 3) ((2 ^ (3 - n) : Nat) • a) ∧
    (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t) (n := 3)
  · intro n t ⟨hn0, hn3, ht, tc, tv, th, tk⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [WP.block_append_iff]
    refine WP.mono (dbl_ok ht false tv) fun u ⟨ku, uv, _, uh⟩ => ?_
    refine WP.mono (doubleDec_ok u k (by omega) ((ku.gpr _ (by decide)).trans tc))
      fun w ⟨wc, wz, kw⟩ => ?_
    have wrep : RepP (point (env w.mem base) 0 1 2 3) ((2 ^ (3 - k) : Nat) • a) := by
      rw [kw.2.1, show 3 - k = (3 - (k + 1)) + 1 by omega, pow_succ, mul_nsmul, two_nsmul]
      exact uv
    have wh : ∀ i : Slot, 16 ≤ i.val → env w.mem base i = env s.mem base i :=
      fun i h => by rw [kw.2.1, uh i h, th i h]
    have wk : DoubleKeep base s w := tk.trans ((keepD ku).trans
      ⟨fun r hr _ => kw.1 r (by simpa using hr), kw.2.2.1, kw.2.2.2,
        by rw [kw.2.1]; exact Outside.refl _ _ _ _⟩)
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, wz, decide_true, Option.map_some, Bool.not_true], ?_⟩
      refine WP.mono (dbl_ok (wk.scratch hs) true wrep) fun v ⟨kv, _, vr, vh⟩ => ?_
      refine ⟨?_, fun i h => (vh i h).trans (wh i h), wk.trans (keepD kv)⟩
      rw [show (16 : Nat) = 2 ^ (3 - 0) * 2 by rfl, mul_nsmul, two_nsmul]
      exact vr rfl
    · exact Or.inr ⟨by simp only [eval, wz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, by omega, by omega, wk.scratch hs, wc, wrep, wh, wk⟩
  · refine ⟨by decide, by decide, hs₁, c1, ?_, fun i _ => by rw [k1.2.1], k1d⟩
    rw [show (2 ^ (3 - 3) : Nat) = 1 from rfl, one_nsmul, k1.2.1]; exact ha.proj

/-! ## Digits -/

theorem addImm_ok (s : State) (r : Reg) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.alu .add r (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr r = off (s.gpr r) n ∧ Keeps [r] s t := by
  have he : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, he,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem digitByte_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitByte ptr add)) s fun t =>
      t.gpr .rbx = (s.mem (off (off P add) i)).setWidth 64 ∧ Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitByte, show ([.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr)),
      .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (Impl.X25519.X86_64.sc 56)),
      .movzx8 .rbx { base := .rsi, index := some .rax }] : List Instr) =
    [.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      ([.mov .rax (.mem (Impl.X25519.X86_64.sc 56))] ++
        [.movzx8 .rbx { base := .rsi, index := some .rax }])) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .rax 56
    (by decide)) fun c ⟨cp, kc⟩ => ?_
  have hm : c.mem = s.mem := kc.2.1.trans (kb.2.1.trans ka.2.1)
  have hrd : c.rd ++ c.wr = s.rd ++ s.wr := by
    rw [kc.2.2.1, kc.2.2.2, kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]
  have crsi : c.gpr .rsi = off P add := by rw [kc.1 _ (by decide), bp, ap, hp]
  have crax : c.gpr .rax = BitVec.ofNat 64 i := by rw [cp, kb.2.1, ka.2.1, hc]
  have hea : c.ea { base := .rsi, index := some .rax } = off (off P add) i := by
    simp only [State.ea, crsi, crax]
    rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.load8, hrd, hr, hm,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, hm, kc.2.2.1.trans (kb.2.2.1.trans ka.2.2.1),
    kc.2.2.2.trans (kb.2.2.2.trans ka.2.2.2)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, kc.1 r (by simp [hr.2.1]), kb.1 r (by simp [hr.1]),
    ka.1 r (by simp [hr.1])]

private theorem high_nibble : ∀ b : BitVec 8,
    b.setWidth 64 >>> 4 = BitVec.ofNat 64 (b.toNat / 16) := by decide

private theorem low_nibble : ∀ b : BitVec 8,
    b.setWidth 64 &&& (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (b.toNat % 16) := by decide

private theorem nibble_zero : ∀ n < 16, (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem digitHigh_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitHigh ptr add)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat / 16) ∧
      t.zf = some (decide ((s.mem (off (off P add) i)).toNat / 16 = 0)) ∧
      Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitHigh, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  have hlt : (s.mem (off (off P add) i)).toNat / 16 < 16 := by
    have := (s.mem (off (off P add) i)).isLt; omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, av,
    show 1 ≤ 4 ∧ 4 ≤ 63 by decide, and_self, ite_true, high_nibble, BitVec.and_self, nibble_zero _ hlt,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.2.2, ite_false]
  exact ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])

theorem digitLow_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitLow ptr add)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat % 16) ∧
      t.zf = some (decide ((s.mem (off (off P add) i)).toNat % 16 = 0)) ∧
      Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitLow, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  have hlt : (s.mem (off (off P add) i)).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, av, low_nibble,
    nibble_zero _ hlt, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2.2, ite_false]
  exact ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])

/-! ## Adding a table entry -/

theorem tableEntryAdd_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base) {o j : Nat}
    (hlo : 768 ≤ o) (hhi : o + 128 * j + 128 ≤ 8192) (hj : j < 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (o + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (tableAddr o ++ pointFromTableQ ++ add)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.rdi o j hj hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  have b_high : ∀ i : Slot, 8 ≤ i.val → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega)), ka.2.1]
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.2.1, hq]
  refine WP.mono (hadd b base q (hs.of_keep (kae.trans kbe)) (by rw [b_high 16 (by decide)]; exact hd) bq)
    fun t ⟨kt, tp, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tp, bp], by rw [th 16 (by decide), b_high 16 (by decide)]⟩

/-- Entries `j < 15` of the table at byte `o` are `f` of representatives of `[j + 1]X`. -/
def TableOf (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (m : Mem) (base : Addr) (o : Nat)
    (X : EPoint dZ) : Prop :=
  ∀ j < 15, ∃ q, tablePoint m base (o + 128 * j) = f q ∧ Rep q ((j + 1) • X)

theorem addDigit_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hlo : 768 ≤ o) (hhi : o + 1920 ≤ 8192) {X a : EPoint dZ} (htab : TableOf f s.mem base o X)
    (v : Nat) (hv : v < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 v) (hz : s.zf = some (decide (v = 0)))
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addDigit o add) s fun t => Rep (point (env t.mem base) 0 1 2 3) (a + v • X) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addDigit]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
    refine WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_
    obtain ⟨q, hq, hr⟩ := htab n (by omega)
    rw [← List.append_assoc]
    refine WP.mono (tableEntryAdd_ok hadd (hs.of_keeps kb (by decide)) hlo (by omega) (by omega) bc q
      (by rw [kb.2.1]; exact hq) (by rw [kb.2.1]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨?_, by rw [td, kb.2.1], (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
    rw [tp, kb.2.1]
    exact pointAdd_rep ha hr
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    refine WP.block_nil ⟨by rw [zero_smul, add_zero]; exact ha, rfl, WinKeep.refl _ _⟩

/-! ## Windows -/

/-- What verification's windows keep: the tables, the inputs and where they are. -/
structure WinCtx (base kp sp : Addr) (A : EPoint dZ) (s : State) : Prop where
  scratch : Scratch s base
  kHeader : s.mem.readW (off base 7952) 64 = kp
  sHeader : s.mem.readW (off base 7944) 64 = sp
  kRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off kp i) 1
  sRead : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sp 32) i) 1
  kFar : ∀ i < 64, 8192 ≤ ofs base (off kp i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)
  aTab : TableOf id s.mem base 5376 A
  bTab : TableOf cache s.mem base 2048 (-baseAff)

/-- Four doublings of the point in slots 0–3, as a window runs them:
`double4` with the field arithmetic, or `Ifma.double4`. -/
class EdDouble (dbl : Prog isa) : Prop where
  ok : ∀ {s : State} {base : Addr} {a : EPoint dZ}, Scratch s base →
    Rep (point (env s.mem base) 0 1 2 3) a → WP isa dbl s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ WinKeep base s t
  ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) dbl (fun _ _ => True)

variable {dbl : Prog isa} [EdDouble dbl]

theorem win_tablePoint {base : Addr} {m m' : Mem} (h : Outside base 56 1832 m m') {d : Nat}
    (hd : 1888 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega)),
    Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega))]

theorem TableOf.of_win {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr} {m m' : Mem}
    {o : Nat} {X : EPoint dZ} (h : TableOf f m base o X) (k : Outside base 56 1832 m m')
    (ho : 1888 ≤ o) (hb : o + 1920 ≤ 8192) : TableOf f m' base o X := by
  intro j hj
  obtain ⟨q, hq, hr⟩ := h j hj
  exact ⟨q, by rw [win_tablePoint k (by omega) (by omega)]; exact hq, hr⟩

theorem Outside.widen {base : Addr} {m m' : Mem} (h : Outside base 64 1824 m m') :
    Outside base 56 1832 m m' := h.mono (by decide) (by decide)

theorem WinKeep.header {base : Addr} {s t : State} (h : WinKeep base s t) {d : Nat} (hd : 1888 ≤ d)
    (hb : d + 8 ≤ 8192) : t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (Or.inr (by omega)) (by omega)

theorem WinCtx.of_keep {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.header (by decide) (by decide)).trans h.kHeader,
    (k.header (by decide) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win (Outside.widen k.mem) (by decide) (by decide), h.bTab.of_win (Outside.widen k.mem) (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem WinCtx.byteK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 64) : t.mem (off kp i) = s.mem (off kp i) :=
  k.mem _ (by have := h.kFar i hi; omega)

theorem WinCtx.byteS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 32) :
    t.mem (off (off sp 32) i) = s.mem (off (off sp 32) i) :=
  k.mem _ (by have := h.sFar i hi; omega)

theorem off_zero (p : Addr) : off p 0 = p := by
  simp only [off, BitVec.add_zero]

/-- A digit's code, with its value `v`, from any state the window has reached. -/
def DigitSpec (base : Addr) (s : State) (digit : List Instr) (v : Nat) : Prop :=
  ∀ t, WinKeep base s t → WP isa (.block digit) t fun u =>
    u.gpr .rbx = BitVec.ofNat 64 v ∧ u.zf = some (decide (v = 0)) ∧ Keeps [.rsi, .rax, .rbx] t u

theorem windowA_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a)
    {digit : List Instr} {v : Nat} (hv : v < 16) (hdig : DigitSpec base s digit v) :
    WP isa (windowA fld dbl digit) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowA]
  refine WP.seq (WP.mono (EdDouble.ok h.scratch ha) fun b ⟨br, bh, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdig b kb) fun c ⟨cv, cz, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a) pointAdd_spec (kbc.scratch h.scratch) (by decide) (by decide)
    (h.aTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) v hv cv cz
    (by rw [kc.2.1, bh 16 (by decide)]; exact hd) (by rw [kc.2.1]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.2.1, bh 16 (by decide)]; exact hd, kbc.trans kt⟩

theorem windowAB_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a)
    {digitA digitB : List Instr} {vA vB : Nat} (hvA : vA < 16) (hvB : vB < 16)
    (hdA : DigitSpec base s digitA vA) (hdB : DigitSpec base s digitB vB) :
    WP isa (windowAB fld dbl digitA digitB) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + vA • A + vB • (-baseAff)) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowAB]
  refine WP.seq (WP.mono (windowA_ok h hd ha hvA hdA) fun b ⟨br, bd, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdB b kb) fun c ⟨cv, cz, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a + vA • A) pointAddCached_spec (kbc.scratch h.scratch)
    (by decide) (by decide) (h.bTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) vB hvB cv cz
    (by rw [kc.2.1]; exact bd) (by rw [kc.2.1]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.2.1]; exact bd, kbc.trans kt⟩

end VG.Proof.Ed25519.X86_64
