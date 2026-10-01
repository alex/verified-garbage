import VerifiedGarbage.Impl.Ed25519.X86_64.PointMulVar
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseAccumulate
import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr

/-!
# Variable-time bit loops: correctness

Untrusted. The loop over a batch's sixteen bits for any addition `add` that
adds `q` to the accumulator when slots 4–7 hold `f q` (`AddSpec`): exact
powers with `pointAdd` (`f = id`), cached ones with `pointAddCached`
(`f = cache`). A clear bit leaves the accumulator alone, which is the
specification's step too (`after_step`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F fe_st4 st4_outside Outside Keeps clob)
open VG.Impl.X25519.X86_64 (stores)

/-- `add` adds `q` to the accumulator in slots 0–3 when slots 4–7 hold `f q`. -/
def AddSpec (add : List Instr) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scratch s base →
    env s.mem base 16 = Spec.Ed25519.d → point (env s.mem base) 4 5 6 7 = f q →
    WP isa (.block add) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i

theorem pointAdd_spec : AddSpec pointAdd id := fun _ _ _ hs hd hq =>
  WP.mono (pointAddWide_ok hs hd) fun _ ⟨k, v, h⟩ => ⟨k, v.trans (by rw [hq]; rfl), h⟩

theorem pointAddCached_spec : AddSpec pointAddCached cache := fun _ _ q hs _ hq =>
  pointAddCachedWide_ok hs q hq

theorem fromTableQuarterQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok hs hp (32 * j) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores8192_ok ht.rdi ht.wr (by omega : 192 + 32 * j + 32 ≤ 8192)
    .r8 .r9 .r10 .r11) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · change F u.mem base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, F, hm, fe_st4 _ _ (by omega), hv]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefixQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .r8 .r9 .r10 .r11)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromTableQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega⟩ = env t.mem base ⟨4 + j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTableQ_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base o ∧ TableKeep base 192 128 s t := by
  refine WP.mono (fromTablePrefixQ_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 4 = _ at h0
  change env t.mem base 5 = _ at h1
  change env t.mem base 6 = _ at h2
  change env t.mem base 7 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

theorem Keep.of_tableQ {base : Addr} {s t : State}
    (h : TableKeep base 192 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

theorem addEntry_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (5376 + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (addEntry add)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [addEntry, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.rdi 5376 j (by omega) hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change F b.mem base (offset i) = F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  have b_high : ∀ i : Slot, 8 ≤ i.val → env b.mem base i = env s.mem base i := by
    intro i hi
    change F b.mem base (offset i) = F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega)), ka.2.1]
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.2.1, hq]
  refine WP.mono (hadd b base q (hs.of_keep (kae.trans kbe)) (by rw [b_high 16 (by decide)]; exact hd) bq)
    fun t ⟨kt, tp, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tp, bp], by rw [th 16 (by decide), b_high 16 (by decide)]⟩

theorem scalarBitTest_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j start bit : Nat) (hi : start + j < 512) (hbit : bit < 2)
    (hj : s.gpr .rbx = BitVec.ofNat 64 j) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit) :
    WP isa (.block scalarBitTest) s fun t =>
      t.zf = some (decide (bit = 0)) ∧ Keeps [.rax, .rcx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (start + j))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + (BitVec.ofNat 64 j + BitVec.ofNat 64 start) * 1#64 + BitVec.ofInt 64 768 =
      off base (768 + (start + j)) := by
    rw [BitVec.mul_one, ← BitVec.ofNat_add, show BitVec.ofInt 64 768 = BitVec.ofNat 64 768 from rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hz : ((BitVec.ofNat 8 bit).setWidth 64 == 0) = decide (bit = 0) := by
    have h : bit = 0 ∨ bit = 1 := by omega
    rcases h with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [scalarBitTest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, State.ea, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, hj, hstart, hs.rdi, he, hr, hb, BitVec.and_self, hz,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem accumulateVarBody_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem base (5376 + 128 * n) = f (powerPoint p (start + n))) :
    WP isa (accumulateVarBody add) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s t := by
  rw [accumulateVarBody]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  refine WP.mono (scalarBitTest_ok ha n start ((scalar / 2 ^ (start + n)) % 2) hi (by omega) ac
    ((ka.1 _ (by decide)).trans hstart) (by rw [ka.2.1]; exact hb)) fun b ⟨bz, kb⟩ => ?_
  have kab : Keeps [.rbx, .rax, .rcx] s b := (ka.mono (by decide)).trans (kb.mono (by decide))
  have hbs := hs.of_keeps kab (by decide)
  have bc : b.gpr .rbx = BitVec.ofNat 64 n := (kb.1 _ (by decide)).trans ac
  have hmid : WP isa (.ite .ne (.block (addEntry add)) (.block [])) b fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s t := by
    refine WP.ite (!decide ((scalar / 2 ^ (start + n)) % 2 = 0))
      (by simp only [eval, bz, Option.map_some]) (fun h => ?_) (fun h => ?_)
    · have h1 : (scalar / 2 ^ (start + n)) % 2 ≠ 0 := by simpa using h
      refine WP.mono (addEntry_ok hadd hbs n (by omega) bc (powerPoint p (start + n)) (by rw [kab.2.1]; exact ht)
        (by rw [kab.2.1]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
      refine ⟨(kt.gpr _ (by decide)).trans bc, ?_, by rw [td, kab.2.1]; exact hd,
        (RbxKeep.of_keeps kab (by decide)).trans (RbxKeep.of_keep kt)⟩
      rw [tp, kab.2.1, hp, after_step scalar p (start + n)]
      simp only [h1, ↓reduceIte]
    · have h0 : (scalar / 2 ^ (start + n)) % 2 = 0 := by simpa using h
      refine WP.block_nil ⟨bc, ?_, by rw [kab.2.1]; exact hd, RbxKeep.of_keeps kab (by decide)⟩
      rw [kab.2.1, hp, after_step scalar p (start + n)]
      simp only [h0, ↓reduceIte]
  refine WP.seq (WP.mono hmid fun t ⟨tc, tp, td, tk⟩ => ?_)
  refine WP.mono (accumulateTest_ok t n hn tc) fun u ⟨uz, ku⟩ => ?_
  exact ⟨(ku.1 _ (by simp)).trans tc, uz, by rw [ku.2.1]; exact tp, by rw [ku.2.1]; exact td,
    tk.trans (RbxKeep.of_keeps ku (by decide))⟩

structure AccumulateVarInv (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (s₀ : State) (base : Addr)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  startReg : s.gpr .rsi = BitVec.ofNat 64 start
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = f (powerPoint p (start + i))
  keep : RbxKeep base s₀ s

theorem accumulateVarStep_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s₀ s : State} {base : Addr} {start scalar : Nat} {p : Spec.Ed25519.Point}
    {k : Nat} (hi : start + 16 ≤ 512) (h : AccumulateVarInv f s₀ base start scalar p (k + 1) s) :
    WP isa (accumulateVarBody add) s fun t => t.zf = some (decide (k = 0)) ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + k) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s₀ t ∧
      (k ≠ 0 → AccumulateVarInv f s₀ base start scalar p k t) := by
  have hk : k < 16 := by have := h.bound; omega
  refine WP.mono (accumulateVarBody_ok hadd h.scratch k start scalar p hk (by omega) h.counter
    h.startReg (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
    fun t ⟨tc, tz, tv, td, tk⟩ => ?_
  refine ⟨tz, tv, td, h.keep.trans tk, fun hk0 => ⟨by omega, by omega, tk.scratch h.scratch, tc,
    (tk.gpr _ (by decide) (by decide)).trans h.startReg, td, tv, ?_, ?_, h.keep.trans tk⟩⟩
  · intro i hi'
    rw [tk.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits i hi']
  · intro i hi'
    rw [workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']

theorem accumulateVarLoop_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s₀ : State} {base : Addr} (start scalar : Nat) (p : Spec.Ed25519.Point)
    (hi : start + 16 ≤ 512) (h₀ : AccumulateVarInv f s₀ base start scalar p 16 s₀) :
    WP isa (.loop (accumulateVarBody add) .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s₀ t := by
  apply WP.loop (AccumulateVarInv f s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    refine WP.mono (accumulateVarStep_ok hadd hi h) fun t ⟨tz, tv, td, tk, tn⟩ => ?_
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, td, tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, tn hk0⟩
  · exact h₀

theorem accumulateVar16_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = f (powerPoint p (start + i))) :
    WP isa (accumulateVar16 add) s fun t => point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ RbxKeep base s t := by
  rw [accumulateVar16]
  refine WP.seq (WP.mono (accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  refine WP.mono (accumulateVarLoop_ok hadd start scalar p hi
    ⟨by decide, by decide, hs.of_keeps ka (by decide), ac, (ka.1 _ (by decide)).trans hstart,
      by rw [ka.2.1]; exact hd, by rw [ka.2.1]; exact hp, by rw [ka.2.1]; exact hb,
      by rw [ka.2.1]; exact ht, RbxKeep.refl _ _⟩) fun t ⟨tv, td, tk⟩ => ?_
  exact ⟨tv, td, (RbxKeep.of_keeps ka (by decide)).trans tk⟩

end VG.Proof.Ed25519.X86_64
