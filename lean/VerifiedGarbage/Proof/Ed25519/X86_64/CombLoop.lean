import VerifiedGarbage.Proof.Ed25519.X86_64.CombDigit
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import Mathlib.Tactic.Module

/-!
# The comb's loop

Untrusted. After step `c`, the accumulator represents `[v]B` for the partial
sum `v = combVal S c`: the odd digits `n_{2j+1} 256^j` for `j < c` while
`c ≤ 32`, then sixteen times all of those plus the even digits `n_{2j}
256^j` for `j < c - 32`. At `c = 64` that is the scalar (`comb_sum`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 256 ^ c

/-- The accumulator's multiple of `B` after `c` steps. -/
def combVal (S c : Nat) : Nat := if c ≤ 32 then oddSum S c else 16 * oddSum S 32 + evenSum S (c - 32)

theorem comb_partial (S : Nat) : ∀ n, 16 * oddSum S n + evenSum S n = S % 256 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have h16 : 256 ^ n = 16 ^ (2 * n) := by rw [pow_mul]; norm_num
    have hd : S / 16 ^ (2 * n + 1) = S / 16 ^ (2 * n) / 16 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    have hm : S % 256 ^ (n + 1) = S % 256 ^ n + 256 ^ n * (S / 256 ^ n % 256) := by
      rw [pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, h16]
    generalize S / 16 ^ (2 * n) = x
    generalize 16 ^ (2 * n) = y
    have : x % 256 = x % 16 + 16 * (x / 16 % 16) := by omega
    rw [this]; ring

theorem comb_sum {S : Nat} (hS : S < 2 ^ (16 * 16)) : combVal S 64 = S := by
  simp only [combVal, show ¬ 64 ≤ 32 by decide, ↓reduceIte, show 64 - 32 = 32 from rfl,
    comb_partial S 32]
  exact Nat.mod_eq_of_lt (by simpa using hS)

theorem combIdx_nib (S c : Nat) (hc : c < 64) :
    nib S (combIdx c) * 256 ^ (c % 32) + (if c = 32 then 16 * combVal S c else combVal S c) =
      combVal S (c + 1) := by
  unfold combIdx combVal
  by_cases h : c < 32
  · simp only [h, ↓reduceIte, show c ≠ 32 by omega, show c ≤ 32 by omega, show c + 1 ≤ 32 by omega,
      oddSum, Nat.mod_eq_of_lt h]
    ring
  · have hs : c + 1 - 32 = (c - 32) + 1 := by omega
    by_cases h32 : c = 32
    · subst h32
      simp only [show ¬ 32 < 32 by decide, ↓reduceIte, le_refl, show ¬ 33 ≤ 32 by decide,
        show 33 - 32 = 0 + 1 from rfl, evenSum]
      ring
    · simp only [h, h32, ↓reduceIte, show ¬ c ≤ 32 by omega, show ¬ c + 1 ≤ 32 by omega, hs, evenSum,
        show c % 32 = c - 32 by omega]
      ring

/-! ## Counters -/

theorem rbxCmp_ok (s : State) (c k : Nat) (hc : c < 64) (hk : k < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (c = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 64, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  have hz : (BitVec.ofNat 64 c - BitVec.ofNat 64 k == 0) = decide (c = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hc, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hb, he, hz, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

private theorem mod32_fact : ∀ c < 64,
    BitVec.ofNat 64 c &&& (31 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (c % 32) := by decide

theorem rdxMod_ok (s : State) (c : Nat) (hc : c < 64) (hb : s.gpr .rbx = BitVec.ofNat 64 c) :
    WP isa (.block [.mov .rdx (.reg .rbx), .alu .and .rdx (.imm 31)]) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 (c % 32) ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hb, mod32_fact c hc, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem rbxNext64_ok (s : State) (n : Nat) (hn : n < 64) (hc : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 64)]) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (n + 1) ∧ t.zf = some (decide (n + 1 = 64)) ∧
      Keeps [.rbx] s t := by
  have ha : BitVec.ofNat 64 n + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (n + 1) - (64 : BitVec 32).signExtend 64 == 0) =
      decide (n + 1 = 64) := by
    rw [show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl]
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

/-! ## A step -/

/-- The loop's invariant, after `c` steps. -/
structure CombInv (s₀ : State) (base : Addr) (S c : Nat) (s : State) : Prop where
  bound : c ≤ 64
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 c
  d : env s.mem base 16 = Spec.Ed25519.d
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  value : Rep (point (env s.mem base) 0 1 2 3) (combVal S c • baseAff)
  keep : PowersKeep base 56 7368 s₀ s

theorem bits_far {base : Addr} {q : Nat} (hq : q < 256) :
    ofs base (off base (768 + q)) = 768 + q := Proof.X25519.X86_64.ofs_off' base (by omega)

theorem combStep_ok {s₀ s : State} {base : Addr} {S c : Nat} (h : CombInv s₀ base S c s)
    (hc : c < 64) :
    WP isa (combStep fld) s fun t => t.zf = some (decide (c + 1 = 64)) ∧
      CombInv s₀ base S (c + 1) t := by
  rw [combStep]
  refine WP.seq (WP.mono (rbxCmp_ok s c 32 hc (by decide) h.counter) fun a ⟨az, ag, am, ar, aw⟩ => ?_)
  have hsa : Scratch a base := ⟨by rw [ag]; exact h.scratch.rdi, aw ▸ h.scratch.wr, h.scratch.nowrap⟩
  have kas : PowersKeep base 56 7368 s a := ⟨fun r _ _ _ => by rw [ag], ar, aw, by rw [am]; exact TableFrame.refl _ _ _ _⟩
  -- The doublings, before the even digits.
  have hite : WP isa (.ite .e (double4 fld) (.block [])) a fun b =>
      Scratch b base ∧ b.gpr .rbx = BitVec.ofNat 64 c ∧ env b.mem base 16 = Spec.Ed25519.d ∧
      (∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) ∧
      Rep (point (env b.mem base) 0 1 2 3)
        ((if c = 32 then 16 * combVal S c else combVal S c) • baseAff) ∧
      PowersKeep base 56 7368 a b := by
    refine WP.ite (decide (c = 32)) (by simp only [eval, az]) (fun hy => ?_) (fun hn => ?_)
    · have h32 : c = 32 := of_decide_eq_true hy
      refine WP.mono (double4_ok (fld := fld) (a := combVal S c • baseAff) hsa (by rw [am]; exact h.value))
        fun b ⟨br, bh, bk⟩ => ?_
      refine ⟨bk.scratch hsa, (bk.gpr _ (by decide) (by decide)).trans (by rw [ag]; exact h.counter),
        by rw [bh 16 (by decide), am]; exact h.d,
        fun q hq => by rw [bk.mem _ (by rw [bits_far hq]; omega), am]; exact h.bits q hq, ?_,
        ⟨fun r _ hs hc' => bk.gpr r hs hc', bk.rd, bk.wr, TableFrame.workspace bk.mem⟩⟩
      simp only [h32, ↓reduceIte]; rw [← smul_smul]; subst h32; exact br
    · have h32 : c ≠ 32 := of_decide_eq_false hn
      refine WP.block_nil ⟨hsa, by rw [ag]; exact h.counter, by rw [am]; exact h.d,
        fun q hq => by rw [am]; exact h.bits q hq, by simp only [h32, ↓reduceIte]; rw [am]; exact h.value,
        PowersKeep.refl _ _ _ _⟩
  refine WP.seq (WP.mono hite fun b ⟨hsb, bc, bd, bbits, bv, kb⟩ => ?_)
  -- The digit's bit index.
  refine WP.seq (WP.mono (combIndex_ok b hc bc) fun e ⟨ec, ke⟩ => ?_)
  have hse : Scratch e base := hsb.of_keeps ke (by decide)
  -- The digit, its masks and the table.
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (combDigit_ok (S := S) hse (combIdx_lt hc) ec (by rw [ke.2.1]; exact bbits))
    fun f ⟨fax, kf⟩ => ?_
  have hsf : Scratch f base := hse.of_keeps kf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (combMaskAll_ok (d := nib S (combIdx c)) hsf (Nat.mod_lt _ (by decide)) fax) fun g ⟨gm, gg, gr, gw, gmem⟩ => ?_
  have hsg : Scratch g base := ⟨(gg _ (by decide)).trans hsf.rdi, gw ▸ hsf.wr, hsf.nowrap⟩
  have gc : g.gpr .rbx = BitVec.ofNat 64 c := by
    rw [gg _ (by decide), kf.1 _ (by decide), ke.1 _ (by decide)]; exact bc
  refine WP.mono (rdxMod_ok g c hc gc) fun i ⟨irdx, ki⟩ => ?_
  have hsi : Scratch i base := hsg.of_keeps ki (by decide)
  -- The entry.
  refine WP.seq (WP.mono (combSelectAll_ok (d := nib S (combIdx c)) hsi (Nat.mod_lt _ (by decide))
    (by rw [ki.2.1]; exact gm)
    (Nat.mod_lt _ (by decide)) irdx) fun u ⟨uq, ku, _, ue⟩ => ?_)
  have hsu : Scratch u base := hsi.of_keep ku
  have eu : ∀ x : Slot, (x.val < 4 ∨ 8 ≤ x.val) → env u.mem base x = env b.mem base x := fun x hx => by
    rw [ue x hx, ki.2.1, table_env gmem (by simp only [combMasks]; omega), kf.2.1, ke.2.1]
  have ud : env u.mem base 16 = Spec.Ed25519.d := (eu 16 (by decide)).trans bd
  have up : point (env u.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by
    simp only [point, eu 0 (by decide), eu 1 (by decide), eu 2 (by decide), eu 3 (by decide)]
  obtain ⟨q, hq, hrq⟩ := combCached_ok (c % 32) (nib S (combIdx c)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))
  -- The addition and the counter.
  rw [WP.block_append_iff]
  refine WP.mono (pointAddCached_spec (fld := fld) u base q hsu ud (by rw [uq, hq])) fun v ⟨kv, vp, vh⟩ => ?_
  have vc : v.gpr .rbx = BitVec.ofNat 64 c := by
    rw [kv.gpr _ (by decide), ku.gpr _ (by decide), ki.1 _ (by decide), gc]
  refine WP.mono (rbxNext64_ok v c hc vc) fun t ⟨tc, tz, kt⟩ => ⟨tz, ?_⟩
  have kbu : PowersKeep base 56 7368 b u :=
    ((((PowersKeep.of_keeps ke (by decide)).trans (PowersKeep.of_keeps kf (by decide))).trans
      ⟨fun r _ _ hcl => gg r (by rintro rfl; exact hcl (by decide)), gr, gw,
        TableFrame.table (gmem.mono (by simp only [combMasks]; omega) (by simp only [combMasks]; omega))⟩).trans
      (PowersKeep.of_keeps ki (by decide))).trans (PowersKeep.of_keep ku)
  refine ⟨by omega, hsu.of_keep kv |>.of_keeps kt (by decide), tc, ?_, fun x hx => ?_, ?_,
    ((((h.keep.trans kas).trans kb).trans kbu).trans (PowersKeep.of_keep kv)).trans
      (PowersKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1, vh 16 (by decide), ud]
  · rw [kt.2.1, kv.mem _ (by rw [bits_far hx]; omega), ku.mem _ (by rw [bits_far hx]; omega), ki.2.1,
      gmem _ (by rw [bits_far hx]; simp only [combMasks]; omega), kf.2.1, ke.2.1]
    exact bbits x hx
  · rw [kt.2.1, vp, up, ← combIdx_nib S c hc, add_nsmul, add_comm]
    exact pointAdd_rep bv hrq

/-! ## The loop -/

theorem combMultiply_ok {s : State} {base : Addr} (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (combMultiply fld) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
  rw [combMultiply]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs (constPointOps Spec.Ed25519.identity))
    fun a ⟨ka, va⟩ => ?_
  refine WP.mono (rbxSet_ok a 0 (by decide)) fun b ⟨bc, kb⟩ => ?_
  have init : CombInv s base S 0 b := by
    refine ⟨by decide, (hs.of_keep ka).of_keeps kb (by decide), bc, ?_, fun q hq => ?_, ?_,
      (PowersKeep.of_keep ka).trans (PowersKeep.of_keeps kb (by decide))⟩
    · rw [kb.2.1, va, point_ops_high _ (by decide) _ 16 (by decide), hd]
    · rw [kb.2.1, ka.mem _ (by rw [bits_far hq]; omega)]; exact hb q hq
    · rw [kb.2.1, va, constPoint_eval, show combVal S 0 = 0 from rfl, zero_smul]
      exact identity_rep
  apply WP.loop (fun n t => CombInv s base S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok (fld := fld) ht (by omega)) fun u ⟨uz, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      refine Or.inl ⟨by simp only [eval, uz, show 64 - (0 + 1) + 1 = 64 from rfl, decide_true,
        Option.map_some, Bool.not_true], ?_, hu.keep⟩
      have hv := hu.value
      rw [show 64 - (0 + 1) + 1 = 64 from rfl, comb_sum hS] at hv
      exact hv
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (64 - (k + 1) + 1 = 64) by omega, decide_false,
        Option.map_some, Bool.not_false], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨init, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64
