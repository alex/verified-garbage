import VerifiedGarbage.Proof.Ed25519.X86_64.CombDigit
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSign
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import Mathlib.Tactic.Module

/-!
# The comb's loop

Untrusted. After step `c`, the accumulator represents `[v]B` for the partial
sum `v = combVal S c`: `G` and the odd digits `d_{2j+1} 256^j` for `j < c`
while `c ≤ 32`, then sixteen times all of those, `G` again, and the even
digits `d_{2j} 256^j` for `j < c - 32`, with the digits `d_i = n_i - 8`. At
`c = 64` that is the scalar (`comb_sum`), since `G = 8 Σ_{j < 32} 256^j`.
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

/-- `Σ_{j < c} 256^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 256 ^ c

theorem combGVal_eq : combGVal = 8 * geom 32 := by decide

/-- The comb's digit `i`: `n_i - 8`, from `-8` to `7`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 8

/-- `Σ_{j < c} d_{2j+1} 256^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} d_{2j} 256^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 256 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The accumulator's multiple of `B` after `c` steps. -/
def combVal (S c : Nat) : ℤ :=
  if c ≤ 32 then combGVal + oddSumZ S c else 16 * (combGVal + oddSumZ S 32) + combGVal + evenSumZ S (c - 32)

theorem comb_sum {S : Nat} (hS : S < 2 ^ (16 * 16)) : combVal S 64 = S := by
  simp only [combVal, show ¬ 64 ≤ 32 by decide, ↓reduceIte, show 64 - 32 = 32 from rfl, oddSumZ_eq,
    evenSumZ_eq, combGVal_eq]
  have h := comb_partial S 32
  rw [Nat.mod_eq_of_lt (by simpa using hS)] at h
  have h' : (16 * oddSum S 32 + evenSum S 32 : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

theorem combIdx_nib (S c : Nat) (hc : c < 64) :
    sdig S (combIdx c) * 256 ^ (c % 32) + (if c = 32 then 16 * combVal S c + combGVal else combVal S c) =
      combVal S (c + 1) := by
  unfold combIdx combVal
  by_cases h : c < 32
  · simp only [h, ↓reduceIte, show c ≠ 32 by omega, show c ≤ 32 by omega, show c + 1 ≤ 32 by omega,
      oddSumZ, Nat.mod_eq_of_lt h]
    ring
  · have hs : c + 1 - 32 = (c - 32) + 1 := by omega
    by_cases h32 : c = 32
    · subst h32
      simp only [show ¬ 32 < 32 by decide, ↓reduceIte, le_refl, show ¬ 33 ≤ 32 by decide,
        show 33 - 32 = 0 + 1 from rfl, evenSumZ]
      ring
    · simp only [h, h32, ↓reduceIte, show ¬ c ≤ 32 by omega, show ¬ c + 1 ≤ 32 by omega, hs, evenSumZ,
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

theorem combAddG_ok {s : State} {base : Addr} (hs : Scratch s base) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (combAddG fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) combG ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [combAddG, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs _) fun a ⟨ka, va⟩ => ?_
  have hsa := hs.of_keep ka
  have ha16 : ∀ i : Slot, 16 ≤ i.val → env a.mem base i = env s.mem base i := fun i hi => by
    rw [va]; exact point_ops_high _ (by decide) _ i hi
  have hp : point (env a.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by rw [va]; rfl
  refine WP.mono (pointAddCached_spec (fld := fld) a base combG hsa (by rw [ha16 16 (by decide)]; exact hd)
    (by rw [va, ← combGCached_eq]; rfl)) fun t ⟨kt, tp, th⟩ =>
    ⟨ka.trans kt, by rw [tp, hp], fun i hi => (th i hi).trans (ha16 i hi)⟩

theorem zsmul_16 (v : ℤ) (g : Nat) (P : EPoint dZ) :
    (16 : Nat) • (v • P) + g • P = (16 * v + g) • P := by
  rw [add_smul, mul_smul, ← natCast_zsmul, ← natCast_zsmul]; rfl

theorem combStep_ok {s₀ s : State} {base : Addr} {S c : Nat} (h : CombInv s₀ base S c s)
    (hc : c < 64) :
    WP isa (combStep fld) s fun t => t.zf = some (decide (c + 1 = 64)) ∧
      CombInv s₀ base S (c + 1) t := by
  rw [combStep]
  refine WP.seq (WP.mono (rbxCmp_ok s c 32 hc (by decide) h.counter) fun a ⟨az, ag, am, ar, aw⟩ => ?_)
  have hsa : Scratch a base := ⟨by rw [ag]; exact h.scratch.rdi, aw ▸ h.scratch.wr, h.scratch.nowrap⟩
  have kas : PowersKeep base 56 7368 s a := ⟨fun r _ _ _ => by rw [ag], ar, aw, by rw [am]; exact TableFrame.refl _ _ _ _⟩
  -- The doublings and `[G]B`, before the even digits.
  have hite : WP isa (.ite .e (.seq (double4 fld) (.block (combAddG fld))) (.block [])) a fun b =>
      Scratch b base ∧ b.gpr .rbx = BitVec.ofNat 64 c ∧ env b.mem base 16 = Spec.Ed25519.d ∧
      (∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) ∧
      Rep (point (env b.mem base) 0 1 2 3)
        ((if c = 32 then 16 * combVal S c + combGVal else combVal S c) • baseAff) ∧
      PowersKeep base 56 7368 a b := by
    refine WP.ite (decide (c = 32)) (by simp only [eval, az]) (fun hy => ?_) (fun hn => ?_)
    · have h32 : c = 32 := of_decide_eq_true hy
      refine WP.seq (WP.mono (double4_ok (fld := fld) (a := combVal S c • baseAff) hsa (by rw [am]; exact h.value))
        fun b ⟨br, bh, bk⟩ => ?_)
      have hsb := bk.scratch hsa
      have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [bh 16 (by decide), am]; exact h.d
      refine WP.mono (combAddG_ok (fld := fld) hsb bd) fun e ⟨ke, ep, eh⟩ => ?_
      refine ⟨hsb.of_keep ke, (ke.gpr _ (by decide)).trans ((bk.gpr _ (by decide) (by decide)).trans
          (by rw [ag]; exact h.counter)),
        by rw [eh 16 (by decide)]; exact bd,
        fun q hq => by
          rw [ke.mem _ (by rw [bits_far hq]; omega), bk.mem _ (by rw [bits_far hq]; omega), am]
          exact h.bits q hq, ?_,
        (⟨fun r _ hs hc' => bk.gpr r hs hc', bk.rd, bk.wr, TableFrame.workspace bk.mem⟩ :
          PowersKeep base 56 7368 a b).trans (PowersKeep.of_keep ke)⟩
      simp only [h32, ↓reduceIte]
      rw [ep, ← zsmul_16]
      subst h32
      exact pointAdd_rep br combG_ok
    · have h32 : c ≠ 32 := of_decide_eq_false hn
      refine WP.block_nil ⟨hsa, by rw [ag]; exact h.counter, by rw [am]; exact h.d,
        fun q hq => by rw [am]; exact h.bits q hq, by simp only [h32, ↓reduceIte]; rw [am]; exact h.value,
        PowersKeep.refl _ _ _ _⟩
  refine WP.seq (WP.mono hite fun b ⟨hsb, bc, bd, bbits, bv, kb⟩ => ?_)
  -- The digit's bit index.
  refine WP.seq (WP.mono (combIndex_ok b hc bc) fun e ⟨ec, ke⟩ => ?_)
  have hse : Scratch e base := hsb.of_keeps ke (by decide)
  -- The digit, its sign and magnitude, its masks and the table.
  have hn : nib S (combIdx c) < 16 := Nat.mod_lt _ (by decide)
  have hmag : mag (nib S (combIdx c)) < 9 := by unfold mag; split <;> omega
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok (S := S) hse (combIdx_lt hc) ec (by rw [ke.2.1]; exact bbits))
    fun f ⟨fax, kf⟩ => ?_
  have hsf : Scratch f base := hse.of_keeps kf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok (n := nib S (combIdx c)) hsf hn fax) fun f' ⟨f'ax, f'm, f'g, f'r, f'w, f'mem⟩ => ?_
  have hsf' : Scratch f' base := ⟨(f'g _ (by decide) (by decide)).trans hsf.rdi, f'w ▸ hsf.wr, hsf.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (combMaskAll_ok (d := mag (nib S (combIdx c))) hsf' (by omega) f'ax)
    fun g ⟨gm, gg, gr, gw, gmem⟩ => ?_
  have hsg : Scratch g base := ⟨(gg _ (by decide)).trans hsf'.rdi, gw ▸ hsf'.wr, hsf'.nowrap⟩
  have gc : g.gpr .rbx = BitVec.ofNat 64 c := by
    rw [gg _ (by decide), f'g _ (by decide) (by decide), kf.1 _ (by decide), ke.1 _ (by decide)]; exact bc
  have gsm : g.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) :=
    (gmem.word (d := combSignMask) (Or.inr (by simp only [combMasks, combSignMask]; omega))
      (by simp only [combSignMask]; omega)).trans f'm
  refine WP.mono (rdxMod_ok g c hc gc) fun i ⟨irdx, ki⟩ => ?_
  have hsi : Scratch i base := hsg.of_keeps ki (by decide)
  -- The entry.
  refine WP.seq (WP.mono (combSelectAll_ok (d := mag (nib S (combIdx c))) hsi hmag
    (by rw [ki.2.1]; exact gm) (Nat.mod_lt _ (by decide)) irdx) fun u ⟨uq, ku, _, ue⟩ => ?_)
  have hsu : Scratch u base := hsi.of_keep ku
  have usm : u.mem.readW (off base combSignMask) 64 = signMask (nib S (combIdx c)) :=
    (ku.mem.word (d := combSignMask) (Or.inr (by simp only [combSignMask]; omega))
      (by simp only [combSignMask]; omega)).trans (by rw [ki.2.1]; exact gsm)
  -- Negated for a negative digit.
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok (fld := fld) hsu usm) fun u' ⟨u'q, ku', ue'⟩ => ?_
  have hsu' : Scratch u' base := hsu.of_keep ku'
  have eu : ∀ x : Slot, (x.val < 4 ∨ 16 ≤ x.val) → env u'.mem base x = env b.mem base x := fun x hx => by
    rw [ue' x (by omega), ue x (by omega), ki.2.1, table_env gmem (by simp only [combMasks]; omega),
      table_env f'mem (by simp only [combSignMask]; omega), kf.2.1, ke.2.1]
  have ud : env u'.mem base 16 = Spec.Ed25519.d := (eu 16 (by decide)).trans bd
  have up : point (env u'.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by
    simp only [point, eu 0 (by decide), eu 1 (by decide), eu 2 (by decide), eu 3 (by decide)]
  obtain ⟨q₀, hq₀, hrq₀⟩ := combCached_ok (c % 32) (mag (nib S (combIdx c))) (Nat.mod_lt _ (by decide)) hmag
  let q := if nib S (combIdx c) < 8 then negPoint q₀ else q₀
  have hq : point (env u'.mem base) 4 5 6 7 = cache q := by
    rw [u'q, uq, hq₀]
    by_cases hlt : nib S (combIdx c) < 8
    · simp only [hlt, ↓reduceIte, q, negCached_cache]
    · simp only [hlt, ↓reduceIte, q]
  have hrq : Rep q ((sdig S (combIdx c) * 256 ^ (c % 32)) • baseAff) := by
    by_cases hlt : nib S (combIdx c) < 8
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 256 ^ (c % 32) = -(((mag (nib S (combIdx c)) * 256 ^ (c % 32) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : nib S (combIdx c) ≤ 8)]; ring
      rw [e, neg_smul, natCast_zsmul]
      exact hrq₀.neg
    · simp only [hlt, ↓reduceIte, q]
      have e : sdig S (combIdx c) * 256 ^ (c % 32) = (((mag (nib S (combIdx c)) * 256 ^ (c % 32) : Nat) : ℤ)) := by
        simp only [sdig, mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ nib S (combIdx c))]; ring
      rw [e, natCast_zsmul]
      exact hrq₀
  -- The addition and the counter.
  rw [WP.block_append_iff]
  refine WP.mono (pointAddCached_spec (fld := fld) u' base q hsu' ud hq) fun v ⟨kv, vp, vh⟩ => ?_
  have vc : v.gpr .rbx = BitVec.ofNat 64 c := by
    rw [kv.gpr _ (by decide), ku'.gpr _ (by decide), ku.gpr _ (by decide), ki.1 _ (by decide), gc]
  refine WP.mono (rbxNext64_ok v c hc vc) fun t ⟨tc, tz, kt⟩ => ⟨tz, ?_⟩
  have kbu : PowersKeep base 56 7368 b u' :=
    (((((PowersKeep.of_keeps ke (by decide)).trans (PowersKeep.of_keeps kf (by decide))).trans
      ⟨fun r _ _ hcl => f'g r (by rintro rfl; exact hcl (by decide)) (by rintro rfl; exact hcl (by decide)),
        f'r, f'w, TableFrame.table (f'mem.mono (by simp only [combSignMask]; omega)
          (by simp only [combSignMask]; omega))⟩).trans
      ⟨fun r _ _ hcl => gg r (by rintro rfl; exact hcl (by decide)), gr, gw,
        TableFrame.table (gmem.mono (by simp only [combMasks]; omega) (by simp only [combMasks]; omega))⟩).trans
      (PowersKeep.of_keeps ki (by decide))).trans ((PowersKeep.of_keep ku).trans (PowersKeep.of_keep ku'))
  refine ⟨by omega, hsu'.of_keep kv |>.of_keeps kt (by decide), tc, ?_, fun x hx => ?_, ?_,
    ((((h.keep.trans kas).trans kb).trans kbu).trans (PowersKeep.of_keep kv)).trans
      (PowersKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1, vh 16 (by decide), ud]
  · rw [kt.2.1, kv.mem _ (by rw [bits_far hx]; omega), ku'.mem _ (by rw [bits_far hx]; omega),
      ku.mem _ (by rw [bits_far hx]; omega), ki.2.1,
      gmem _ (by rw [bits_far hx]; simp only [combMasks]; omega),
      f'mem _ (by rw [bits_far hx]; simp only [combSignMask]; omega), kf.2.1, ke.2.1]
    exact bbits x hx
  · rw [kt.2.1, vp, up, ← combIdx_nib S c hc, add_smul, add_comm]
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
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs (constPointOps combG))
    fun a ⟨ka, va⟩ => ?_
  refine WP.mono (rbxSet_ok a 0 (by decide)) fun b ⟨bc, kb⟩ => ?_
  have init : CombInv s base S 0 b := by
    refine ⟨by decide, (hs.of_keep ka).of_keeps kb (by decide), bc, ?_, fun q hq => ?_, ?_,
      (PowersKeep.of_keep ka).trans (PowersKeep.of_keeps kb (by decide))⟩
    · rw [kb.2.1, va, point_ops_high _ (by decide) _ 16 (by decide), hd]
    · rw [kb.2.1, ka.mem _ (by rw [bits_far hq]; omega)]; exact hb q hq
    · rw [kb.2.1, va, constPoint_eval, show combVal S 0 = (combGVal : ℤ) by simp [combVal, oddSumZ],
        natCast_zsmul]
      exact combG_ok
  apply WP.loop (fun n t => CombInv s base S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok (fld := fld) ht (by omega)) fun u ⟨uz, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      refine Or.inl ⟨by simp only [eval, uz, show 64 - (0 + 1) + 1 = 64 from rfl, decide_true,
        Option.map_some, Bool.not_true], ?_, hu.keep⟩
      have hv := hu.value
      rw [show 64 - (0 + 1) + 1 = 64 from rfl, comb_sum hS, natCast_zsmul] at hv
      exact hv
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (64 - (k + 1) + 1 = 64) by omega, decide_false,
        Option.map_some, Bool.not_false], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨init, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64
