import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Limbwise

/-!
# Differences and sums

Untrusted: everything here is checked by Lean. `sub o a b` writes
`a + 2p - b` limb by limb, and `addSub` also `a + b`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

def K2 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 2)
def K4 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 4)

def twoPW (i : Nat) : BitVec 64 := if i = 4 then K4 else K2

theorem twoPRegs_ok (s : State) :
    WP isa (.block twoPRegs) s fun t =>
      t.gpr .x0 = K2 ∧ t.gpr .x2 = K4 ∧ t.mem = s.mem ∧ Keeps [.x0, .x2] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [twoPRegs, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide,
      show 16 * 2 < 64 from by decide, show 16 * 3 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem twoPReg_val {t : State} (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) (i : Nat) :
    t.gpr (twoPReg i) = twoPW i := by
  simp only [twoPReg, twoPW]; split <;> assumption

/-- Load two words, from the working space. -/
theorem ld2 {t : State} {base : Addr} (ht : Scr t base) {d e : Nat} (hd : d % 8 = 0) (hd' : d + 8 ≤ 8192)
    (he : e % 8 = 0) (he' : e + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 d) 8 ∧
      (d % 8 = 0 ∧ d < 4096 * 8) ∧ InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 e) 8 ∧
      (e % 8 = 0 ∧ e < 4096 * 8) :=
  ⟨ht.read hd', ⟨hd, by omega⟩, ht.read he', ⟨he, by omega⟩⟩

theorem subStep_ok {t : State} {base : Addr} (ht : Scr t base) {o a b i : Nat} (hi : i < 8)
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)]) t fun u =>
      u.mem = t.mem.writeW (off base (o + 8 * i))
        (word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) ∧
      Keeps [.x4, .x5] t u := by
  obtain ⟨ra, aa, rb, ab⟩ := ld2 ht (d := a + 8 * i) (e := b + 8 * i) (by omega) (by omega) (by omega)
    (by omega)
  have wo := ht.write (d := o + 8 * i) (n := 8) (by omega)
  have ao : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 := by simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, aa, ab, ao, ra, rb, wo, and_self,
      Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [tw.1, tw.2, ite_false, BitVec.setWidth_eq, write8_eq, read8_eq, twoPReg_val h0 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem away_word {base : Addr} {outs : List Nat} {m m' : Mem}
    (h : ∀ x, Away base outs 64 x → m' x = m x) {d : Nat} (hd : d + 8 ≤ 8192)
    (ho : ∀ o ∈ outs, d + 8 ≤ o ∨ o + 64 ≤ d) : word m' base d = word m base d :=
  word_congr hd fun x h1 h2 => h x fun o h' => by have := ho o h'; omega

theorem writeW_frame {base : Addr} (m : Mem) {d : Nat} (hd : d + 8 ≤ 8192) (v : BitVec 64) (x : Addr)
    (hx : ofs base x < d ∨ d + 8 ≤ ofs base x) : (m.writeW (off base d) v) x = m x :=
  writeW_outside m base v hd x hx

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hoa : o + 64 ≤ a ∨ a + 64 ≤ o) (hob : o + 64 ≤ b ∨ b + 64 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.sub o a b)) s fun t =>
      (∀ i < 8, word t.mem base (o + 8 * i) =
        word s.mem base (a + 8 * i) + twoPW i - word s.mem base (b + 8 * i)) ∧
      (∀ x, Away base [o] 64 x → t.mem x = s.mem x) ∧ Keeps [.x0, .x2, .x4, .x5] s t := by
  rw [Impl.Curve448.AArch64.Fast.sub, WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have := limbs_loop (base := base) (outs := [o]) (rs := [.x4, .x5])
    (body := fun i => [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)])
    (fun u => u.gpr .x0 = K2 ∧ u.gpr .x2 = K4)
    (fun u v ⟨h0, h2⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2⟩) (by decide)
    (fun _ i => word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) t
    (fun i hi u us ⟨h0, h2⟩ hm => WP.mono (subStep_ok us hi ho ha hb ho8 ha8 hb8 h0 h2)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'; subst ho'
          rw [wm, word, Mem.readW_writeW_self64, away_word hm (by omega) (by simp; omega),
            away_word hm (by omega) (by simp; omega)],
        fun x hx => by rw [wm]; exact writeW_frame _ (by omega) _ x (hx o (by simp)), wk⟩)
    (by simp; omega) (by simp) ts ⟨t0, t2⟩
  refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun i hi => by rw [uv o (by simp) i hi, tm], fun x hx => by
    rw [um x hx, tm], (tk.mono (by decide)).trans (uk.mono (by decide))⟩

theorem addSubStep_ok {t : State} {base : Addr} (ht : Scr t base) {o₁ o₂ a b i : Nat} (hi : i < 8)
    (ho₁ : o₁ + 64 ≤ 8192) (ho₂ : o₂ + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ho₁8 : o₁ % 8 = 0) (ho₂8 : o₂ % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)]) t fun u =>
      u.mem = (t.mem.writeW (off base (o₁ + 8 * i))
        (word t.mem base (a + 8 * i) + word t.mem base (b + 8 * i))).writeW (off base (o₂ + 8 * i))
        (word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) ∧
      Keeps [.x4, .x5, .x6, .x7] t u := by
  obtain ⟨ra, aa, rb, ab⟩ := ld2 ht (d := a + 8 * i) (e := b + 8 * i) (by omega) (by omega) (by omega)
    (by omega)
  have wo₁ := ht.write (d := o₁ + 8 * i) (n := 8) (by omega)
  have wo₂ := ht.write (d := o₂ + 8 * i) (n := 8) (by omega)
  have ao₁ : (o₁ + 8 * i) % 8 = 0 ∧ o₁ + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have ao₂ : (o₂ + 8 * i) % 8 = 0 ∧ o₂ + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 ∧ twoPReg i ≠ .x6 ∧ twoPReg i ≠ .x7 := by
    simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, aa, ab, ao₁, ao₂, ra, rb, wo₁, wo₂,
      and_self, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [tw.1, tw.2.1, tw.2.2.1, ite_false, BitVec.setWidth_eq, write8_eq, read8_eq,
      twoPReg_val h0 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, ite_false]

theorem addSub_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ a b : Nat}
    (ho₁ : o₁ + 64 ≤ 8192) (ho₂ : o₂ + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ho₁8 : o₁ % 8 = 0) (ho₂8 : o₂ % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) (h1a : o₁ + 64 ≤ a ∨ a + 64 ≤ o₁)
    (h1b : o₁ + 64 ≤ b ∨ b + 64 ≤ o₁) (h2a : o₂ + 64 ≤ a ∨ a + 64 ≤ o₂)
    (h2b : o₂ + 64 ≤ b ∨ b + 64 ≤ o₂) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.addSub o₁ o₂ a b)) s fun t =>
      (∀ i < 8, word t.mem base (o₁ + 8 * i) = word s.mem base (a + 8 * i) + word s.mem base (b + 8 * i)) ∧
      (∀ i < 8, word t.mem base (o₂ + 8 * i) =
        word s.mem base (a + 8 * i) + twoPW i - word s.mem base (b + 8 * i)) ∧
      (∀ x, Away base [o₁, o₂] 64 x → t.mem x = s.mem x) ∧ Keeps [.x0, .x2, .x4, .x5, .x6, .x7] s t := by
  rw [Impl.Curve448.AArch64.Fast.addSub, WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have ne : o₁ ≠ o₂ := by omega
  have := limbs_loop (base := base) (outs := [o₁, o₂]) (rs := [.x4, .x5, .x6, .x7])
    (body := fun i => [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)])
    (fun u => u.gpr .x0 = K2 ∧ u.gpr .x2 = K4)
    (fun u v ⟨h0, h2⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2⟩) (by decide)
    (fun o i => if o = o₁ then word t.mem base (a + 8 * i) + word t.mem base (b + 8 * i)
      else word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) t
    (fun i hi u us ⟨h0, h2⟩ hm => WP.mono (addSubStep_ok us hi ho₁ ho₂ ha hb ho₁8 ho₂8 ha8 hb8 h0 h2)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => by
          have ea := away_word hm (d := a + 8 * i) (by omega) (by simp; omega)
          have eb := away_word hm (d := b + 8 * i) (by omega) (by simp; omega)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
          rcases ho' with rfl | rfl
          · rw [wm, VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ (by omega) (by omega) (by omega),
              ite_eq_right (by omega), word, Mem.readW_writeW_self64, ite_eq_left rfl, ea, eb]
          · rw [wm, word, Mem.readW_writeW_self64, ite_eq_right (Ne.symm ne), ea, eb],
        fun x hx => by
          rw [wm, writeW_frame _ (by omega) _ x (hx o₂ (by simp)),
            writeW_frame _ (by omega) _ x (hx o₁ (by simp))], wk⟩)
    (by simp; omega) (by simp; omega) ts ⟨t0, t2⟩
  refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun i hi => ?_, fun i hi => ?_, fun x hx => by
    rw [um x hx, tm], (tk.mono (by decide)).trans (uk.mono (by decide))⟩
  · rw [uv o₁ (by simp) i hi, ite_eq_left rfl, tm]
  · rw [uv o₂ (by simp) i hi, ite_eq_right (Ne.symm ne), tm]

end VG.Proof.Curve448.AArch64.Fast
