import VerifiedGarbage.Proof.X448.Wide.Columns
import VerifiedGarbage.Proof.X448.Wide.Bridge

/-! Untrusted: staging normalized 28-bit field slots for the wide kernel. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem pack_word (lo hi : BitVec 64) (hl : lo.toNat < VG.Proof.X448.radix)
    (hh : hi.toNat < VG.Proof.X448.radix) :
    (lo + (hi <<< 28)).toNat = lo.toNat + VG.Proof.X448.radix * hi.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [VG.Proof.X448.radix] at hl hh ⊢
  have hb : hi.toNat * 2 ^ 28 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
  omega

theorem packStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 128 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 8)
    (hb : Bounded s.mem base a) :
    WP isa (.block (packStep o a i)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i))
        (BitVec.ofNat 64 (paired (limbs s.mem base a) i)) ∧ Keeps [.x4, .x5] s t := by
  have al := hs.read (d := a + 16 * i) (n := 8) (by omega)
  have bl := hs.read (d := a + 16 * i + 8) (n := 8) (by omega)
  have ow := hs.write (d := o + 8 * i) (n := 8) (by omega)
  have ae : (a + 16 * i) % 8 = 0 ∧ a + 16 * i < 32768 := ⟨by omega, by omega⟩
  have be : (a + 16 * i + 8) % 8 = 0 ∧ a + 16 * i + 8 < 32768 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega, by omega⟩
  have e0 : a + 8 * (2 * i) = a + 16 * i := by omega
  have e1 : a + 8 * (2 * i + 1) = a + 16 * i + 8 := by omega
  apply WP.of_runBlock
  simp only [packStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, Size.bits, ae, be, oe, and_self, State.read, State.load, State.store,
    hs.x3, al, bl, ow, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Nat.reduceLT,
    Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (o + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    have h0 : (word s.mem base (a + 16 * i)).toNat < VG.Proof.X448.radix := by
      simpa only [limbs, e0] using hb (2 * i) (by omega)
    have h1 : (word s.mem base (a + 16 * i + 8)).toNat < VG.Proof.X448.radix := by
      simpa only [limbs, e1] using hb (2 * i + 1) (by omega)
    rw [pack_word _ _ h0 h1, BitVec.toNat_ofNat]
    have cap := paired_bound hb i hi
    rw [Nat.mod_eq_of_lt (Nat.lt_trans cap (show radix < 2 ^ 64 by decide))]
    simp only [paired, limbs, e0, e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem pack_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 128 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : a + 128 ≤ o ∨ o + 64 ≤ a) (hb : Bounded s.mem base a) :
    WP isa (.block (pack o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = paired (limbs s.mem base a) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = paired (limbs s.mem base a) i) ∧
    Outside base o 64 s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (packStep o a n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 16, limbs t.mem base a i = limbs s.mem base a i :=
      fun i hi => tm.limbs (by omega) ha hi
    have tb : Bounded t.mem base a := by
      intro i hi
      rw [av i hi]
      exact hb i hi
    refine WP.mono (packStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn tb)
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]
      exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write _ base (by omega) (by omega)]
    by_cases h : i = n
    · subst i
      rw [ite_eq_left rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (paired_bound tb n hn) (show radix < 2 ^ 64 by decide))]
      simp only [paired]
      rw [av (2 * n) (by omega), av (2 * n + 1) (by omega)]
    · rw [ite_eq_right h]
      exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Wide
