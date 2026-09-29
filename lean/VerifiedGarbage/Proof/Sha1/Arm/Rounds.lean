import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sha1.Spec
import VerifiedGarbage.Impl.Sha1.Arm

/-!
# SHA-1 compression function on ARMv7: the message schedule and the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha1.Arm

open VG VG.Arm VG.Impl.Sha1.Arm
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4]

/-- The pointers and the count: never written by the rounds. -/
def pubRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : BitVec 32) (j : Nat) : Addr := State.addr (scr + BitVec.ofNat 32 (slot j))

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .r4, work.getD ((1 + 5 - c) % 5) .r4,
      work.getD ((2 + 5 - c) % 5) .r4, work.getD ((3 + 5 - c) % 5) .r4,
      work.getD ((4 + 5 - c) % 5) .r4].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne' : ∀ r ∈ work, r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T1 ∧ r ≠ T2 ∧ r ∉ pubRegs := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T1 ∧ r ≠ T2 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T1 ∧ r ≠ T2 := pubRegs_ne' r h

/-! ## One round -/

/-- `fₜ` as the code computes it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x ||| y) &&& z ||| x &&& y

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  split_ifs <;> simp only [fval, ch_eq, maj_eq, Spec.Sha1.parity]

theorem fcode_ok (g : Fn) (b c d : Reg) (s : State) (x y z : Word)
    (hbw : b ∈ work) (hcw : c ∈ work) (hdw : d ∈ work)
    (hb : s.gpr b = x) (hc : s.gpr c = y) (hd : s.gpr d = z) :
    WP isa (.block (fcode g b c d)) s fun s' =>
      s'.gpr T1 = fval g x y z ∧ (∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨b1, -, -⟩ := work_ne hbw
  obtain ⟨c1, -, -⟩ := work_ne hcw
  obtain ⟨d1, -, -⟩ := work_ne hdw
  simp only [T1, T2] at b1 c1 d1 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp (config := {decide := true}) only [fcode, T1, T2, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.setReg,
    ite_true, ite_false, b1, c1, d1, hb, hc, hd,
    Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨rfl, fun r h1 h2 => by simp [h1, h2], ?_⟩ <;> trivial

theorem sum_ok (t : Nat) (a b e : Reg) (s : State) (x y z fv w : Word) (scr : BitVec 32)
    (hbw : b ∈ work) (hew : e ∈ work) (hbe : b ≠ e)
    (ha : s.gpr a = x) (hb : s.gpr b = y) (he : s.gpr e = z) (hf : s.gpr T1 = fv)
    (hr3 : s.gpr .r3 = scr) (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) :
    WP isa (.block (sum t a b e)) s fun s' =>
      s'.gpr e = x.rotateRight 27 + fv + z + K t + w ∧
      s'.gpr b = y.rotateRight 2 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨b1, b2, -⟩ := work_ne hbw
  obtain ⟨e1, e2, -⟩ := work_ne hew
  have heb := hbe.symm
  have hs : slot t < 4096 := by simp only [slot]; omega
  simp only [slotAddr] at hin hw
  simp only [T1, T2] at b1 b2 e1 e2 hf ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [sum, T1, T2, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.setReg, State.load32,
    ite_true, ite_false, b1, b2, e1, e2, hbe, heb, ha, hb, he, hf, hr3, hin, hw, hs,
    movw_movt, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], trivial⟩

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by omega)
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by omega)
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by omega)

/-- The round is symbolically executed once per function `f`, for any
registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word) (scr : BitVec 32)
    (hv : Vars t s v) (hr3 : s.gpr .r3 = scr) (hin : InRegions (s.rd ++ s.wr) (slotAddr scr t) 4)
    (hw : s.mem.readW (slotAddr scr t) 32 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, -, -, h04⟩, ⟨h12, h13, h14⟩, ⟨-, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  rw [Impl.Sha1.Arm.round, WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ s _ _ _ m1 m2 m3 h1 h2 h3)
    fun s₁ ⟨hT1, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r ∈ work, s₁.gpr r = s.gpr r := fun r hr =>
    hk₁ r (work_ne hr).1 (work_ne hr).2.1
  refine WP.mono (sum_ok t (var t 0) (var t 1) (var t 4) s₁ v[0] v[1] v[4] _ w scr m1 m4 h14
    (by rw [k₁ _ m0, h0]) (by rw [k₁ _ m1, h1]) (by rw [k₁ _ m4, h4]) hT1
    (by rw [hk₁ _ (by decide) (by decide), hr3]) (by rw [hrd₁, hwr₁]; exact hin)
    (by rw [hm₁, hw]))
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  refine ⟨?_, by rw [hm₂, hm₁], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁], fun r hr => ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega),
      var_succ t _ (show 1 < 4 by omega), var_succ t _ (show 2 < 4 by omega),
      var_succ t _ (show 3 < 4 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, rotl5]; rfl
    · rw [hk₂ _ h04 h01 (work_ne m0).1 (work_ne m0).2.1, k₁ _ m0, h0]; rfl
    · rw [hb]; simp only [roundKW, rotl30]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).1 (work_ne m2).2.1, k₁ _ m2, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).1 (work_ne m3).2.1, k₁ _ m3, h3]; rfl
  · have hp := pubRegs_ne hr
    have hne : ∀ k, var t k ≠ r := fun k h => (work_ne (var_mem t k)).2.2 (h ▸ hr)
    rw [hk₂ r (Ne.symm (hne 4)) (Ne.symm (hne 1)) hp.1 hp.2, hk₁ r hp.1 hp.2]

/-! ## The message schedule -/

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32)
    (hr1 : s.gpr .r1 = bp) (hr3 : s.gpr .r3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : t < 16 → rev (s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  have hs : ∀ j, slot j < 4096 := fun j => by simp only [slot]; omega
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    have ho : 4 * t < 4096 := by omega
    simp only [Impl.Sha1.Arm.schedule, ht, ite_true, T1, T2]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, isa, State.setReg, State.load32,
      State.store32, hr1, hr3, hi, hout, ho, hs, ite_true, ite_false, hb, Option.map_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, fun r h1 _ => ?_⟩
    simp [h1]
  · have hw := hwin (by omega)
    have e3 := hw (t - 3) (by omega) (by omega)
    have e8 := hw (t - 8) (by omega) (by omega)
    have e14 := hw (t - 14) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 3) = slot (t + 13) by simp only [slot]; omega] at e3
    rw [show slot (t - 8) = slot (t + 8) by simp only [slot]; omega] at e8
    rw [show slot (t - 14) = slot (t + 2) by simp only [slot]; omega] at e14
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha1.Arm.schedule, ht, ite_false, T1, T2]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, isa, State.setReg,
      State.load32, State.store32, hr3, hin, hout, hs, ite_true, ite_false,
      e3, e8, e14, e16, Option.map_some, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    rw [rotl1] at hW
    refine ⟨by rw [hW], trivial, trivial, fun r h1 h2 => ?_⟩
    simp [h1, h2]

/-! ## The 80 rounds -/

/-- The scratch area the rounds write: the window. -/
abbrev winRegion (scr : BitVec 32) : Region := ⟨State.addr scr, 64⟩

theorem slotAddr_eq {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    slotAddr scr j = State.addr scr + BitVec.ofNat 64 (slot j) :=
  addr_add (by simp only [slot]; omega)

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem win_contains {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) (j : Nat) :
    (winRegion scr).Contains (slotAddr scr j) 4 := by
  rw [slotAddr_eq h]; exact contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 112 ≤ 2 ^ 32) {i j : Nat}
    (hij : i % 16 ≠ j % 16) : Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  intro x hx hy
  rw [slotAddr_eq h] at hx hy
  simp only [slot] at hx hy
  have hi : i % 16 < 16 := Nat.mod_lt _ (by omega)
  have hj : j % 16 < 16 := Nat.mod_lt _ (by omega)
  generalize i % 16 = p at *
  generalize j % 16 = q at *
  generalize State.addr scr = a at *
  bv_omega

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) :
    Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hscr : scr.toNat + 112 ≤ 2 ^ 32)
    (hr1 : sB.gpr .r1 = bp) (hr3 : sB.gpr .r3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 →
      InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * t))) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev (m.readW (State.addr (bp + BitVec.ofNat 32 (4 * t))) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_r1 : s.gpr .r1 = bp := (hs.pub .r1 (by decide)).trans hr1
    have hs_r3 : s.gpr .r3 = scr := (hs.pub .r3 (by decide)).trans hr3
    refine WP.mono (schedule_ok t s M bp scr hs_r1 hs_r3
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1
      simp only [Vars, e] at hv ⊢
      exact hv
    have hr3₁ : s₁.gpr .r3 = scr := by
      rw [hr₁ .r3 (by decide) (by decide), hs_r3]
    have hself : s₁.mem.readW (slotAddr scr t) 32 = W M t := by
      rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
    refine WP.mono (round_ok t s₁ _ _ scr hv₁ hr3₁
      (by rw [hrd₁, hwr₁, hs.rd, hs.wr]; exact hin t) hself) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains hscr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep hscr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha1.Arm
