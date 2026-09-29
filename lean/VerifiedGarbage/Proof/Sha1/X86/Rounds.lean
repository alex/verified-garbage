import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Sha1.Spec
import VerifiedGarbage.Impl.Sha1.X86
import Mathlib.Tactic.SplitIfs

/-!
# SHA-1 compression function on x86 (32-bit): the message schedule and the rounds

Untrusted: everything here is checked by Lean. As on x86-64 (each function
`f` symbolically executed once, for any registers), with `Wₜ` added into `e`
first and `Maj` as a sum of two terms.
-/

namespace VG.Proof.Sha1.X86

open VG VG.X86 VG.Impl.Sha1.X86
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3] ∧
  s.gpr (var t 4) = v[4]

/-- The scratch pointer and `esp`: never written by the rounds. -/
def pubRegs : List Reg := [.ebp, .esp]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 4) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 4 := by
  simp only [var]; congr 1; omega

/-- The registers of the working variables are all different. -/
theorem round_nodup (t : Nat) : [var t 0, var t 1, var t 2, var t 3, var t 4].Nodup := by
  have h : ∀ c < 5, [work.getD ((0 + 5 - c) % 5) .eax, work.getD ((1 + 5 - c) % 5) .eax,
      work.getD ((2 + 5 - c) % 5) .eax, work.getD ((3 + 5 - c) % 5) .eax,
      work.getD ((4 + 5 - c) % 5) .eax].Nodup := by decide
  exact h (t % 5) (Nat.mod_lt _ (by omega))

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 5 - t % 5) % 5]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T ∧ r ∉ pubRegs := by
  simp only [work, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T := by
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

/-! ## One round -/

/-- `Maj` is the sum of two terms without common bits. -/
theorem maj_add (x y z : Word) : Spec.Sha1.maj x y z = (x &&& y) + ((x ^^^ y) &&& z) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i; simp only [Spec.Sha1.maj, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
    cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl
  · ext i; simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_zero]
    cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

/-- `fₜ` as the code computes it. -/
def fval : Fn → Word → Word → Word → Word
  | .ch, x, y, z => (y ^^^ z) &&& x ^^^ z
  | .parity, x, y, z => x ^^^ y ^^^ z
  | .maj, x, y, z => (x &&& y) + ((x ^^^ y) &&& z)

theorem f_eq (t : Nat) (x y z : Word) : f t x y z = fval (fn t) x y z := by
  unfold Spec.Sha1.f fn
  split_ifs <;> simp only [fval, ch_eq, maj_add, Spec.Sha1.parity]

theorem fcode_ok (g : Fn) (b c d e : Reg) (s : State) (x y z u : Word)
    (hbw : b ∈ work) (hcw : c ∈ work) (hdw : d ∈ work) (hew : e ∈ work) (hbe : b ≠ e) (hce : c ≠ e)
    (hde : d ≠ e) (hb : s.gpr b = x) (hc : s.gpr c = y) (hd : s.gpr d = z) (he : s.gpr e = u) :
    WP isa (.block (fcode g b c d e)) s fun s' =>
      s'.gpr e = u + fval g x y z ∧ (∀ r, r ≠ e → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have b1 := (work_ne hbw).1; have c1 := (work_ne hcw).1; have d1 := (work_ne hdw).1
  have e1 := (work_ne hew).1
  simp only [T] at b1 c1 d1 e1 ⊢
  apply WP.of_runBlock
  cases g <;>
  simp (config := {decide := true}) only [fcode, T, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, State.setReg, arithFlags,
    State.setFlags, ite_true, ite_false, b1, c1, d1, e1, hbe, hce, hde, hb, hc, hd, he,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun r h1 h2 => by simp [h1, h2], trivial⟩
  · rfl
  · rfl
  · simp only [fval, BitVec.add_assoc]

theorem sum_ok (t : Nat) (a b e : Reg) (s : State) (x y z : Word)
    (hbe : b ≠ e) (hbw : b ∈ work) (hew : e ∈ work)
    (ha : s.gpr a = x) (hb : s.gpr b = y) (he : s.gpr e = z) :
    WP isa (.block (sum t a b e)) s fun s' =>
      s'.gpr e = z + x.rotateRight 27 + K t ∧ s'.gpr b = y.rotateRight 2 ∧
      (∀ r, r ≠ e → r ≠ b → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have b1 := (work_ne hbw).1; have e1 := (work_ne hew).1
  have heb := hbe.symm
  simp only [T] at b1 e1 ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [sum, T, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execShift, readSrc, isa, State.setReg,
    arithFlags, State.setFlags, ite_true, ite_false, b1, e1, hbe, heb, ha, hb, he,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial⟩

theorem rotl5 (x : Word) : x.rotateLeft 5 = x.rotateRight 27 := rotateLeft_eq x (by omega)
theorem rotl30 (x : Word) : x.rotateLeft 30 = x.rotateRight 2 := rotateLeft_eq x (by omega)
theorem rotl1 (x : Word) : x.rotateLeft 1 = x.rotateRight 31 := rotateLeft_eq x (by omega)

theorem sum_order (a fv e k w : Word) : e + w + fv + a + k = a + fv + e + k + w := by ac_rfl

/-- The round is symbolically executed once per function `f`, for any
registers `a … e`. -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr T = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (f t v[1] v[2] v[3]) (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  have hd := round_nodup t
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hd
  have m0 := var_mem t 0; have m1 := var_mem t 1; have m2 := var_mem t 2
  have m3 := var_mem t 3; have m4 := var_mem t 4
  have e4 := (work_ne m4).1
  rw [Impl.Sha1.X86.round]
  -- `e := e + Wₜ`
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  set s₀ : State := (arithFlags s (s.gpr (var t 4) + s.gpr T) (2 ^ 32 ≤ (s.gpr (var t 4)).toNat +
    (s.gpr T).toNat) (addOverflow (s.gpr (var t 4)) (s.gpr T) (s.gpr (var t 4) + s.gpr T))).setReg (var t 4)
    (s.gpr (var t 4) + s.gpr T) with hs₀
  have k₀ : ∀ r, r ≠ var t 4 → s₀.gpr r = s.gpr r := fun r h => by simp [hs₀, State.setReg, h]
  have e₀ : s₀.gpr (var t 4) = v[4] + w := by simp [hs₀, State.setReg, h4, hw]
  rw [WP.block_append_iff]
  refine WP.mono (fcode_ok (fn t) _ _ _ _ s₀ v[1] v[2] v[3] (v[4] + w) m1 m2 m3 m4 h14 h24 h34
    (by rw [k₀ _ h14, h1]) (by rw [k₀ _ h24, h2]) (by rw [k₀ _ h34, h3]) e₀)
    fun s₁ ⟨he₁, hk₁, hm₁, hrd₁, hwr₁⟩ => ?_
  have k₁ : ∀ r, r ≠ var t 4 → r ≠ T → s₁.gpr r = s.gpr r := fun r h h' => by rw [hk₁ r h h', k₀ r h]
  refine WP.mono (sum_ok t (var t 0) (var t 1) (var t 4) s₁ v[0] v[1] _ h14 m1 m4
    (by rw [k₁ _ h04 (work_ne m0).1, h0]) (by rw [k₁ _ h14 (work_ne m1).1, h1]) he₁)
    fun s₂ ⟨he, hb, hk₂, hm₂, hrd₂, hwr₂⟩ => ?_
  refine ⟨?_, by rw [hm₂, hm₁]; rfl, by rw [hrd₂, hrd₁]; rfl, by rw [hwr₂, hwr₁]; rfl, fun r hr => ?_⟩
  · simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega),
      var_succ t _ (show 1 < 4 by omega), var_succ t _ (show 2 < 4 by omega),
      var_succ t _ (show 3 < 4 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he, ← f_eq]; simp only [roundKW, rotl5]
      exact sum_order _ _ _ _ _
    · rw [hk₂ _ h04 h01 (work_ne m0).1, k₁ _ h04 (work_ne m0).1, h0]; rfl
    · rw [hb]; simp only [roundKW, rotl30]; rfl
    · rw [hk₂ _ h24 (Ne.symm h12) (work_ne m2).1, k₁ _ h24 (work_ne m2).1, h2]; rfl
    · rw [hk₂ _ h34 (Ne.symm h13) (work_ne m3).1, k₁ _ h34 (work_ne m3).1, h3]; rfl
  · have hp := pubRegs_ne hr
    have hne : ∀ k, var t k ≠ r := fun k h => (work_ne (var_mem t k)).2 (h ▸ hr)
    rw [hk₂ r (Ne.symm (hne 4)) (Ne.symm (hne 1)) hp, k₁ r (Ne.symm (hne 4)) hp]

/-! ## The message schedule -/

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : BitVec 32) (j : Nat) : Addr := addr scr (4 * (j % 16))

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : BitVec 32)
    (hebp : s.gpr .ebp = scr) (hbpin : InRegions (s.rd ++ s.wr) (addr scr bpOff) 4)
    (hbp : s.mem.readW (addr scr bpOff) 32 = bp)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 4)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (addr bp (4 * t)) 4)
    (hblk : t < 16 → bswap (s.mem.readW (addr bp (4 * t)) 32) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha1.X86.schedule, ht, ite_true, slot, at_, T]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, isa, ea_mk,
      State.load32, State.store32, State.setReg, hebp, hbpin, hbp, hi, hout, ite_true,
      ite_false, hb, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 => ?_⟩
    simp [h0]
  · have hw := hwin (by omega)
    have e3 := hw (t - 3) (by omega) (by omega)
    have e8 := hw (t - 8) (by omega) (by omega)
    have e14 := hw (t - 14) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show (t - 3) % 16 = (t + 13) % 16 by omega] at e3
    rw [show (t - 8) % 16 = (t + 8) % 16 by omega] at e8
    rw [show (t - 14) % 16 = (t + 2) % 16 by omega] at e14
    rw [show (t - 16) % 16 = t % 16 by omega] at e16
    simp only [Impl.Sha1.X86.schedule, ht, ite_false, slot, at_, T]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, execShift, readSrc,
      isa, ea_mk, State.load32, State.store32, State.setReg, arithFlags,
      State.setFlags, hebp, hin, hout, ite_true, ite_false, e3, e8, e14, e16,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    rw [rotl1] at hW
    refine ⟨by rw [hW], by rw [hW], trivial, trivial, fun r h0 => ?_⟩
    simp [h0]

/-! ## The 80 rounds -/

/-- The window `⟨scr, 64⟩`. -/
abbrev winRegion (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 64⟩

theorem win_contains {scr : BitVec 32} (h : scr.toNat + 64 ≤ 2 ^ 32) (j : Nat) :
    (winRegion scr).Contains (slotAddr scr j) 4 := by
  have : j % 16 < 16 := Nat.mod_lt _ (by omega)
  simp only [Region.Contains, slotAddr]
  rw [addr_eq (by omega)]
  generalize j % 16 = p at *
  rw [show scr.setWidth 64 + BitVec.ofNat 64 (4 * p) - scr.setWidth 64 = BitVec.ofNat 64 (4 * p) by bv_omega]
  simp only [BitVec.toNat_ofNat]
  omega

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 64 ≤ 2 ^ 32) {i j : Nat} (hij : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  have hi : i % 16 < 16 := Nat.mod_lt _ (by omega)
  have hj : j % 16 < 16 := Nat.mod_lt _ (by omega)
  intro x hx hy
  simp only [slotAddr] at hx hy
  rw [addr_eq (by omega)] at hx hy
  generalize i % 16 = p at *
  generalize j % 16 = q at *
  generalize scr.setWidth 64 = a at *
  bv_omega

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : BitVec 32) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha1.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 32 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hfit : scr.toNat + 64 ≤ 2 ^ 32) (hebp : sB.gpr .ebp = scr)
    (hbpin : InRegions (sB.rd ++ sB.wr) (addr scr bpOff) 4)
    (hbp : ∀ m, Frame [winRegion scr] sB.mem m → m.readW (addr scr bpOff) 32 = bp)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 4)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 4)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (addr bp (4 * t)) 4)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → bswap (m.readW (addr bp (4 * t)) 32) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_ebp : s.gpr .ebp = scr := (hs.pub .ebp (by decide)).trans hebp
    refine WP.mono (schedule_ok t s M bp scr hs_ebp (by rw [hs.rd, hs.wr]; exact hbpin) (hbp _ hs.frame)
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha1.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => hr₁ _ (work_ne (var_mem t k)).1
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · rw [rounds_succ, round_eq]; exact hv₂
    · rw [hr₂ r hr, hr₁ r (pubRegs_ne hr), hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains hfit t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep hfit (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha1.X86
