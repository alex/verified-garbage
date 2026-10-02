import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Sha1.Spec
import VerifiedGarbage.Impl.Sha1.X86
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Sha1.X86.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SHA-1 compression function on x86 (32-bit): the message schedule and the rounds

As on x86-64 (each function `f` symbolically executed once, for any
registers), with `Wₜ` added into `e` first and `Maj` as a sum of two terms.
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
    runBlock_nil, exec, execAlu, readSrc, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    ite_true, ite_false, b1, c1, d1, e1, hbe, hce, hde, hb, hc, hd, he,
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
    runBlock_nil, exec, execAlu, execShift, readSrc, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, b1, e1, hbe, heb, ha, hb, he,
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
  have k₀ : ∀ r, r ≠ var t 4 → s₀.gpr r = s.gpr r := fun r h => by simp [hs₀, RegUpd.gpr_setReg, h]
  have e₀ : s₀.gpr (var t 4) = v[4] + w := by simp [hs₀, RegUpd.gpr_setReg, h4, hw]
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
      State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, hebp, hbpin, hbp, hi, hout, ite_true,
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
      isa, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
      RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, hebp, hin, hout, ite_true, ite_false, e3, e8, e14, e16,
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
  simp only [slotAddr]
  rw [addr_eq (by omega)]
  exact Offset.contains_base _ (by omega) (by omega)

theorem slot_sep {scr : BitVec 32} (h : scr.toNat + 64 ≤ 2 ^ 32) {i j : Nat} (hij : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 4 (slotAddr scr j) 4 := by
  simp only [slotAddr]
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

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

/-!
# SHA-1 compression function on x86 (32-bit): the whole function
-/

namespace VG.Proof.Sha1.X86

open VG VG.X86 VG.Impl.Sha1.X86
open VG.Spec.Sha1 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(st s₀).setWidth 64, 20⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 64 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 112⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((st s₀).setWidth 64)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := addr (st s₀) (4 * k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 20 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 5) :
    stAddr s₀ k = (st s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by have := h.st_fits; omega)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    addr (blkAddr s₀ i) (4 * t) =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega)]
  have e : (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    have := addr_eq (x := bp s₀) (k := 64 * i) (by omega)
    simpa only [addr] using this
  rw [e]

theorem scr_eq {d : Nat} (hd : d < 112) :
    addr (scr s₀) d = (scr s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.scr_fits; omega)

theorem in_scr {d : Nat} (hd : d + 4 ≤ 112) : InRegions (s₀.rd ++ s₀.wr) (addr (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.scr_eq (by omega))⟩

theorem out_scr {d : Nat} (hd : d + 4 ≤ 112) : InRegions s₀.wr (addr (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.scr_eq (by omega))⟩

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  show Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (esp₀ s₀) 4, 16⟩
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (addr (blkAddr s₀ i) (4 * t)) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem st_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 20) (he : e + 4 ≤ 20)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (st s₀) d) 4 (addr (st s₀) e) 4 := by
  have := hp.st_fits
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ hde (by omega) (by omega)

/-- Reading the hash value at offset `d` after writing it at offset `e`. -/
theorem readW_writeW_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 20) (he : e + 4 ≤ 20) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (st s₀) e) v).readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 :=
  Mem.readW_writeW_sep (st_sep hp hd he hde) (by decide)

theorem st_eq {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 20) :
    addr (st s₀) d = (st s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem in_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem out_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 20) :
    InRegions s₀.wr (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 5) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m ((st s₀).setWidth 64) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 5) :
    (stateAt m ((st s₀).setWidth 64))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

theorem scr_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (scr s₀) e) 4 (addr (scr s₀) d) 4 := by
  rw [hp.scr_eq (by omega), hp.scr_eq (by omega)]
  exact Offset.sep _ hde.symm (by omega) (by omega)

/-- Reading `[scr + e]` after writing `[scr + d]`. -/
theorem readW_writeW_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (x : Word)
    {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (scr s₀) d) x).readW (addr (scr s₀) e) 32 = m.readW (addr (scr s₀) e) 32 :=
  Mem.readW_writeW_sep (scr_sep hp hd he hde) (by decide)

theorem st_scr_sep {s₀ : State} (hp : Pre s₀) {e d : Nat} (he : e + 4 ≤ 20) (hd : d + 4 ≤ 112) :
    Mem.Sep (addr (st s₀) e) 4 (addr (scr s₀) d) 4 :=
  hp.st_scr.sep (contains_sub he (by omega) (st_eq hp (by omega)))
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))

/-- Reading the hash value after writing the scratch buffer. -/
theorem readW_writeW_scr_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 20) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (st s₀) e) 32 = m.readW (addr (st s₀) e) 32 :=
  Mem.readW_writeW_sep (st_scr_sep hp he hd) (by decide)

/-- Reading the scratch buffer after writing the hash value. -/
theorem readW_writeW_st_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 20) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (st s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (fun x h₁ h₂ => st_scr_sep hp he hd x h₂ h₁) (by decide)

/-! ## The loop invariant -/

/-- The callee-saved registers and their slots in the scratch buffer. -/
def compressSaved : Spill.Slots := [(.ebx, 64), (.esi, 68), (.edi, 72), (.ebp, 76)]

theorem compressSaved_fits : Spill.Fits 80 compressSaved := by decide

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scr s₀)) s₀.gpr compressSaved

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((st s₀).setWidth 64) =
    compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`: the block pointer and the
count of blocks left are in the scratch buffer. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  bpw : s.mem.readW (addr (scr s₀) bpOff) 32 = blkAddr s₀ i
  nw : s.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [.mov .edi (.mem ⟨.esp, 4⟩), .mov .eax (.mem ⟨.edi, 0⟩),
    .mov .ebx (.mem ⟨.edi, 4⟩), .mov .ecx (.mem ⟨.edi, 8⟩), .mov .edx (.mem ⟨.edi, 12⟩),
    .mov .esi (.mem ⟨.edi, 16⟩)] := by
  decide

theorem update_eq : update = [.mov .edi (.mem ⟨.esp, 4⟩),
    .alu .add .eax (.mem ⟨.edi, 0⟩), .alu .add .ebx (.mem ⟨.edi, 4⟩),
    .alu .add .ecx (.mem ⟨.edi, 8⟩), .alu .add .edx (.mem ⟨.edi, 12⟩), .alu .add .esi (.mem ⟨.edi, 16⟩),
    .store ⟨.edi, 0⟩ .eax, .store ⟨.edi, 4⟩ .ebx, .store ⟨.edi, 8⟩ .ecx, .store ⟨.edi, 12⟩ .edx,
    .store ⟨.edi, 16⟩ .esi] := by
  decide

theorem advance_eq : advance = [.mov .eax (.mem ⟨.ebp, 80⟩), .alu .add .eax (.imm 64),
    .store ⟨.ebp, 80⟩ .eax, .mov .eax (.mem ⟨.ebp, 84⟩), .alu .sub .eax (.imm 1),
    .store ⟨.ebp, 84⟩ .eax] := rfl

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .eax = v[0] ∧ s.gpr .ebx = v[1] ∧ s.gpr .ecx = v[2] ∧ s.gpr .edx = v[3] ∧
    s.gpr .esi = v[4] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hesp : s.gpr .esp = esp₀ s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem ((st s₀).setWidth 64)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  have hin : ∀ d, d + 4 ≤ 20 → InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 := by
    rw [hrd, hwr]; exact fun d hd => in_st hp hd
  have h0 := hin 0 (by decide); have h1 := hin 4 (by decide); have h2 := hin 8 (by decide)
  have h3 := hin 12 (by decide); have h4 := hin 16 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_mk,
    State.load32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hesp, ia, harg, h0, h1, h2, h3, h4, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 5 by decide), stateAt_get hp _ (show 1 < 5 by decide),
    stateAt_get hp _ (show 2 < 5 by decide), stateAt_get hp _ (show 3 < 5 by decide),
    stateAt_get hp _ (show 4 < 5 by decide), stAddr]
  simp (config := {decide := true}) [pubRegs]

/-- Five words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  let a := addr (st s₀)
  (((((m.writeW (a 0) v[0]).writeW (a 4) v[1]).writeW (a 8) v[2]).writeW (a 12) v[3]).writeW (a 16) v[4])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) ((st s₀).setWidth 64) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState, stAddr]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, readW_writeW_st hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ d, d + 4 ≤ 20 → (stR s₀).Contains (addr (st s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (st_eq hp (by omega))
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 8 ?_)).writeW ?_ _ (c 12 ?_)).writeW
    ?_ _ (c 16 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hesp : s.gpr .esp = esp₀ s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block update) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  have hin : ∀ d, d + 4 ≤ 20 → InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 := by
    rw [hrd, hwr]; exact fun d hd => in_st hp hd
  have hout : ∀ d, d + 4 ≤ 20 → InRegions s.wr (addr (st s₀) d) 4 := by
    rw [hwr]; exact fun d hd => out_st hp hd
  have i0 := hin 0 (by decide); have i1 := hin 4 (by decide); have i2 := hin 8 (by decide)
  have i3 := hin 12 (by decide); have i4 := hin 16 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 4 (by decide); have o2 := hout 8 (by decide)
  have o3 := hout 12 (by decide); have o4 := hout 16 (by decide)
  have m0 : s.mem.readW (addr (st s₀) 0) 32 = H[0] := hH 0 (by decide)
  have m1 : s.mem.readW (addr (st s₀) 4) 32 = H[1] := hH 1 (by decide)
  have m2 : s.mem.readW (addr (st s₀) 8) 32 = H[2] := hH 2 (by decide)
  have m3 : s.mem.readW (addr (st s₀) 12) 32 = H[3] := hH 3 (by decide)
  have m4 : s.mem.readW (addr (st s₀) 16) 32 = H[4] := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.cf_arithFlags,
    hesp, ia, harg, i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [writeState, Vector.getElem_zipWith], ?_⟩
  simp (config := {decide := true}) [pubRegs]

set_option simprocs false in
theorem advance_ok {s₀ : State} (hp : Pre s₀) {s : State} (hebp : s.gpr .ebp = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block advance) s fun s' =>
      s'.mem = (s.mem.writeW (addr (scr s₀) bpOff) (s.mem.readW (addr (scr s₀) bpOff) 32 + 64)).writeW
        (addr (scr s₀) nOff) (s.mem.readW (addr (scr s₀) nOff) 32 - 1) ∧
      s'.zf = some (s.mem.readW (addr (scr s₀) nOff) 32 - 1 == 0) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i80 : InRegions (s.rd ++ s.wr) (addr (scr s₀) 80) 4 := by
    rw [hrd, hwr]; exact hp.in_scr (by omega)
  have i84 : InRegions (s.rd ++ s.wr) (addr (scr s₀) 84) 4 := by
    rw [hrd, hwr]; exact hp.in_scr (by omega)
  have o80 : InRegions s.wr (addr (scr s₀) 80) 4 := by rw [hwr]; exact hp.out_scr (by omega)
  have o84 : InRegions s.wr (addr (scr s₀) 84) 4 := by rw [hwr]; exact hp.out_scr (by omega)
  have hsep := readW_writeW_scr hp s.mem (s.mem.readW (addr (scr s₀) 80) 32 + 64) (d := 80) (e := 84)
    (by omega) (by omega) (by omega)
  simp only [bpOff, nOff]
  apply WP.of_runBlock
  rw [advance_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.cf_arithFlags,
    hebp, i80, i84, o80, o84, hsep, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  simp (config := {decide := true}) [pubRegs]

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    bswap (s₀.mem.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, bswap_readW]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem harg_of {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    m.readW (addr (esp₀ s₀) 4) 32 = st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem win_sub (p : BitVec 32) : Region.Sub (winRegion p) ⟨p.setWidth 64, 112⟩ :=
  Region.sub_prefix (by omega)

/-- A word of the scratch buffer from offset 64 on is outside the window. -/
theorem win_word {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [winRegion (scr s₀)] m m') {d : Nat}
    (hd : 64 ≤ d) (hd' : d + 4 ≤ 112) : m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  rw [hp.scr_eq (by omega)]
  exact Offset.disjoint_base _ hd (by omega)

/-- A word of the scratch buffer is unchanged by writes to the hash value. -/
theorem st_word {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [stR s₀] m m') {d : Nat}
    (hd' : d + 4 ≤ 112) : m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  refine Region.Disjoint.sub_left hp.st_scr.symm ?_
  rw [hp.scr_eq (by omega)]
  exact Offset.sub_base _ hd'

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hfits := hp.scr_fits
  refine WP.seq (WP.mono (load_ok hp hL.esp hL.rd hL.wr (harg_of hp hL.frame))
    fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap (m.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  have hebp₁ : s₁.gpr .ebp = scr s₀ := (hpub₁ .ebp (by decide)).trans hL.ebp
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) (scr s₀) s₁ (by omega) hebp₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_scr (by simp [bpOff]))
    (fun m hm => by rw [win_word hp hm (by simp [bpOff]) (by simp [bpOff]), hm₁]; exact hL.bpw)
    (fun j => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_scr (by omega))
    (fun j => by rw [hwr₁, hL.wr]; exact hp.out_scr (by omega))
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hf₂ : Frame [winRegion (scr s₀)] s.mem s₂.mem := by rw [← hm₁]; exact hR.frame
  have hframe₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hL.frame.trans (hf₂.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩)
  rw [WP.block_append_iff]
  refine WP.mono (update_ok hp _ (stateAt s.mem ((st s₀).setWidth 64)) hR.vars
    (by rw [pub₂ .esp (by decide), hL.esp]) (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr])
    (harg_of hp hframe₂) fun k hk => ?_) fun s₃ ⟨hm₃, hpub₃, hrd₃, hwr₃⟩ => ?_
  · rw [hf₂.readW (contains_sub (by omega) (by omega) (hp.stAddr_eq hk)) hst (by decide),
      stateAt_get hp _ hk]
  have hebp₃ : s₃.gpr .ebp = scr s₀ := by rw [hpub₃ _ (by decide), pub₂ _ (by decide), hL.ebp]
  refine WP.mono (advance_ok hp hebp₃ (by rw [hrd₃, hR.rd, hrd₁, hL.rd]) (by rw [hwr₃, hR.wr, hwr₁, hL.wr]))
    fun s₄ ⟨hm₄, hz₄, hpub₄, hrd₄, hwr₄⟩ => ?_
  have hfs : Frame [stR s₀] s₂.mem s₃.mem := by rw [hm₃]; exact frame_writeState hp (Frame.refl _ _) _
  have r80 : s₃.mem.readW (addr (scr s₀) bpOff) 32 = blkAddr s₀ i := by
    rw [st_word hp hfs (by simp [bpOff]), win_word hp hf₂ (by simp [bpOff]) (by simp [bpOff])]; exact hL.bpw
  have r84 : s₃.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [st_word hp hfs (by simp [nOff]), win_word hp hf₂ (by simp [nOff]) (by simp [nOff])]; exact hL.nw
  rw [r80, r84] at hm₄; rw [r84] at hz₄
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hn : BitVec.ofNat 32 (nb s₀ - i) - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  rw [hn] at hm₄ hz₄
  have hfa : Frame [scrR s₀] s₃.mem s₄.mem := by
    rw [hm₄]; simp only [bpOff, nOff]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub (off := 80) (by omega) (by omega) (hp.scr_eq (by omega)))).writeW
      (List.mem_singleton_self _) _ (contains_sub (off := 84) (by omega) (by omega) (hp.scr_eq (by omega)))
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hframe₂.trans ((hfs.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hfa.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩))
  have hsv : ∀ d, 64 ≤ d → d + 4 ≤ 80 → s₄.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
    intro d h₁ h₂
    rw [hm₄, readW_writeW_scr hp _ _ (by simp [nOff]) (by omega) (by simp [nOff]; omega),
      readW_writeW_scr hp _ _ (by simp [bpOff]) (by omega) (by simp [bpOff]; omega),
      st_word hp hfs (by omega), win_word hp hf₂ h₁ (by omega)]
  have hstate : stateAt s₄.mem ((st s₀).setWidth 64) =
      compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) (i + 1) := by
    have e : stateAt s₄.mem ((st s₀).setWidth 64) = stateAt s₃.mem ((st s₀).setWidth 64) := by
      apply stateAt_eq hp
      intro k hk
      rw [hm₄, readW_writeW_scr_st hp _ _ (by omega) (by simp [nOff]),
        readW_writeW_scr_st hp _ _ (by omega) (by simp [bpOff]), stateAt_get hp _ hk]
    rw [e, hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
    rfl
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₄ := by
    rintro j rfl
    refine ⟨by rw [hpub₄ _ (by decide), hebp₃], by rw [hpub₄ _ (by decide), hpub₃ _ (by decide),
      pub₂ _ (by decide), hL.esp], by rw [hrd₄, hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₄, hwr₃, hR.wr, hwr₁, hL.wr], hframe, hstate, ?_⟩
    exact hL.saved.of_readW fun p h => hsv _ (by revert p h; decide) (compressSaved_fits.1 p h)
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₄, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with bpw := ?_, nw := ?_ }⟩
    · rw [hm₄, readW_writeW_scr hp _ _ (by simp [nOff]) (by simp [bpOff]) (by simp [bpOff, nOff]),
        Mem.readW_writeW_self32]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hm₄, Mem.readW_writeW_self32]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = .mov .eax (.mem ⟨.esp, 16⟩) :: (Spill.saveCode .eax compressSaved ++
    ([.mov .ebp (.reg .eax), .mov .ecx (.mem ⟨.esp, 8⟩), .store ⟨.ebp, 80⟩ .ecx,
      .mov .ecx (.mem ⟨.esp, 12⟩), .store ⟨.ebp, 84⟩ .ecx, .alu .test .ecx (.reg .ecx)] : List Instr)) :=
  rfl

theorem epilogue_eq :
    epilogue = Spill.restoreCode .ebp ([(.ebx, 64), (.esi, 68), (.edi, 72)] ++ [(.ebp, 76)]) ++ [] := rfl

/-- Reading an argument after writing the scratch buffer. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 112) (he : 4 ≤ e) (he' : e + 4 ≤ 20) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (esp₀ s₀) e) 32 = m.readW (addr (esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))) (by decide)

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  ((Spill.saveMem s₀.mem (addr (scr s₀)) s₀.gpr compressSaved).writeW (addr (scr s₀) 80) (bp s₀)).writeW
    (addr (scr s₀) 84) (arg s₀ 2)

theorem compressSaved_contains {s₀ : State} (hp : Pre s₀) : ∀ p ∈ compressSaved, (scrR s₀).Contains (addr (scr s₀) p.2) 4 :=
  fun p h => have := compressSaved_fits.1 p h; contains_sub (by omega) (by omega) (hp.scr_eq (by omega))

/-- Reading an argument after saving the registers. -/
theorem spill_arg {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (Spill.saveMem s₀.mem (addr (scr s₀)) s₀.gpr compressSaved).readW (addr (esp₀ s₀) d) 32 =
      s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
  Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
    hp.arg_scr.sep (hp.arg_contains hd hd') (compressSaved_contains hp p h)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .ebp = scr s₀ ∧ s₁.gpr .esp = esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = saveMem s₀ ∧ s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  rw [prologue_eq]
  refine Wp.wp_ldm rfl (hp.in_arg (d := 16) (by omega) (by omega)) fun s₁ u₁ => ?_
  refine Spill.save_ok compressSaved (fun p h => by rw [u₁.gpr, u₁.wr]; exact hp.out_scr (by
    have := compressSaved_fits.1 p h; omega)) fun s₂ u₂ => ?_
  have hm : s₂.mem = Spill.saveMem s₀.mem (addr (scr s₀)) s₀.gpr compressSaved := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have hesp : s₂.gpr .esp = esp₀ s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have hrd : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  have hwr : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  have hebp : s₃.gpr .ebp = scr s₀ := by rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl
  refine Wp.wp_ldm (by rw [u₃.other _ (by decide), hesp])
    (by rw [u₃.rd, u₃.wr, hrd, hwr]; exact hp.in_arg (d := 8) (by omega) (by omega)) fun s₄ u₄ => ?_
  refine Wp.wp_stm (by rw [u₄.other _ (by decide), hebp])
    (by rw [u₄.wr, u₃.wr, hwr]; exact hp.out_scr (by omega)) fun s₅ u₅ => ?_
  refine Wp.wp_ldm (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hesp])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, hrd, hwr]; exact hp.in_arg (d := 12) (by omega) (by omega))
    fun s₆ u₆ => ?_
  refine Wp.wp_stm (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), hebp])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, hwr]; exact hp.out_scr (by omega)) fun s₇ u₇ => ?_
  have h12 : s₆.gpr .ecx = arg s₀ 2 := by
    rw [u₆.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, hm, readW_writeW_scr_arg hp _ _ (by omega) (by omega) (by omega),
      spill_arg hp (by omega) (by omega)]; rfl
  refine Wp.wp_test fun s₈ f₈ z₈ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), hebp]
  · rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      hesp]
  · rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hrd]
  · rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, hwr]
  · rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, hm, h12, spill_arg hp (by omega) (by omega)]
    rfl
  · rw [z₈, u₇.gpr, h12]

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) :=
  (Spill.saveMem_saved_addr _ _ compressSaved_fits (by have := hp.scr_fits; omega)).of_readW fun p h => by
    have := compressSaved_fits.1 p h
    rw [saveMem, readW_writeW_scr hp _ _ (by omega) (by omega) (by omega),
      readW_writeW_scr hp _ _ (by omega) (by omega) (by omega)]

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 112 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (hp.scr_eq (by omega))
  have m := List.mem_singleton_self (scrR s₀)
  exact ((Spill.saveMem_frame m _ _ _ _ (compressSaved_contains hp)).writeW
    m _ (c 80 (by omega))).writeW m _ (c 84 (by omega))

theorem linv_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hebp : s₁.gpr .ebp = scr s₀)
    (hesp : s₁.gpr .esp = esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = saveMem s₀) : LInv s₀ 0 s₁ := by
  have hrw := readW_writeW_scr hp
  refine ⟨⟨hebp, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩, ?_, ?_⟩
  · rw [hm]; exact (saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame hp).readW (contains_sub (len := 20) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl
  · rw [hm]; simp only [saveMem, bpOff]
    simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hrw]
    simp [blkAddr]
  · rw [hm]; simp only [saveMem, nOff]
    simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32]
    simp [nb]

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [epilogue_eq]
  refine Spill.restoreBase_ok _ (by decide)
    (fun p h => by rw [hc.ebp, hc.rd, hc.wr]; exact hp.in_scr (by have := compressSaved_fits.1 p h; omega))
    (by rw [hc.ebp]; exact hc.saved) fun s' u => WP.block_nil ⟨u.abi (by decide) (by decide) hc.esp, u.mem⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha1.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hL₀ := linv_zero hp hebp hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀.toCommon)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem sat_pre : Proof.Sha1.compressX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0 := by decide
  have a3 : arg satState 3 = 0x3000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha1.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [20, 112], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha1.compressX86.pre s₁)
    (h₂ : Proof.Sha1.compressX86.pre s₂) (hpub : Proof.Sha1.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sha1.X86.compress Proof.Sha1.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sha1.X86
