import VerifiedGarbage.Proof.Blake2.Arm.RoundsB

/-!
# BLAKE2b on ARMv7: one block

Untrusted: everything here is checked by Lean. Initializing the work vector
in `scratch` (`init_ok`), XORing it into the state (`fin_ok`), and advancing
the counter, the block pointer and the count (`advance_ok`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi ld st add64 const64)
open VG.Impl.Blake2.Arm.B (xor64 ldH ldIV finH tweak ctrLo ctrHi flagOff zeroOff)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A A_eq Reg64 Wrote wp_ld wp_st wp_const64
  rd64_write64_self rd64_write64_ne rd64_write64_disj frame_write64 rd64_frame lo_append hi_append
  hi_append_lo eq_of_lo_hi)
open VG.Spec.Blake2 (Work Block HashValue Params)

/-! ## The work vector of `F` -/

section InitV
variable {w : Nat} (P : Params w)

/-- The work vector at the start of the rounds of `F` (RFC 7693 §3.2). -/
def initV (h : HashValue w) (t : Nat) (f : Bool) : Work w :=
  let v : Work w := h ++ P.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat w t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat w (t / 2 ^ w))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes w) else v

theorem F_eq (h : HashValue w) (m : Block w) (t : Nat) (f : Bool) :
    Spec.Blake2.F P h m t f =
      Vector.ofFn fun i => h[i] ^^^ ((List.range P.r).foldl (Spec.Blake2.round P m) (initV P h t f))[i] ^^^
        ((List.range P.r).foldl (Spec.Blake2.round P m) (initV P h t f))[i.val + 8] := rfl

/-- The flag word. -/
def flagW (w : Nat) (f : Bool) : BitVec w := if f then BitVec.allOnes w else 0

/-- The word XORed into IV word `k` (`k < 8`): the counter's words and the flag word. -/
def tweakV (t : Nat) (f : Bool) (k : Nat) : BitVec w :=
  if k = 4 then BitVec.ofNat w t else if k = 5 then BitVec.ofNat w (t / 2 ^ w)
  else if k = 6 then flagW w f else 0

theorem initV_get (h : HashValue w) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) :
    (initV P h t f)[k] =
      if hk8 : k < 8 then h[k] else P.IV[k - 8] ^^^ tweakV t f (k - 8) := by
  unfold initV tweakV flagW
  have ha : ∀ j (hj : j < 16), (h ++ P.IV)[j] = if h8 : j < 8 then h[j] else P.IV[j - 8] :=
    fun j hj => Vector.getElem_append hj
  by_cases e12 : k = 12
  · subst e12; cases f <;> simp [ha]
  by_cases e13 : k = 13
  · subst e13; cases f <;> simp [ha]
  by_cases e14 : k = 14
  · subst e14; cases f <;> simp [ha]
  have e4 : k - 8 ≠ 4 := by omega
  have e5 : k - 8 ≠ 5 := by omega
  have e6 : k - 8 ≠ 6 := by omega
  cases f <;> simp [Ne.symm e12, Ne.symm e13, Ne.symm e14, e4, e5, e6, ha k hk]

end InitV

/-! ## Regions -/

/-- The state's region, the scratch region, and the work vector's part of it. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 64⟩
abbrev scrR (scr : BitVec 32) : Region := ⟨State.addr scr, 512⟩
abbrev workR (scr : BitVec 32) : Region := ⟨State.addr scr, 128⟩

/-- What a block needs of its state `s`, with `state = st` (in `r0`) and
`scratch = scr` (in `r3`). -/
structure Ctx (st scr : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  fitS : st.toNat + 64 ≤ 2 ^ 32
  fitV : scr.toNat + 512 ≤ 2 ^ 32
  disj : (stR st).Disjoint (scrR scr)
  wS : Reg64 s.wr st 64
  wV : Reg64 s.wr scr 512

theorem Ctx.of_eq {st scr : BitVec 32} {s s' : State} (c : Ctx st scr s) (h0 : s'.gpr .r0 = s.gpr .r0)
    (h3 : s'.gpr .r3 = s.gpr .r3) (hwr : s'.wr = s.wr) : Ctx st scr s' :=
  ⟨h0.trans c.r0, h3.trans c.r3, c.fitS, c.fitV, c.disj, hwr ▸ c.wS, hwr ▸ c.wV⟩

theorem Ctx.disjW {st scr : BitVec 32} {s : State} (c : Ctx st scr s) : (stR st).Disjoint (workR scr) :=
  c.disj.sub_right (Region.sub_prefix (by omega))

/-- A word of `scratch` above the work vector is unchanged by writes to it. -/
theorem rd64_frame_hi {m m' : Mem} {scr : BitVec 32} (fit : scr.toNat + 512 ≤ 2 ^ 32)
    (hf : Frame [workR scr] m m') {o : Nat} (h1 : 128 ≤ o) (h2 : o + 8 ≤ 512) :
    rd64 m' scr o = rd64 m scr o := by
  have hd : ∀ r ∈ [workR scr], Region.Disjoint ⟨State.addr scr + BitVec.ofNat 64 128, 384⟩ r := by
    simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ (by omega) (by omega)
  have c : ∀ d, 128 ≤ d → d + 4 ≤ 512 →
      Region.Contains ⟨State.addr scr + BitVec.ofNat 64 128, 384⟩ (A scr d) (32 / 8) := fun d h h' => by
    rw [A_eq (by omega)]; exact Offset.contains _ h (by omega) (by omega)
  simp only [rd64]
  rw [hf.readW (c o h1 (by omega)) hd (by decide), hf.readW (c (o + 4) (by omega) (by omega)) hd (by decide)]

/-! ## Initializing the work vector -/

structure LdInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, rd64 s'.mem scr (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [workR scr] s.mem s'.mem

theorem ldH_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap ldH)) s (LdInv st scr s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ldH, ← List.append_nil (Impl.Sha512.Arm.st .r4 .r5 .r3 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_st (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3]) p₂
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ u₃ => WP.block_nil ⟨fun r hr => ?_, by rw [u₃.rd, o₂.rd, h₁.rd],
        by rw [u₃.wr, o₂.wr, h₁.wr], by rw [u₃.sp, o₂.sp, h₁.sp], fun k hk => ?_, ?_⟩
    · rw [u₃.gpr, (o₂.mono (es := [Reg.r4, .r5, .r6, .r7]) (by decide)).gpr r hr, h₁.gpr r hr]
    · have fitV := c.fitV
      rw [u₃.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disjW) c.fitS (by omega)]
      · rw [rd64_write64_ne (b := scr) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega), o₂.mem]
        exact h₁.vars k (by omega)
    · rw [u₃.mem, o₂.mem]
      exact frame_write64 (N := 128) (o := 8 * n) h₁.frame (by simp) (by have := c.fitV; omega)
        (by omega) _

theorem tweak_ok (k : Nat) : 128 ≤ tweak k ∧ tweak k + 8 ≤ 512 := by
  unfold tweak ctrLo ctrHi flagOff zeroOff; split_ifs <;> omega

theorem iv_getD {k : Nat} (hk : k < 8) :
    Spec.Blake2.b.IV.toList.getD k 0 = Spec.Blake2.b.IV[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

structure IvInv (scr : BitVec 32) (T : Nat → BitVec 64) (s : State) (n : Nat) (s' : State) :
    Prop where
  gpr : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < 8, rd64 s'.mem scr (8 * k) = rd64 s.mem scr (8 * k)
  ivs : ∀ k, k < n → ∀ h8 : k < 8, rd64 s'.mem scr (64 + 8 * k) = Spec.Blake2.b.IV[k] ^^^ T k
  frame : Frame [workR scr] s.mem s'.mem

theorem ldIV_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) (T : Nat → BitVec 64)
    (hT : ∀ k < 8, rd64 s.mem scr (tweak k) = T k) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap ldIV)) s (IvInv scr T s n) := by
  intro n hn
  have fitV := c.fitV
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ h _ => absurd h (by omega), Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ldIV, ← List.append_nil (Impl.Sha512.Arm.st .r4 .r5 .r3 (64 + 8 * n))]
    have tw := tweak_ok n
    refine wp_const64 (by decide) fun s₂ o₂ p₂ => ?_
    refine wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3])
      (by rw [o₂.wr]; exact (c₁.wV _ tw.2).1) (by rw [o₂.wr]; exact (c₁.wV _ tw.2).2)
      fun s₃ o₃ p₃ => ?_
    refine wp_xor64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
      fun s₄ o₄ p₄ => ?_
    have O := (o₂.trans o₃).trans o₄
    refine wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r3]) p₄
      (by rw [O.wr]; exact (c₁.wV _ (by omega)).1) (by rw [O.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₅ u₅ => WP.block_nil ⟨fun r hr => ?_, by rw [u₅.rd, O.rd, h₁.rd],
        by rw [u₅.wr, O.wr, h₁.wr], by rw [u₅.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk h8 => ?_, ?_⟩
    · rw [u₅.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · rw [u₅.mem, rd64_write64_ne (b := scr) (o := 64 + 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega), O.mem]
      exact h₁.vars k hk
    · rw [u₅.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), o₂.mem,
          rd64_frame_hi fitV h₁.frame tw.1 tw.2, hT k (by omega), iv_getD (by omega)]
      · rw [rd64_write64_ne (b := scr) (o := 64 + 8 * n) (o' := 64 + 8 * k) _ _ (by omega)
          (by omega) (by omega), O.mem]
        exact h₁.ivs k (by omega) h8
    · rw [u₅.mem, O.mem]
      exact frame_write64 (N := 128) (o := 64 + 8 * n) h₁.frame (by simp) (by omega) (by omega) _

/-- `init` makes the work vector of `F` for the state `H` (at `st`) and the
tweaks `T` (in `scratch`). -/
theorem init_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) (T : Nat → BitVec 64)
    (hT : ∀ k < 8, rd64 s.mem scr (tweak k) = T k) :
    WP isa (.block Impl.Blake2.Arm.B.init) s fun s' =>
      (∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Frame [workR scr] s.mem s'.mem ∧
      ∀ k (hk : k < 16), rd64 s'.mem scr (8 * k) =
        if k < 8 then rd64 s.mem st (8 * k) else Spec.Blake2.b.IV[k - 8]'(by omega) ^^^ T (k - 8) := by
  unfold Impl.Blake2.Arm.B.init
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok c 8 (Nat.le_refl _)) fun s₁ h₁ => ?_
  have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
  have hT₁ : ∀ k < 8, rd64 s₁.mem scr (tweak k) = T k := fun k hk => by
    rw [rd64_frame_hi c.fitV h₁.frame (tweak_ok k).1 (tweak_ok k).2]; exact hT k hk
  refine WP.mono (ldIV_ok c₁ T hT₁ 8 (Nat.le_refl _)) fun s₂ h₂ => ?_
  refine ⟨fun r hr => by rw [h₂.gpr r hr, h₁.gpr r hr], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
    by rw [h₂.sp, h₁.sp], h₁.frame.trans h₂.frame, fun k hk => ?_⟩
  by_cases h8 : k < 8
  · simp only [h8, ↓reduceIte]; rw [h₂.vars k h8, h₁.vars k h8]
  · simp only [h8, ↓reduceIte]
    rw [show 8 * k = 64 + 8 * (k - 8) by omega, h₂.ivs (k - 8) (by omega) (by omega)]

/-! ## XORing the work vector into the state -/

structure UInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8, .r9] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  done : ∀ k < n, rd64 s'.mem st (8 * k) =
    rd64 s.mem st (8 * k) ^^^ rd64 s.mem scr (8 * k) ^^^ rd64 s.mem scr (64 + 8 * k)
  todo : ∀ k, n ≤ k → k < 8 → rd64 s'.mem st (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [stR st] s.mem s'.mem

theorem fin_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap finH)) s (UInv st scr s n) := by
  intro n hn
  have fitS := c.fitS
  have fitV := c.fitV
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [finH, ← List.append_nil (Impl.Sha512.Arm.st .r4 .r5 .r0 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3])
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ o₃ p₃ => ?_
    have O₃ := o₂.trans o₃
    refine wp_ld (by decide) (by decide) (by omega) (by rw [O₃.gpr _ (by decide), c₁.r3])
      (by rw [O₃.wr]; exact (c₁.wV _ (by omega)).1) (by rw [O₃.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₄ o₄ p₄ => ?_
    refine wp_xor64 (by decide) (by decide) (p₂.of_only (o₃.trans o₄) (by decide) (by decide))
      (p₃.of_only o₄ (by decide) (by decide)) fun s₅ o₅ p₅ => ?_
    refine wp_xor64 (by decide) (by decide) p₅ (p₄.of_only o₅ (by decide) (by decide))
      fun s₆ o₆ p₆ => ?_
    have O := ((O₃.trans o₄).trans o₅).trans o₆
    refine wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r0]) p₆
      (by rw [O.wr]; exact (c₁.wS _ (by omega)).1) (by rw [O.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₇ u₇ => WP.block_nil ⟨fun r hr => ?_, by rw [u₇.rd, O.rd, h₁.rd],
        by rw [u₇.wr, O.wr, h₁.wr], by rw [u₇.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [u₇.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · have hd : ∀ r ∈ [stR st], Region.Disjoint (scrR scr) r := fun r hr => by
        simp at hr; subst hr; exact c.disj.symm
      rw [u₇.mem, O.mem, o₃.mem, o₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), h₁.todo k (by omega) (by omega),
          rd64_frame h₁.frame hd fitV (by omega), rd64_frame h₁.frame hd fitV (by omega)]
      · rw [rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega)]
        exact h₁.done k (by omega)
    · rw [u₇.mem, rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega), O.mem]
      exact h₁.todo k (by omega) hk'
    · rw [u₇.mem, O.mem]
      exact frame_write64 (N := 64) (o := 8 * n) h₁.frame (by simp) fitS (by omega) _

end VG.Proof.Blake2.ArmB
