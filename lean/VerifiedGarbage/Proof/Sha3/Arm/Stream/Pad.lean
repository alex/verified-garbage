import VerifiedGarbage.Proof.Sha3.Arm.Permute
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on ARMv7: `pad`

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Sha3.AArch64.Stream.Pad`), with the return address
saved in the scratch space instead of a frame.
-/

namespace VG.Proof.Sha3.Arm.Stream.Pad

open VG VG.Arm VG.Impl.Sha3.Arm.Stream
open VG.Proof.Sha3.Arm (call_ok covers_of readW_hi xor_setWidth32' ofNat_toNat32 argByte_eq
  addr_toNat)
open VG.Proof.Sha512.Arm (A contains_A)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_sub wp_ldr wp_str wp_ldrb
  wp_strb wp_ldrSp)
open VG.Proof.Sha512.Arm (wp_eor)
open VG.Proof.Sha3 (Rep xorByte stateAt_xorByte stateAt_congr writeW8_apply contains_offset ne_of_lt200
  absorb_pad)
open VG.Spec.Sha3 (stateAt keccakF rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev rt : Nat := (s₀.gpr .r1).toNat
abbrev pos : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev stA : Addr := State.addr (st s₀)
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 640⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  st_fit : (s₀.gpr .r0).toNat + 200 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.padArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## Correctness -/

/-- The postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.padArm.post s₀ s'

theorem x80 : ((0x80 : BitVec 32).setWidth 8) = (0x80 : BitVec 8) := by decide

theorem keep_ne : ∀ r ∈ preserved, r ≠ .r12 ∧ r ≠ .r2 ∧ r ≠ .r1 := by decide

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa pad s₀ (Post s₀) := by
  have ⟨hr₀, hr₁⟩ := Proof.Sha3.rate_bounds hp.rate
  have hr₀' : 72 ≤ (s₀.gpr .r1).toNat := hr₀
  have hr₁' : (s₀.gpr .r1).toNat ≤ 168 := hr₁
  have hpl : (s₀.gpr .r2).toNat < (s₀.gpr .r1).toNat := hp.pos_lt
  have fS := hp.st_fit
  have fC := hp.scr_fit
  have hin : ∀ rs : List Region, stR s₀ ∈ rs → ∀ j < 200,
      InRegions rs (stA s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h j hj => ⟨stR s₀, h, contains_offset (by omega) (by omega)⟩
  have hlr : ∀ rs : List Region, scR s₀ ∈ rs → InRegions rs (A (scr s₀) 512) 4 :=
    fun rs h => ⟨scR s₀, h, contains_A fC (by omega)⟩
  have hp1 : pos s₀ < 200 := show (s₀.gpr .r2).toNat < 200 by omega
  have hq : rt s₀ - 1 < 200 := show (s₀.gpr .r1).toNat - 1 < 200 by omega
  unfold pad
  refine WP.seq ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    ⟨argR s₀, by simp [hp.rd], Region.contains_self _ _⟩ fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine wp_str (a := A (scr s₀) 512) (by decide) (by rw [h12])
    (hlr _ (by simp [u₁.wr, hp.wr])) fun s₂ m₂ => ?_
  have hm₂ : s₂.mem = s₀.mem.writeW (A (scr s₀) 512) (s₀.gpr .lr) := by
    rw [m₂.mem, u₁.mem, u₁.other .lr (by decide)]
  have hf₂ : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_A fC (by omega))
  have k₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [m₂.gpr, u₁.other r h]
  -- The suffix.
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have e₁ : State.addr (s₃.gpr .r2 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 (pos s₀) := by
    rw [u₃.gpr, k₂ .r0 (by decide), k₂ .r2 (by decide), BitVec.add_zero]
    have := addr_add (a := s₀.gpr .r0) (k := pos s₀) (by omega)
    rwa [ofNat_toNat32] at this
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 (pos s₀)) (by decide) e₁
    (hin _ (by simp [u₃.rd, u₃.wr, m₂.rd, m₂.wr, u₁.rd, u₁.wr, hp.rd, hp.wr]) _ hp1) fun s₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_strb (a := stA s₀ + BitVec.ofNat 64 (pos s₀)) (by decide)
    (by rw [u₅.other .r2 (by decide), u₄.other .r2 (by decide)]; exact e₁)
    (hin _ (by simp [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, hp.wr]) _ hp1) fun s₆ g₆ => ?_
  have hb₁ : s₆.mem = s₂.mem.writeW (stA s₀ + BitVec.ofNat 64 (pos s₀))
      (s₂.mem (stA s₀ + BitVec.ofNat 64 (pos s₀)) ^^^ (s₀.gpr .r3).setWidth 8) := by
    rw [g₆.mem, u₅.gpr, u₄.gpr, u₄.other .r3 (by decide), u₃.other .r3 (by decide), k₂ .r3 (by decide),
      xor_setWidth32', u₅.mem, u₄.mem, u₃.mem]
  have k₆ : ∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .lr → s₆.gpr r = s₀.gpr r := fun r h12 h2 hl => by
    rw [g₆.gpr, u₅.other r hl, u₄.other r hl, u₃.other r h2, k₂ r h12]
  -- The final bit.
  refine wp_add (op2_reg _ _) fun s₇ u₇ => wp_sub (op2_imm (by decide)) fun s₈ u₈ => ?_
  have e₂ : State.addr (s₈.gpr .r2 + BitVec.ofNat 32 0) = stA s₀ + BitVec.ofNat 64 (rt s₀ - 1) := by
    rw [u₈.gpr, u₇.gpr, k₆ .r0 (by decide) (by decide) (by decide),
      k₆ .r1 (by decide) (by decide) (by decide), BitVec.add_zero,
      show s₀.gpr .r0 + s₀.gpr .r1 - 1 = s₀.gpr .r0 + BitVec.ofNat 32 ((s₀.gpr .r1).toNat - 1) by
        exact Offset.add_sub_one32 _ _ (by omega)]
    exact addr_add (by omega)
  refine wp_ldrb (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) (by decide) e₂
    (hin _ (by simp [u₈.rd, u₈.wr, u₇.rd, u₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd,
      u₃.wr, m₂.rd, m₂.wr, u₁.rd, u₁.wr, hp.rd, hp.wr]) _ hq) fun s₉ u₉ => ?_
  refine wp_eor (op2_imm (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_strb (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) (by decide)
    (by rw [u₁₀.other .r2 (by decide), u₉.other .r2 (by decide)]; exact e₂)
    (hin _ (by simp [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, hp.wr]) _ hq)
    fun s₁₁ g₁₁ => ?_
  have hb₂ : s₁₁.mem = s₆.mem.writeW (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1))
      (s₆.mem (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) ^^^ 0x80) := by
    rw [g₁₁.mem, u₁₀.gpr, u₉.gpr, xor_setWidth32', x80, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  refine wp_mov (op2_reg _ _) fun s₁₂ u₁₂ => WP.block_nil ?_
  -- The state and the frame.
  have hS₂ : stateAt s₂.mem (stA s₀) = stateAt s₀.mem (stA s₀) :=
    stateAt_congr fun i hi => hf₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  have hS : stateAt s₁₂.mem (stA s₀) = xorByte (xorByte (stateAt s₀.mem (stA s₀)) (pos s₀)
      ((s₀.gpr .r3).setWidth 8)) (rt s₀ - 1) 0x80 := by
    rw [u₁₂.mem, ← hS₂, ← stateAt_xorByte (m := s₂.mem) (m' := s₆.mem) hp1
      (by rw [hb₁, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [hb₁, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi hp1 hne))])]
    exact stateAt_xorByte hq (by rw [hb₂, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [hb₂, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi hq hne))])
  have hf₆ : Frame [stR s₀] s₂.mem s₆.mem := by
    rw [hb₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have hf₁₂ : Frame [stR s₀] s₂.mem s₁₂.mem := by
    rw [u₁₂.mem, hb₂]
    exact hf₆.writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  have k₁₂ : ∀ r, r ≠ .r12 → r ≠ .r2 → r ≠ .lr → r ≠ .r1 → s₁₂.gpr r = s₀.gpr r :=
    fun r h12 h2 hl h1 => by
      rw [u₁₂.other r h1, g₁₁.gpr, u₁₀.other r hl, u₉.other r hl, u₈.other r h2, u₇.other r h2,
        k₆ r h12 h2 hl]
  have r1₁₂ : s₁₂.gpr .r1 = scr s₀ := by
    rw [u₁₂.gpr, g₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), g₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), m₂.gpr, h12]
  have rd₁₂ : s₁₂.rd = s₀.rd := by
    rw [u₁₂.rd, g₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd]
  have wr₁₂ : s₁₂.wr = s₀.wr := by
    rw [u₁₂.wr, g₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]
  -- The call, and the return address.
  refine WP.seq (call_ok (st := st s₀) (scr := scr s₀)
    (k₁₂ .r0 (by decide) (by decide) (by decide) (by decide)) r1₁₂ fS (by omega)
    (hp.st_scr.sub_right (Region.sub_prefix (by omega)))
    (by rw [wr₁₂, hp.wr]; exact covers_of (N := 640) (by omega) (by simp) (by simp))
    fun s' rd' wr' _ cs' _ r1' f' e' => ?_)
  refine wp_ldr (a := A (scr s₀) 512) (by decide) (by rw [r1'])
    (hlr _ (by simp [rd', wr', rd₁₂, wr₁₂, hp.rd, hp.wr])) fun s'' u'' => WP.block_nil ?_
  refine ⟨fun r hr => ?_, fun msg hR hm => ?_⟩
  · by_cases hl : r = .lr
    · subst hl
      rw [u''.gpr, readW_hi fC hp.st_scr f' (fun r hr => by simpa using hr) (d := 512) (Nat.le_refl _)
        (by omega), readW_hi fC hp.st_scr hf₁₂ (fun r hr => .inl (List.mem_singleton.mp hr))
        (d := 512) (Nat.le_refl _) (by omega), hm₂, Mem.readW_writeW_self32]
    · have ne := keep_ne r hr
      rw [u''.other r hl, cs' r hr hl, k₁₂ r ne.1 ne.2.1 hl ne.2.2]
  · rw [u''.mem, e', hS, Proof.Sha3.repr_iff.mp hR, absorb_pad (by omega) (by omega), ← hm]

/-! ## Constant time -/

/-- The initial taint: the register arguments are public, `r0` points at the
state, and the stack argument is public and points at the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [200, 640], bases := [(.r0, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : Proof.Sha3.padArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_,
    fun _ => ⟨hp.sp_fit, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.padArm.pre s₁) (h₂ : Proof.Sha3.padArm.pre s₂)
    (hpub : Proof.Sha3.padArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stA, scr, st, p0, a0]
  · simp only [τ₀] at hk
    rw [argByte_eq hp₁.sp_fit hk, argByte_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega)),
      show k / 4 = 0 by omega]
    exact congrArg _ a0

/-- A state satisfying the precondition (with the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 72 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x4000, 4⟩]
  wr := [⟨0x1000, 200⟩, ⟨0, 640⟩]

theorem pad_verified : Verified Arm.target pad Proof.Sha3.padArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide_weak VG.Proof.Sha3.Arm.dropRC)
  · have e : ∀ k, stackArg sat k = 0 := fun k => by
      simp [stackArg, sat, Mem.readW, Mem.read]
    refine ⟨sat, ?_⟩
    simp only [Proof.Sha3.padArm, e]
    refine ⟨by simp [sat, stackArgAddr]; decide, rfl, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide⟩ <;>
    · exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.Arm.Stream.Pad
