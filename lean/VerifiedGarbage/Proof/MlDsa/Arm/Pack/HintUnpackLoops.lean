import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpack

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_unpack`, the loops

Untrusted: everything here is checked by Lean. The loops of
`vg_mldsa_hint_bit_unpack`, as on x86-64: the coefficients of a polynomial
(`coefs_ok`), the polynomials (`main_ok`), each an iteration of the fold
`huPoly` of the spec, and the bytes after the last index (`trail_ok`), from
any state that permits reading `y` and writing `h` (`MainPre`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint.Unpack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.Arm.Pack.Hint

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .r1 = BitVec.ofNat 32 idx ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .r1 = 256

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- The coefficients after the first. -/
theorem nexts_ok {i bound first : Nat} (hi : i < uk s₀) (hbω : bound ≤ uω s₀) {hA₀ : Array (Vector Bool n)}
    {t : Nat} (ht1 : 1 ≤ t) {hA' : Array (Vector Bool n)} {idx' : Nat}
    (hF : optFold (huStep (uYs s₀) i first) (List.range t) (hA₀, first) = some (hA', idx'))
    (hidx : idx' = first + t) (hlt : idx' < bound) {s : State} (hP : PCom s₀ sA i bound s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx') (hh : HArr s₀ s.mem hA') :
    WP isa (.loop hbuNext .ne) s fun s' => PCom s₀ sA i bound s' ∧
      SIn s₀ bound (optFold (huStep (uYs s₀) i first) (List.range (bound - first)) (hA₀, first)) s' ∧
      KeepC s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧ 1 ≤ t ∧
      optFold (huStep (uYs s₀) i first) (List.range t) (hA₀, first) = some (hA', idx') ∧ idx' = first + t ∧
      idx' < bound ∧ PCom s₀ sA i bound s' ∧ s'.gpr .r1 = BitVec.ofNat 32 idx' ∧ HArr s₀ s'.mem hA' ∧
      KeepC s s')
    (fun m s' ⟨t, hA', idx', hm, ht1, hF, hidx, hlt, hP', h1', hh', hk'⟩ => ?_) _ s
    ⟨t, hA', idx', rfl, ht1, hF, hidx, hlt, hP, h1, hh, KeepC.refl _⟩
  refine WP.mono (next_ok hp hA hi (first := first) (by omega) hlt hbω hP' h1' hh') fun s'' ⟨hP'', hm'', hk''⟩ => ?_
  have hF1 : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA₀, first) =
      huStep (uYs s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
  cases hs : huStep (uYs s₀) i first (hA', idx') 0 with
  | none =>
    rw [hs] at hm''
    obtain ⟨r1'', z''⟩ := hm''
    refine .inl ⟨by show some (!s''.z) = some false; rw [z'']; rfl, hP'', ?_, hk'.trans hk''⟩
    have : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA₀, first) = none := by
      rw [hF1]; exact hs
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega) this]
    exact r1''
  | some st =>
    rw [hs] at hm''
    obtain ⟨hA'', idx''⟩ := st
    obtain ⟨r1'', hh'', z''⟩ := hm''
    have hi'' : idx'' = idx' + 1 := huStep_idx hs
    have hF2 : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA₀, first) = some (hA'', idx'') := by
      rw [hF1]; exact hs
    by_cases e : idx'' < bound
    · refine .inr ⟨by show some (!s''.z) = some true; rw [z'', decide_eq_false (by omega)]; rfl, bound - idx'',
        by omega, t + 1, hA'', idx'', rfl, by omega, hF2, by omega, e, hP'', r1'', hh'', hk'.trans hk''⟩
    · refine .inl ⟨by show some (!s''.z) = some false; rw [z'', decide_eq_true (by omega)]; rfl, hP'', ?_,
        hk'.trans hk''⟩
      rw [show bound - first = t + 1 by omega, hF2]
      exact ⟨by omega, r1'', hh''⟩

/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ uω s₀)
    {hA₀ : Array (Vector Bool n)} {s : State} (hP : PCom s₀ sA i bound s) (h1 : s.gpr .r1 = BitVec.ofNat 32 first)
    (hh : HArr s₀ s.mem hA₀) :
    WP isa hbuCoefs s fun s' => PCom s₀ sA i bound s' ∧
      SIn s₀ bound (optFold (huStep (uYs s₀) i first) (List.range (bound - first)) (hA₀, first)) s' ∧
      KeepC s s' := by
  obtain ⟨-, -, -, hω80, -, -⟩ := ufacts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (ltBit_ok .r7 .r1 .r4 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := keepC_r7 g₁ rd₁ wr₁ sp₁
  have hP₁ : PCom s₀ sA i bound s₁ := hP.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  have h1₁ : s₁.gpr .r1 = BitVec.ofNat 32 first := by rw [g₁ _ (by decide), h1]
  rw [h1, hP.r4, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
    toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)] at z₁
  refine WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
  · -- No coefficient.
    have hge : bound ≤ first := by rw [z₁] at hge; simpa using hge
    refine WP.block_nil ⟨hP₁, ?_, k₁⟩
    rw [show bound - first = 0 by omega]
    exact ⟨by omega, h1₁, by rw [m₁]; exact hh⟩
  · -- The first coefficient, then the others.
    have hlt : first < bound := by rw [z₁] at hlt; simpa using hlt
    have hF1 : optFold (huStep (uYs s₀) i first) (List.range 1) (hA₀, first) =
        some (huSet i ((uYs s₀).getD first 0).toNat hA₀, first + 1) := by
      simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ite_false]; rfl
    refine WP.seq (WP.mono (first_ok hp hA hi hlt hbω (hA' := hA₀) hP₁ h1₁ (by rw [m₁]; exact hh))
      fun s₂ ⟨hP₂, r1₂, hh₂, z₂, k₂⟩ => ?_)
    refine WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun hge₂ => ?_) (fun hlt₂ => ?_)
    · have hge₂ : bound ≤ first + 1 := by rw [z₂] at hge₂; simpa using hge₂
      refine WP.block_nil ⟨hP₂, ?_, k₁.trans k₂⟩
      rw [show bound - first = 1 by omega, hF1]
      exact ⟨by omega, r1₂, hh₂⟩
    · have hlt₂ : first + 1 < bound := by rw [z₂] at hlt₂; simpa using hlt₂
      exact WP.mono (nexts_ok hp hA hi hbω (Nat.le_refl 1) hF1 rfl hlt₂ hP₂ r1₂ hh₂) fun s₃ ⟨hP₃, hr₃, k₃⟩ =>
        ⟨hP₃, hr₃, (k₁.trans k₂).trans k₃⟩

end

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uYs s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`, in the loops that start from `sA`. -/
structure OInv (s₀ sA : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ sA s
  r5 : s.gpr .r5 = uY s₀ + BitVec.ofNat 32 (uω s₀ + i)
  r3 : s.gpr .r3 = uH s₀ + BitVec.ofNat 32 (1024 * i)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (1 * (uk s₀ - i))
  st : SRel s₀ (huS s₀ i) s

/-- A polynomial writes at most `r1`, `r4`, `r7` and `r12`. -/
def KeepP (s s' : State) : Prop :=
  (∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem KeepC.keepP {s s' : State} (h : KeepC s s') : KeepP s s' :=
  ⟨fun r a _ c d => h.1 r a c d, h.2⟩

theorem KeepP.trans {s s' s'' : State} (h : KeepP s s') (h' : KeepP s' s'') : KeepP s s'' :=
  ⟨fun r a b c d => (h'.1 r a b c d).trans (h.1 r a b c d), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem UCom.ofP {s₀ sA s s' : State} (h : UCom s₀ sA s) (hk : KeepP s s') (hm : Frame [uhR s₀] s.mem s'.mem) :
    UCom s₀ sA s' :=
  ⟨(hk.1 _ (by decide) (by decide) (by decide) (by decide)).trans h.r0,
    (hk.1 _ (by decide) (by decide) (by decide) (by decide)).trans h.r2,
    hk.2.1.trans h.rd, hk.2.2.1.trans h.wr, hk.2.2.2.trans h.sp, h.frame.trans hm⟩

theorem keepP_r4 {s s' : State} (h : ∀ r, r ≠ .r4 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : KeepP s s' := ⟨fun r _ b _ _ => h r b, hrd, hwr, hsp⟩

theorem keepP_r7 {s s' : State} (h : ∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : KeepP s s' := ⟨fun r _ _ c _ => h r c, hrd, hwr, hsp⟩

theorem ldrb4_blk {s : State} {p : BitVec 32} (h5 : s.gpr .r5 = p)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (p + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.ldrb .r4 .r5 0]) s fun s' =>
      s'.gpr .r4 = (s.mem (State.addr (p + BitVec.ofNat 32 0))).setWidth 32 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r4 → s'.gpr r = s.gpr r := by
  run_block [h5, ib, true_and]
  intro r hr; rw [ite_neg' hr]

theorem ptail_blk {s : State} :
    WP isa (.block [.dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1024), .subs .r6 .r6 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = s.gpr .r5 + 1 ∧ s'.gpr .r3 = s.gpr .r3 + 1024 ∧ s'.gpr .r6 = s.gpr .r6 - 1 ∧
      s'.z = (s.gpr .r6 - 1 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = s.gpr .r2 := by
  run_block []

section
variable {s₀ : State} (hp : UPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- Polynomial `i`: its checks and coefficients, unless a check failed. -/
theorem poly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ sA i s) :
    WP isa (.seq hbuPoly (.block [.dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1024), .subs .r6 .r6 (.imm 1)]))
      s fun s' => OInv s₀ sA (i + 1) s' ∧ s'.z = decide (i + 1 = uk s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  have fY := hp.fitY
  have hsucc : huS s₀ (i + 1) = (huS s₀ i).bind fun st => huPoly (uω s₀) (uYs s₀) st i := optFold_range_succ _ _ _
  -- After the polynomial, whichever way it went.
  suffices h : WP isa hbuPoly s fun s' => UCom s₀ sA s' ∧ KeepP s s' ∧ SRel s₀ (huS s₀ (i + 1)) s' by
    refine WP.seq (WP.mono h fun s₁ ⟨hc₁, k₁, st₁⟩ => ?_)
    refine WP.mono ptail_blk fun s₂ ⟨r5₂, r3₂, r6₂, z₂, m₂, rd₂, wr₂, sp₂, r0₂, r1₂, r2₂⟩ =>
      ⟨⟨⟨by rw [r0₂, hc₁.r0], by rw [r2₂, hc₁.r2], by rw [rd₂, hc₁.rd], by rw [wr₂, hc₁.wr], by rw [sp₂, hc₁.sp],
        by rw [m₂]; exact hc₁.frame⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [r5₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r5, BitVec.add_assoc, ofNat_succ32,
        Nat.add_assoc]
    · rw [r3₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r3, BitVec.add_assoc,
        show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.ofNat_add_ofNat, Nat.mul_succ]
    · rw [r6₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r6]; exact count_sub (k := 1) hi
    · revert st₁
      cases huS s₀ (i + 1) with
      | none => exact fun h => by simp only [SRel] at h ⊢; rw [r1₂, h]
      | some st => obtain ⟨hA', idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [r1₂, h1], h2, by rw [m₂]; exact h3⟩
    · rw [z₂, k₁.1 _ (by decide) (by decide) (by decide) (by decide), hI.r6]
      exact count_z (k := 1) hi (by decide) (by omega)
  unfold hbuPoly
  refine WP.seq (WP.mono (ltBit_ok .r7 .r2 .r1 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := keepP_r7 g₁ rd₁ wr₁ sp₁
  have hc₁ : UCom s₀ sA s₁ := hI.com.ofP k₁ (by rw [m₁]; exact Frame.refl _ _)
  have hst := hI.st
  cases hS : huS s₀ i with
  | none =>
    -- A check failed before: nothing.
    rw [hS] at hst
    have hst : s.gpr .r1 = 256 := hst
    rw [hI.com.r2, hst, ltBit_z (by omega) (by decide), show (256 : BitVec 32).toNat = 256 from rfl] at z₁
    refine WP.ite (M := isa) false (by show some s₁.z = _; rw [z₁, decide_eq_false (by omega)]) (fun h => by cases h)
      fun _ => WP.block_nil ⟨hc₁, k₁, ?_⟩
    rw [hsucc, hS]
    show s₁.gpr .r1 = 256
    rw [g₁ _ (by decide), hst]
  | some st =>
    obtain ⟨hA', idx⟩ := st
    rw [hS] at hst
    obtain ⟨h1, hidx, hh⟩ := hst
    rw [hI.com.r2, h1, ltBit_z (by omega) (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega)] at z₁
    have h1₁ : s₁.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₁ _ (by decide), h1]
    refine WP.ite (M := isa) true (by show some s₁.z = _; rw [z₁, decide_eq_true hidx]) (fun _ => ?_)
      (fun h => by cases h)
    -- The bound.
    have ebd : State.addr (uY s₀ + BitVec.ofNat 32 (uω s₀ + i) + BitVec.ofNat 32 0) =
        State.addr (uY s₀) + BitVec.ofNat 64 (uω s₀ + i) := by
      rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    rw [WP.seq_iff, WP.block_append_iff]
    refine WP.mono (ldrb4_blk (p := uY s₀ + BitVec.ofNat 32 (uω s₀ + i)) (by rw [g₁ _ (by decide), hI.r5]) (by
        rw [ebd, hc₁.rd, hc₁.wr]
        exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨r4₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
    rw [ebd, yByte hp hA hc₁ (by omega)] at r4₂
    have k₂ := keepP_r4 g₂ rd₂ wr₂ sp₂
    have hc₂ : UCom s₀ sA s₂ := hc₁.ofP k₂ (by rw [m₂]; exact Frame.refl _ _)
    have hbl := ((uYs s₀).getD (uω s₀ + i) 0).isLt
    refine WP.mono (ltBit_ok .r7 .r4 .r1 s₂) fun s₃ ⟨_, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ?_
    have k₃ := keepP_r7 g₃ rd₃ wr₃ sp₃
    have hc₃ : UCom s₀ sA s₃ := hc₂.ofP k₃ (by rw [m₃]; exact Frame.refl _ _)
    rw [r4₂, g₂ _ (by decide), h1₁, ltBit_z (by rw [byte_toNat32]; omega) (by rw [toNat_ofNat32 (by omega)]; omega),
      byte_toNat32, toNat_ofNat32 (by omega)] at z₃
    have hpoly := hsucc
    rw [hS] at hpoly
    simp only [Option.bind_some, huPoly] at hpoly
    have r4₃ : s₃.gpr .r4 = BitVec.ofNat 32 ((uYs s₀).getD (uω s₀ + i) 0).toNat := by
      rw [g₃ _ (by decide), r4₂]; apply BitVec.eq_of_toNat_eq; rw [byte_toNat32, toNat_ofNat32 (by omega)]
    have h1₃ : s₃.gpr .r1 = BitVec.ofNat 32 idx := by rw [g₃ _ (by decide), g₂ _ (by decide), h1₁]
    refine WP.ite (M := isa) _ (show some s₃.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
    · have hge : idx ≤ ((uYs s₀).getD (uω s₀ + i) 0).toNat := by rw [z₃] at hge; simpa using hge
      refine WP.seq (WP.mono (ltBit_ok .r7 .r2 .r4 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_)
      have k₄ := keepP_r7 g₄ rd₄ wr₄ sp₄
      have hc₄ : UCom s₀ sA s₄ := hc₃.ofP k₄ (by rw [m₄]; exact Frame.refl _ _)
      rw [hc₃.r2, r4₃, ltBit_z (by omega) (by rw [toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega)] at z₄
      refine WP.ite (M := isa) _ (show some s₄.z = _ from rfl) (fun hle => ?_) (fun hgt => ?_)
      · -- The coefficients.
        have hle : ((uYs s₀).getD (uω s₀ + i) 0).toNat ≤ uω s₀ := by rw [z₄] at hle; simpa using hle
        have hP₄ : PCom s₀ sA i ((uYs s₀).getD (uω s₀ + i) 0).toNat s₄ :=
          ⟨hc₄, by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hI.r3],
            by rw [g₄ _ (by decide), r4₃]⟩
        refine WP.mono (coefs_ok hp hA hi (first := idx) (hA₀ := hA') hge hle hP₄
          (by rw [g₄ _ (by decide), h1₃]) (by rw [m₄, m₃, m₂, m₁]; exact hh)) fun s₅ ⟨hP₅, hin₅, k₅⟩ =>
            ⟨hP₅.com, (((k₁.trans k₂).trans k₃).trans k₄).trans k₅.keepP, ?_⟩
        rw [hpoly, ite_neg' (by omega)]
        revert hin₅
        cases optFold (huStep (uYs s₀) i idx) (List.range (((uYs s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA', idx) with
        | none => exact id
        | some st => obtain ⟨hA'', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega, h3⟩
      · -- `bound > ω`: fail.
        have hgt : uω s₀ < ((uYs s₀).getD (uω s₀ + i) 0).toNat := by rw [z₄] at hgt; simpa using hgt
        refine WP.mono fail_ok fun s₅ ⟨r1₅, m₅, k₅⟩ => ⟨hc₄.of k₅ (by rw [m₅]; exact Frame.refl _ _),
          (((k₁.trans k₂).trans k₃).trans k₄).trans k₅.keepP, ?_⟩
        rw [hpoly, ite_pos' (.inr hgt)]; exact r1₅
    · -- `bound < index`: fail.
      have hlt : ((uYs s₀).getD (uω s₀ + i) 0).toNat < idx := by rw [z₃] at hlt; simpa using hlt
      refine WP.mono fail_ok fun s₄ ⟨r1₄, m₄, k₄⟩ => ⟨hc₃.of k₄ (by rw [m₄]; exact Frame.refl _ _),
        ((k₁.trans k₂).trans k₃).trans k₄.keepP, ?_⟩
      rw [hpoly, ite_pos' (.inl hlt)]; exact r1₄

omit hp hA in
theorem mainPro_blk {s : State} :
    WP isa (.block [.dp .add .r5 .r0 (.reg .r2)]) s fun s' => s'.gpr .r5 = s.gpr .r0 + s.gpr .r2 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r5 → s'.gpr r = s.gpr r := by
  run_block [true_and]
  intro r hr; rw [ite_neg' hr]

/-- The polynomials, from the state after zeroing `h`. -/
theorem main_ok (h0 : sA.gpr .r0 = uY s₀) (h1 : sA.gpr .r1 = 0) (h2 : sA.gpr .r2 = uW s₀)
    (h3 : sA.gpr .r3 = uH s₀) (h6 : sA.gpr .r6 = BitVec.ofNat 32 (uk s₀))
    (hz : ∀ t < 256 * uk s₀, coeffAt sA.mem (State.addr (uH s₀)) t = 0) :
    WP isa hbuMain sA fun s' => UCom s₀ sA s' ∧ SRel s₀ (huS s₀ (uk s₀)) s' := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuMain
  refine WP.seq (WP.mono mainPro_blk fun s₁ ⟨r5₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  refine wp_loop_ne (OInv s₀ sA) (N := uk s₀) (by omega) (fun i hi s h => poly_ok hp hA hi h)
    (fun s hI => ⟨hI.com, hI.st⟩)
    ⟨⟨by rw [g₁ _ (by decide), h0], by rw [g₁ _ (by decide), h2], rd₁, wr₁, sp₁, by rw [m₁]; exact Frame.refl _ _⟩,
      by rw [r5₁, h0, h2, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [g₁ _ (by decide), h3]; simp, by rw [g₁ _ (by decide), h6, Nat.one_mul, Nat.sub_zero], ?_⟩
  show SRel s₀ (some (Array.replicate (uk s₀) noHint, 0)) s₁
  exact ⟨by rw [g₁ _ (by decide), h1]; rfl, Nat.zero_le _, by rw [m₁]; exact harr_zero hz⟩

/-! ## The bytes after the last index -/

omit hp hA in
theorem tload_blk {s : State} {y i : BitVec 32} (h0 : s.gpr .r0 = y) (h1 : s.gpr .r1 = i)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + i + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r12 .r0 (.reg .r1), .ldrb .r12 .r12 0, .cmp .r12 (.imm 0)]) s fun s' =>
      s'.z = ((s.mem (State.addr (y + i + BitVec.ofNat 32 0))).setWidth 32 - 0 == 0) ∧ s'.mem = s.mem ∧
      s'.gpr .r1 = i ∧ KeepC s s' := by
  run_block [KeepC, h0, h1, ib, true_and, and_true]
  intro r _ _ c; rw [ite_neg' c, ite_neg' c]

omit hp hA in
theorem inc_blk {s : State} :
    WP isa (.block [.dp .add .r1 .r1 (.imm 1)]) s fun s' => s'.gpr .r1 = s.gpr .r1 + 1 ∧ s'.mem = s.mem ∧
      KeepC s s' := by
  run_block [KeepC, true_and, and_true]
  intro r a _ _; rw [ite_neg' a]

omit hp hA in
theorem byte_z (b : Byte) : ((b.setWidth 32 : BitVec 32) - 0 == 0) = decide (b = 0) := by
  rw [sub_zero32]
  by_cases h : b = 0
  · subst h; rfl
  · rw [decide_eq_false h]
    apply beq_eq_false_iff_ne.mpr
    intro e; apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    rw [byte_toNat32] at this
    exact this

/-- The bytes from the index `idx` up to `ω`. -/
theorem trail_ok {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ sA s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ sA s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
        | some _ => s'.gpr .r1 = BitVec.ofNat 32 (uω s₀)
        | none => s'.gpr .r1 = 256) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  have fY := hp.fitY
  unfold hbuTrail
  refine WP.seq (WP.mono (ltBit_ok .r7 .r1 .r2 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := keepC_r7 g₁ rd₁ wr₁ sp₁
  have hc₁ : UCom s₀ sA s₁ := hc.of k₁ (by rw [m₁]; exact Frame.refl _ _)
  rw [h1, hc.r2, ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by omega), toNat_ofNat32 (by omega)] at z₁
  refine WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun hge => ?_) (fun hlt => ?_)
  · have hge : uω s₀ ≤ idx := by rw [z₁] at hge; simpa using hge
    refine WP.block_nil ⟨hc₁, m₁, ?_⟩
    rw [show uω s₀ - idx = 0 by omega]
    show s₁.gpr .r1 = _
    rw [g₁ _ (by decide), h1, show idx = uω s₀ by omega]
  · have hlt : idx < uω s₀ := by rw [z₁] at hlt; simpa using hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
        optFold (huTrail (uYs s₀)) (List.range' idx u) () = some () ∧ s'.gpr .r1 = BitVec.ofNat 32 (idx + u) ∧
        UCom s₀ sA s' ∧ s'.mem = s.mem)
      (fun m s' ⟨u, hm, hu, hF, h1', hc', hm'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega, rfl, by rw [g₁ _ (by decide), h1]; rfl, hc₁, m₁⟩
    have eb : State.addr (uY s₀ + BitVec.ofNat 32 (idx + u) + BitVec.ofNat 32 0) =
        State.addr (uY s₀) + BitVec.ofNat 64 (idx + u) := by
      rw [addr_ptr _ _ _ (by omega), Nat.add_zero]
    refine WP.seq (WP.mono (tload_blk hc'.r0 h1' (by
        rw [eb, hc'.rd, hc'.wr]
        exact ⟨_, List.mem_append_left _ hA.rd, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨z₂, m₂, r1₂, k₂⟩ => ?_)
    rw [eb, yByte hp hA hc' (by omega), byte_z] at z₂
    have hc₂ : UCom s₀ sA s₂ := hc'.of k₂ (by rw [m₂]; exact Frame.refl _ _)
    have hF1 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = huTrail (uYs s₀) () (idx + u) := by
      rw [optFold_range'_succ, hF]; rfl
    refine WP.seq (WP.ite (M := isa) _ (show some s₂.z = _ from rfl) (fun heq => ?_) (fun hne => ?_))
    · -- A zero byte: next.
      have heq : (uYs s₀).getD (idx + u) 0 = 0 := by rw [z₂] at heq; simpa using heq
      have hF2 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' (by simpa using heq)]
      refine WP.mono inc_blk fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
      have r1₃' : s₃.gpr .r1 = BitVec.ofNat 32 (idx + (u + 1)) := by rw [r1₃, r1₂, ofNat_succ32, Nat.add_assoc]
      refine WP.mono (ltBit_ok .r7 .r1 .r2 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
      have k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
      have hc₄ : UCom s₀ sA s₄ := (hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).of k₄ (by rw [m₄]; exact Frame.refl _ _)
      rw [r1₃', (hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)).r2,
        ltBit_z (by rw [toNat_ofNat32 (by omega)]; omega) (by omega), toNat_ofNat32 (by omega)] at z₄
      have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (idx + (u + 1)) := by rw [g₄ _ (by decide), r1₃']
      by_cases e : idx + (u + 1) < uω s₀
      · exact .inr ⟨by show some (!s₄.z) = some true; rw [z₄, decide_eq_false (by omega)]; rfl, _, by omega, u + 1,
          rfl, e, hF2, r1₄, hc₄, by rw [m₄, m₃, m₂, hm']⟩
      · refine .inl ⟨by show some (!s₄.z) = some false; rw [z₄, decide_eq_true (by omega)]; rfl, hc₄,
          by rw [m₄, m₃, m₂, hm'], ?_⟩
        rw [show uω s₀ - idx = u + 1 by omega, hF2]
        show s₄.gpr .r1 = _
        rw [r1₄, show idx + (u + 1) = uω s₀ by omega]
    · -- A nonzero byte: fail.
      have hne : (uYs s₀).getD (idx + u) 0 ≠ 0 := by rw [z₂] at hne; simpa using hne
      have hn : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono fail_ok fun s₃ ⟨r1₃, m₃, k₃⟩ => ?_
      refine WP.mono (ltBit_ok .r7 .r1 .r2 s₃) fun s₄ ⟨_, z₄, m₄, rd₄, wr₄, sp₄, g₄⟩ => ?_
      have k₄ := keepC_r7 g₄ rd₄ wr₄ sp₄
      have hc₃ : UCom s₀ sA s₃ := hc₂.of k₃ (by rw [m₃]; exact Frame.refl _ _)
      rw [r1₃, hc₃.r2, ltBit_z (by decide) (by omega), show (256 : BitVec 32).toNat = 256 from rfl] at z₄
      refine .inl ⟨by show some (!s₄.z) = some false; rw [z₄, decide_eq_true (by omega)]; rfl,
        hc₃.of k₄ (by rw [m₄]; exact Frame.refl _ _), by rw [m₄, m₃, m₂, hm'], ?_⟩
      rw [hn]
      show s₄.gpr .r1 = 256
      rw [g₄ _ (by decide), r1₃]

omit hA in
/-- After a failed check, the bytes after the last index are not checked. -/
theorem trail_fail {s : State} (hc : UCom s₀ sA s) (h1 : s.gpr .r1 = 256) :
    WP isa hbuTrail s fun s' => UCom s₀ sA s' ∧ s'.mem = s.mem ∧ s'.gpr .r1 = 256 := by
  obtain ⟨-, -, -, hω80, -, -⟩ := ufacts hp
  have eω : (uW s₀).toNat = uω s₀ := rfl
  unfold hbuTrail
  refine WP.seq (WP.mono (ltBit_ok .r7 .r1 .r2 s) fun s₁ ⟨_, z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  have k₁ := keepC_r7 g₁ rd₁ wr₁ sp₁
  rw [h1, hc.r2, ltBit_z (by decide) (by omega), show (256 : BitVec 32).toNat = 256 from rfl] at z₁
  refine WP.ite (M := isa) true (by show some s₁.z = _; rw [z₁, decide_eq_true (by omega)]) (fun _ => ?_)
    (fun h => by cases h)
  exact WP.block_nil ⟨hc.of k₁ (by rw [m₁]; exact Frame.refl _ _), m₁, by rw [g₁ _ (by decide), h1]⟩

end

end VG.Proof.MlDsa.Arm.Pack.Hint.Unpack
