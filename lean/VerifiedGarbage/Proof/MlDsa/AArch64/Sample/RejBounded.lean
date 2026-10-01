import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_bounded_poly`, correctness

Untrusted: everything here is checked by Lean. The function runs in pieces:
the prologue, the sponge (544 bytes of SHAKE256 of the seed), the branch on
`η` to its loop, and the end. Iteration `t` of the loop starts from `LAt t`,
with the coefficients `rbFold` samples from the first `t` bytes of output
stored; it loads byte `t` (`LB`), tries its low half-byte if `j < 256`
(`LM`), and then its high half-byte if still `j < 256`. The pieces are
separate lemmas, which the proof of constant time (`RejBoundedCT.lean`)
uses too.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_mov wp_movz wp_subImm wp_addImm wp_ldrb wp_and wp_lsr
  wp_lsl ptr_add ptr_zero toNat_lsr toNat_sub_n toNat_byte eval_zero eq_zero_iff count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejBounded (Consts try_ok)
open VG.Spec.MlDsa (Zq q H PolyIs coeffAt rejBoundedLeak n)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the `u32` argument in `w1`. -/
abbrev etaOf (s : State) : Nat := ((s.gpr .x1).setWidth 32).toNat

/-- `vg_mldsa_rej_bounded_poly(seed = x0, eta = w1, a = x2, scratch = x3) -> w0`,
with 16 bytes of stack below `sp`. -/
def rbK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 66⟩
    let a : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch ∧ (etaOf s = 2 ∨ etaOf s = 4)
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544)).length = 256 then 1 else 0) ∧
      ((rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544)).length = 256 →
        PolyIs s'.mem (s.gpr .x2) (toPoly (rbFold (etaOf s) [] (H (bytesAt s.mem (s.gpr .x0) 66) 544))))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
    rejBoundedLeak (etaOf s₁) (bytesAt s₁.mem (s₁.gpr .x0) 66) =
      rejBoundedLeak (etaOf s₂) (bytesAt s₂.mem (s₂.gpr .x0) 66)

namespace RejBounded

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, 66, σ.gpr .x3, σ.gpr .x2, ((σ.gpr .x1).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((spOf σ).msg σ) 544

theorem X_length (σ : State) : (X σ).length = 544 := H_length _ _

/-- The coefficients sampled from the first `t` bytes. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rbFold (etaOf σ) [] ((X σ).take t)

/-- Byte `t` of the output. -/
abbrev Z (σ : State) (t : Nat) : Byte := (X σ).getD t 0

/-- After the low half-byte of byte `t`. -/
abbrev Lm (σ : State) (t : Nat) : List Zq := hbTry (etaOf σ) (Lt σ t) ((Z σ t).toNat % 16)

theorem Lt_le (σ : State) (t : Nat) : (Lt σ t).length ≤ 256 := rbFold_length_le (by simp) _

theorem Lt_succ {σ : State} {t : Nat} (ht : t < 544) :
    Lt σ (t + 1) = rbStep (etaOf σ) (Lt σ t) (Z σ t) := by
  simp only [Lt]
  rw [Ball.take_succ'' _ (by rw [X_length]; omega), rbFold_snoc]

/-- What the loop keeps, and the bytes of the output and the coefficients
stored, from the prologue on. -/
structure Base (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 544 = X σ
  cs : Consts (etaOf σ) s

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (t : Nat) (s : State) : Prop where
  base : Base σ s
  x2 : s.gpr .x2 = (spOf σ).at' (840 + t)
  x3 : s.gpr .x3 = coeffAddr (σ.gpr .x2) (Lt σ t).length
  x4 : (s.gpr .x4).toNat = 256 - (Lt σ t).length
  x5 : (s.gpr .x5).toNat = 544 - t
  st : Stored s.mem (σ.gpr .x2) (Lt σ t)

/-- After loading byte `t`. -/
structure LB (σ : State) (t : Nat) (s : State) : Prop where
  base : Base σ s
  x2 : s.gpr .x2 = (spOf σ).at' (840 + (t + 1))
  x3 : s.gpr .x3 = coeffAddr (σ.gpr .x2) (Lt σ t).length
  x4 : (s.gpr .x4).toNat = 256 - (Lt σ t).length
  x5 : (s.gpr .x5).toNat = 544 - (t + 1)
  x6 : s.gpr .x6 = (Z σ t).setWidth 64
  x7 : s.gpr .x7 = BitVec.ofNat 64 ((Z σ t).toNat % 16)
  st : Stored s.mem (σ.gpr .x2) (Lt σ t)

/-- After trying the low half-byte of byte `t`. -/
structure LM (σ : State) (t : Nat) (s : State) : Prop where
  base : Base σ s
  x2 : s.gpr .x2 = (spOf σ).at' (840 + (t + 1))
  x3 : s.gpr .x3 = coeffAddr (σ.gpr .x2) (Lm σ t).length
  x4 : (s.gpr .x4).toNat = 256 - (Lm σ t).length
  x5 : (s.gpr .x5).toNat = 544 - (t + 1)
  x7 : s.gpr .x7 = BitVec.ofNat 64 ((Z σ t).toNat / 16)
  st : Stored s.mem (σ.gpr .x2) (Lm σ t)

section
variable {σ : State} (hp : rbK.pre σ)
include hp

theorem spOk : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, by show (66 : Nat) < 2 ^ 64; decide⟩

theorem eta : etaOf σ = 2 ∨ etaOf σ = 4 := hp.2.2.2.2.2.2.2.2.2

theorem Base.keepA {s s' : State} (h : Base σ s) {regs : List Reg} (hk : Keep regs s s')
    (hf : Frame [polyR (σ.gpr .x2)] s.mem s'.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide)
    (hc : ∀ r ∈ regs, r ∉ [Reg.x9, .x10, .x11, .x15, .x16, .x17] := by decide) : Base σ s' :=
  ⟨h.env.keepA (spOk hp) hk hf hr, by
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' (spOk hp) (by omega)).symm) (by omega)]; exact h.out,
    h.cs.keep hk hc⟩

omit hp in
theorem Base.byte {s : State} (h : Base σ s) {p : Nat} (hp' : p < 544) :
    s.mem ((spOf σ).at' (840 + p)) = Z σ p := by
  rw [← at_add, ← MlKem.bytesAt_getD s.mem _ hp', h.out]

theorem inA' {s : State} (h : Base σ s) {i : Nat} (hi : i < 256) :
    InRegions s.wr (coeffAddr (σ.gpr .x2) i) 4 := inA (spOk hp) h.env.wr hi

/-- The load of byte `t`. -/
theorem load_ok {t : Nat} (ht : t < 544) {s : State} (h : LAt σ t s) : WP isa (.block rbLoad) s (LB σ t) := by
  refine wp_ldrb (a := (spOf σ).at' (840 + t)) (by decide) (by rw [h.x2, ptr_zero])
    (inScrRd (spOk hp) h.base.env.rd h.base.env.wr (by omega)) fun s₁ o₁ e₁ => ?_
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => wp_subImm (by decide) fun s₃ o₃ e₃ => wp_and fun s₄ o₄ e₄ =>
    wp_nil ?_
  have k := ((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep
  have m : s₄.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have x6 : s₄.gpr .x6 = (Z σ t).setWidth 64 := by
    rw [o₄.get .x6, o₃.get .x6, o₂.get .x6, e₁, h.base.byte ht]
  refine ⟨h.base.keepA hp k (by rw [m]; exact Frame.refl _ _), ?_, by rw [k.get .x3, h.x3],
    by rw [k.get .x4, h.x4], ?_, x6, ?_, by rw [m]; exact h.st⟩
  · rw [o₄.get .x2, o₃.get .x2, e₂, o₁.get .x2, h.x2, at_add, Nat.add_assoc]
  · rw [o₄.get .x5, e₃, o₂.get .x5, o₁.get .x5, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  · apply BitVec.eq_of_toNat_eq
    rw [e₄, Proof.MlKem.AArch64.toNat_and_mask _ _ (k := 4) (by
        rw [o₃.get .x11, o₂.get .x11, o₁.get .x11, h.base.cs.x11]; rfl),
      o₃.get .x6, o₂.get .x6, e₁, toNat_byte, h.base.byte ht, BitVec.toNat_ofNat]
    have := (Z σ t).isLt
    omega

/-- The try of the low half-byte of byte `t`, when `j < 256`. -/
theorem lo_ok {t : Nat} {s : State} (h : LB σ t s) (hl : (Lt σ t).length < 256) :
    WP isa (.block (rbTry (etaOf σ) ++ ([.lsr .x .x7 .x6 4] : List Instr))) s (LM σ t) := by
  rw [WP.block_append_iff]
  refine WP.mono (try_ok (eta hp) (L := Lt σ t) (by omega) h.base.cs h.x7 h.x3 h.x4 hl h.st
    (inA' hp h.base hl)) fun s₁ ⟨k₁, f₁, x3, x4, st⟩ => wp_lsr (by decide) fun s₂ o₂ e₂ => wp_nil ?_
  refine ⟨(h.base.keepA hp k₁ f₁).keepA hp o₂.keep (by rw [o₂.mem]; exact Frame.refl _ _),
    by rw [o₂.get .x2, k₁.get .x2, h.x2], by rw [o₂.get .x3, x3], by rw [o₂.get .x4, x4],
    by rw [o₂.get .x5, k₁.get .x5, h.x5], ?_, by rw [o₂.mem]; exact st⟩
  apply BitVec.eq_of_toNat_eq
  rw [e₂, toNat_lsr, k₁.get .x6, h.x6, toNat_byte, BitVec.toNat_ofNat]
  have := (Z σ t).isLt
  omega

/-- The try of the high half-byte of byte `t`, when `j < 256` still. -/
theorem hi_ok {t : Nat} (ht : t < 544) {s : State} (h : LM σ t s) (hl : (Lm σ t).length < 256) :
    WP isa (.block (rbTry (etaOf σ))) s (LAt σ (t + 1)) := by
  have hl0 : (Lt σ t).length < n := by
    have := hbTry_length (etaOf σ) (Lt σ t) ((Z σ t).toNat % 16)
    simp only [Lm, n] at hl ⊢
    omega
  have e : Lt σ (t + 1) = hbTry (etaOf σ) (Lm σ t) ((Z σ t).toNat / 16) := by
    rw [Lt_succ ht, rbStep, ifT hl0, ifT (show (Lm σ t).length < n from hl)]
  refine WP.mono (try_ok (eta hp) (L := Lm σ t) (by have := (Z σ t).isLt; omega) h.base.cs h.x7 h.x3 h.x4 hl
    h.st (inA' hp h.base hl)) fun s₁ ⟨k₁, f₁, x3, x4, st⟩ => ?_
  rw [← e] at x3 x4 st
  exact ⟨h.base.keepA hp k₁ f₁, by rw [k₁.get .x2, h.x2], x3, x4, by rw [k₁.get .x5, h.x5], st⟩

omit hp in
/-- `j = 256` after the low half-byte: the iteration is done. -/
theorem lo_full {t : Nat} (ht : t < 544) {s : State} (h : LM σ t s) (hl' : (Lt σ t).length < 256)
    (hl : (Lm σ t).length = 256) : LAt σ (t + 1) s := by
  have e : Lt σ (t + 1) = Lm σ t := by
    rw [Lt_succ ht, rbStep, ifT (show (Lt σ t).length < n from hl'),
      ifF (show ¬ (Lm σ t).length < n by simp only [n]; omega)]
  exact ⟨h.base, h.x2, by rw [e, h.x3], by rw [e, h.x4], h.x5, by rw [e]; exact h.st⟩

omit hp in
/-- `j = 256` before byte `t`: the iteration does nothing but its load. -/
theorem full {t : Nat} (ht : t < 544) {s : State} (h : LB σ t s) (hl : (Lt σ t).length = 256) :
    LAt σ (t + 1) s := by
  have e : Lt σ (t + 1) = Lt σ t := by rw [Lt_succ ht, rbStep, ifF (by simp only [n]; omega)]
  exact ⟨h.base, h.x2, by rw [e, h.x3], by rw [e, h.x4], h.x5, by rw [e]; exact h.st⟩

omit hp in
theorem eval_x4 {s : State} {L : List Zq} (h : (s.gpr .x4).toNat = 256 - L.length) (hl : L.length ≤ 256) :
    isa.eval (.zero .x .x4) s = some (decide (L.length = 256)) := by
  rw [eval_zero, eq_zero_iff, h]
  congr 1
  exact decide_eq_decide.mpr (by omega)

/-- An iteration. -/
theorem step_ok {t : Nat} (ht : t < 544) {s : State} (h : LAt σ t s) :
    WP isa (rbBody (etaOf σ)) s fun s' => LAt σ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 544) := by
  have c5 : ∀ {u : State}, (u.gpr .x5).toNat = 544 - (t + 1) → ((u.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 544) :=
    fun h5 => by rw [h5]; omega
  refine WP.seq (WP.mono (load_ok hp ht h) fun s₁ h₁ => ?_)
  by_cases hf : (Lt σ t).length = 256
  · exact WP.ite true (by rw [eval_x4 h₁.x4 (Lt_le σ t), decide_eq_true hf]) (fun _ =>
      wp_nil ⟨full ht h₁ hf, c5 h₁.x5⟩) (fun h => nomatch h)
  refine WP.ite false (by rw [eval_x4 h₁.x4 (Lt_le σ t), decide_eq_false hf]) (fun h => nomatch h) fun _ => ?_
  refine WP.seq (WP.mono (lo_ok hp h₁ (by have := Lt_le σ t; omega)) fun s₂ h₂ => ?_)
  have hml : (Lm σ t).length ≤ 256 := by
    have := hbTry_length (etaOf σ) (Lt σ t) ((Z σ t).toNat % 16)
    have := halfByteOk_le (etaOf σ) ((Z σ t).toNat % 16)
    have := Lt_le σ t
    simp only [Lm]; omega
  by_cases hf' : (Lm σ t).length = 256
  · exact WP.ite true (by rw [eval_x4 h₂.x4 hml, decide_eq_true hf']) (fun _ =>
      wp_nil ⟨lo_full ht h₂ (by have := Lt_le σ t; omega) hf', c5 h₂.x5⟩) (fun h => nomatch h)
  · exact WP.ite false (by rw [eval_x4 h₂.x4 hml, decide_eq_false hf']) (fun h => nomatch h) fun _ =>
      WP.mono (hi_ok hp ht h₂ (by omega)) fun s₃ h₃ => ⟨h₃, c5 (by rw [h₃.x5])⟩

theorem movz_rbBound : ((BitVec.ofNat 16 (rbBound (etaOf σ))).setWidth 64) = BitVec.ofNat 64 (rbB (etaOf σ)) := by
  rcases eta hp with h | h <;> rw [h] <;> rfl

omit hp in
theorem x27_eq {s : State} (he : Env (spOf σ) σ s) : s.gpr .x27 = BitVec.ofNat 64 (etaOf σ) := by
  rw [he.x27]
  apply BitVec.eq_of_toNat_eq
  simp

/-- After the sponge. -/
theorem setup_ok {s : State} (h : J6 136 544 (spOf σ) σ s) :
    WP isa (.block (rbSetup (etaOf σ))) s (LAt σ 0) := by
  unfold rbSetup movQ
  refine wp_addImm (by decide) fun s₁ o₁ e₁ => wp_mov fun s₂ o₂ e₂ => wp_movz fun s₃ o₃ e₃ =>
    wp_movz fun s₄ o₄ e₄ => RejNtt.movQ_ok fun s₅ o₅ e₅ => wp_mov fun s₆ o₆ e₆ => wp_movz fun s₇ o₇ e₇ =>
    wp_movz fun s₈ o₈ e₈ => wp_movz fun s₉ o₉ e₉ => wp_movz fun s₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k := (((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).trans o₉.keep).trans o₁₀.keep)
  have m : s₁₀.mem = s.mem := by
    rw [o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have hL : Lt σ 0 = [] := rfl
  refine ⟨⟨h.env.keep k m, by rw [m, h.out, X, H_eq], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₁₀.get .x9, o₉.get .x9, o₈.get .x9, o₇.get .x9, o₆.get .x9]
    exact BitVec.eq_of_toNat_eq (by rw [e₅, BitVec.toNat_ofNat]; rfl)
  · rw [o₁₀.get .x10, o₉.get .x10, o₈.get .x10, o₇.get .x10, e₆, o₅.get .x27, o₄.get .x27, o₃.get .x27,
      o₂.get .x27, o₁.get .x27, x27_eq h.env]
  · rw [o₁₀.get .x11, o₉.get .x11, o₈.get .x11, e₇]; rfl
  · rw [o₁₀.get .x15, o₉.get .x15, e₈, movz_rbBound hp]
  · rw [o₁₀.get .x16, e₉]; rfl
  · rw [e₁₀]; rfl
  · rw [o₁₀.get .x2, o₉.get .x2, o₈.get .x2, o₇.get .x2, o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2,
      o₂.get .x2, e₁, h.env.x25]
  · rw [o₁₀.get .x3, o₉.get .x3, o₈.get .x3, o₇.get .x3, o₆.get .x3, o₅.get .x3, o₄.get .x3, o₃.get .x3, e₂,
      o₁.get .x26, h.env.x26, hL]; simp [coeffAddr]
  · rw [o₁₀.get .x4, o₉.get .x4, o₈.get .x4, o₇.get .x4, o₆.get .x4, o₅.get .x4, o₄.get .x4, e₃, hL]; rfl
  · rw [o₁₀.get .x5, o₉.get .x5, o₈.get .x5, o₇.get .x5, o₆.get .x5, o₅.get .x5, e₄]; rfl
  · rw [m, hL]; exact stored_nil _ _

theorem loop_ok {s : State} (h : J6 136 544 (spOf σ) σ s) :
    WP isa (rbLoop (etaOf σ)) s (LAt σ 544) :=
  WP.seq (WP.mono (setup_ok hp h) fun _ h0 =>
    count_loop (by decide) (LAt σ) (fun t ht s hs => step_ok hp ht hs) h0)

/-- The loop, chosen by `η`. -/
theorem branch_ok {s : State} (h : J6 136 544 (spOf σ) σ s) :
    WP isa (.seq (.block [.subImm .x .x9 .x27 2]) (.ite (.zero .x .x9) (rbLoop 2) (rbLoop 4))) s
      (LAt σ 544) := by
  refine WP.seq (wp_subImm (by decide) fun s₁ o₁ e₁ => wp_nil ?_)
  have h6 : J6 136 544 (spOf σ) σ s₁ := ⟨h.env.keep o₁.keep o₁.mem, by rw [o₁.mem]; exact h.out⟩
  rcases eta hp with he | he
  · refine WP.ite true (by rw [eval_zero, eq_zero_iff, e₁, x27_eq h.env, he]; rfl) (fun _ => ?_) (fun h => nomatch h)
    have := loop_ok hp h6; rw [he] at this; exact this
  · refine WP.ite false (by rw [eval_zero, eq_zero_iff, e₁, x27_eq h.env, he]; rfl) (fun h => nomatch h) (fun _ => ?_)
    have := loop_ok hp h6; rw [he] at this; exact this

omit hp in
/-- After the loop. -/
theorem Lt_544 : Lt σ 544 = rbFold (etaOf σ) [] (X σ) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {s : State} (h : LAt σ 544 s) :
    WP isa (.block (retZ ++ epi)) s fun s' => GprAbi σ s' ∧ rbK.post σ s' := by
  rw [retZ, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subImm (by decide) fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => ?_
  have hl := Lt_le σ 544
  have x4 := h.x4
  have st := h.st
  rw [Lt_544] at hl x4 st
  have v0 : (s₂.gpr .x0).toNat = if (rbFold (etaOf σ) [] (X σ)).length = 256 then 1 else 0 := by
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, x4, one]
    simp only [Nat.reducePow]
    split <;> omega
  refine WP.mono (epi_ok (spOk hp) (h.base.env.keep (h₁.keep.trans h₂.keep) (by rw [h₂.mem, h₁.mem])))
    fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₂.mem, h₁.mem]
    exact stored_polyIs st hf

theorem pro_ok : WP isa (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0))) σ (J0 (spOf σ) σ) :=
  Sample.pro_ok (spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x1 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

end

theorem correct (σ : State) (hp : rbK.pre σ) :
    ∃ t s', Exec isa rejBounded σ t s' ∧ abiPreserved σ s' ∧ rbK.post σ s' :=
  WP.withPreservedV (hc := by decide +kernel) <| WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok (spOk hp) (rate := 136) (outlen := 544) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (branch_ok hp h2) fun _ h3 => end_ok hp h3)))

end RejBounded

end VG.Proof.MlDsa.AArch64.Sample
