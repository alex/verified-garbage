import VerifiedGarbage.Proof.Framework.Taint

/-!
# Summaries of called functions, for the constant-time analysis

`taint_decide` has the kernel evaluate the analysis (`Taint.check`) of the
whole program, including the body of every function it calls, once per call:
a sponge called forty times has its permutation analysed forty times, in every
theorem about a caller. A *summary* `(code, pre, post)` says that the analysis
of `code` from `pre` succeeds and ends with at least `post` public
(`SumOk`); it is proven once, and `checkSum` then uses it, in place of the
analysis of `code`, wherever the program has `code` with at least `pre`
public.

This needs the analysis to be monotone (`Mono`): with more public on entry,
it succeeds, with as much public at the end. The kernel never compares code:
`checkSum` does not look at the code it summarizes, and `fill` puts the
summarized code back where the hint says, so `fill S c h = c`, which the
kernel checks by definitional unfolding (`Eq.refl`), says that it was the
right code. `taint_decide_sum` and `taint_summary` compute the hints (in
compiled code, which need not be sound) and prove both.
-/

namespace VG

namespace Taint

variable {M : ISA} (A : Taint M)

/-- The analysis is monotone: with more public (`le`) on entry, each of its
steps succeeds, with more public after it. -/
class Mono : Prop where
  le_refl : ∀ τ, A.le τ τ = true
  le_trans : ∀ {a b c}, A.le a b = true → A.le b c = true → A.le a c = true
  step : ∀ {τ σ τ'} (i : M.Instr), A.le τ σ = true → A.step τ i = some τ' →
    ∃ σ', A.step σ i = some σ' ∧ A.le τ' σ' = true
  condPub : ∀ {τ σ} (c : M.Cond), A.le τ σ = true → A.condPub τ c = true → A.condPub σ c = true
  meet : ∀ {τ₁ τ₂ σ₁ σ₂}, A.le τ₁ σ₁ = true → A.le τ₂ σ₂ = true →
    A.le (A.meet τ₁ τ₂) (A.meet σ₁ σ₂) = true
  call : ∀ {τ σ τ'}, A.le τ σ = true → A.call τ = some τ' →
    ∃ σ', A.call σ = some σ' ∧ A.le τ' σ' = true
  ret : ∀ {τ σ τ'}, A.le τ σ = true → A.ret τ = some τ' →
    ∃ σ', A.ret σ = some σ' ∧ A.le τ' σ' = true
  push : ∀ {τ σ τ'} (i : M.Instr), A.le τ σ = true → A.push τ i = some τ' →
    ∃ σ', A.push σ i = some σ' ∧ A.le τ' σ' = true
  pop : ∀ {τ σ τ'} (i : M.Instr), A.le τ σ = true → A.pop τ i = some τ' →
    ∃ σ', A.pop σ i = some σ' ∧ A.le τ' σ' = true

/-- The analysis keeps what is public of a set `F` of things it does not
write (`keeps F i`), between `join` and `meet` (a lattice), with a least
element `bot`. Then a summary can say that what was public of its `F` stays
public (`SumOk`), and one summary applies to calls that differ in what is
public of `F`. -/
class Frame extends Mono A where
  join : A.T → A.T → A.T
  bot : A.T
  le_join_left : ∀ a b, A.le a (join a b) = true
  le_join_right : ∀ a b, A.le b (join a b) = true
  join_le : ∀ {a b c}, A.le a c = true → A.le b c = true → A.le (join a b) c = true
  meet_le_left : ∀ a b, A.le (A.meet a b) a = true
  meet_le_right : ∀ a b, A.le (A.meet a b) b = true
  le_meet : ∀ {a b c}, A.le a b = true → A.le a c = true → A.le a (A.meet b c) = true
  bot_le : ∀ a, A.le bot a = true
  /-- `i` does not write anything of `F`. -/
  keeps : A.T → M.Instr → Bool
  /-- A call and a return do not write anything of `F`. -/
  keepsCall : A.T → Bool
  keeps_bot : ∀ i, keeps bot i = true
  keepsCall_bot : keepsCall bot = true
  step_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → A.le Φ F = true → A.le Φ σ = true →
    A.step σ i = some σ' → A.le Φ σ' = true
  call_keeps : ∀ {F Φ σ σ'}, keepsCall F = true → A.le Φ F = true → A.le Φ σ = true →
    A.call σ = some σ' → A.le Φ σ' = true
  ret_keeps : ∀ {F Φ σ σ'}, keepsCall F = true → A.le Φ F = true → A.le Φ σ = true →
    A.ret σ = some σ' → A.le Φ σ' = true
  push_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → A.le Φ F = true → A.le Φ σ = true →
    A.push σ i = some σ' → A.le Φ σ' = true
  pop_keeps : ∀ {F Φ σ σ'} (i : M.Instr), keeps F i = true → A.le Φ F = true → A.le Φ σ = true →
    A.pop σ i = some σ' → A.le Φ σ' = true

/-- A hint for `checkSum`: a `Hint`, where `sum k` uses the `k`-th summary. -/
inductive SHint (T : Type) where
  | block (mids : List T)
  | seq (mid : T) (h₁ h₂ : SHint T)
  | ite (h₁ h₂ : SHint T)
  | loop (inv : T) (h : SHint T)
  | call (h : SHint T)
  | frame (h : SHint T)
  | sum (k : Nat)
  deriving Lean.ToExpr

/-- A summary: code, `pre`, `post` and `frame`. -/
abbrev Summary (M : ISA) (T : Type) := Prog M × T × T × T

/-- The summary `(code, pre, post, F)` holds: from at least `pre` public, the
analysis of `code` succeeds, and ends with at least `post` public, and what
was public of `F`. -/
def SumOk (s : Summary M A.T) : Prop :=
  ∀ τ, A.le s.2.1 τ = true → ∃ h τ', A.check τ s.1 h = some τ' ∧ A.le s.2.2.1 τ' = true ∧
    A.le (A.meet τ s.2.2.2) τ' = true

/-- Every summary of the list holds. -/
def AllOk : List (Summary M A.T) → Prop
  | [] => True
  | s :: S => SumOk A s ∧ AllOk S

/-- `check`, with the summaries `S`: at a `sum k` hint, the `k`-th summary
`(code, pre, post, F)`, if at least `pre` is public, gives `post` and what is
public of `F`, whatever the code there (`fill` says it is `code`). -/
def checkSum [Frame A] (S : List (Summary M A.T)) (τ : A.T) (c : Prog M) (h : SHint A.T) : Option A.T :=
  match h, τ, c with
  | .sum k, τ, _ => match S[k]? with
    | some (_, pre, post, F) => if A.le pre τ then some (Frame.join post (A.meet τ F)) else none
    | none => none
  | .block ms, τ, .block is => checkChunks A τ is ms
  | .seq mid h₁ h₂, τ, .seq c₁ c₂ =>
    (checkSum S τ c₁ h₁).bind fun τ' => if A.le mid τ' then checkSum S mid c₂ h₂ else none
  | .ite h₁ h₂, τ, .ite c t e =>
    if A.condPub τ c then
      (checkSum S τ t h₁).bind fun τ₁ => (checkSum S τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | .loop σ h, τ, .loop body c =>
    if A.le σ τ then
      (checkSum S σ body h).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
    else none
  | .call h, τ, .call _ body => (A.call τ).bind fun τ₁ => (checkSum S τ₁ body h).bind A.ret
  | .frame h, τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (checkSum S τ₁ body h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none
termination_by structural h

/-- Nothing of `F` is written, but where the hint uses a summary, whose frame
then has all of `F`. -/
def keepsSum [Frame A] (S : List (Summary M A.T)) (F : A.T) (c : Prog M) (h : SHint A.T) : Bool :=
  match h, c with
  | .sum k, _ => match S[k]? with
    | some (_, _, _, F') => A.le F F'
    | none => true
  | .block _, .block is => is.all (Frame.keeps (A := A) F)
  | .seq _ h₁ h₂, .seq a b => keepsSum S F a h₁ && keepsSum S F b h₂
  | .ite h₁ h₂, .ite _ t e => keepsSum S F t h₁ && keepsSum S F e h₂
  | .loop _ h, .loop b _ => keepsSum S F b h
  | .call h, .call _ b => Frame.keepsCall (A := A) F && keepsSum S F b h
  | .frame h, .frame i b j =>
    Frame.keeps (A := A) F i && keepsSum S F b h && Frame.keeps (A := A) F j
  | _, _ => true
termination_by structural h

variable {A} in
/-- `c`, with the code of the summary at each `sum k` of the hint in place of
what is there. `fill S c h = c` says that each summary is used for its code. -/
def fill {T : Type} (S : List (Summary M T)) (c : Prog M) (h : SHint T) : Prog M :=
  match h, c with
  | .sum k, c => match S[k]? with
    | some (b, _, _, _) => b
    | none => c
  | .seq _ h₁ h₂, .seq a b => .seq (fill S a h₁) (fill S b h₂)
  | .ite h₁ h₂, .ite cd t e => .ite cd (fill S t h₁) (fill S e h₂)
  | .loop _ h, .loop b cd => .loop (fill S b h) cd
  | .call h, .call n b => .call n (fill S b h)
  | .frame h, .frame i b j => .frame i (fill S b h) j
  | _, c => c
termination_by structural h

/-- `checkSum` ends with at least `post` public. -/
def checkSumLe [Frame A] (S : List (Summary M A.T)) (τ : A.T) (c : Prog M) (h : SHint A.T)
    (post : A.T) : Bool :=
  match checkSum A S τ c h with
  | some τ' => A.le post τ'
  | none => false

/-! ## Soundness -/

private theorem if_pos' {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

variable {A}

local notation "J" => Frame.join (A := A)

theorem checkBlock_frame [hm : Frame A] {is : List M.Instr} {F Φ τ σ τ' : A.T}
    (h : A.checkBlock τ is = some τ') (hk : is.all (Frame.keeps (A := A) F) = true)
    (hΦF : A.le Φ F = true) (hle : A.le τ σ = true) (hΦ : A.le Φ σ = true) :
    ∃ σ', A.checkBlock σ is = some σ' ∧ A.le τ' σ' = true ∧ A.le Φ σ' = true := by
  induction is generalizing τ σ with
  | nil =>
    simp only [checkBlock, Option.some.injEq] at h
    subst h; exact ⟨σ, rfl, hle, hΦ⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hk
    simp only [checkBlock, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, hs, hr⟩ := h
    obtain ⟨σ₁, hs', hle'⟩ := hm.step i hle hs
    obtain ⟨σ', h', hle'', hΦ'⟩ := ih hr hk.2 hle' (hm.step_keeps i hk.1 hΦF hΦ hs')
    exact ⟨σ', by simp only [checkBlock, Option.bind_eq_some_iff]; exact ⟨σ₁, hs', h'⟩, hle'', hΦ'⟩

theorem checkChunks_frame [hm : Frame A] {ms : List A.T} {is : List M.Instr} {F Φ τ σ τ' : A.T}
    (h : A.checkChunks τ is ms = some τ') (hk : is.all (Frame.keeps (A := A) F) = true)
    (hΦF : A.le Φ F = true) (hle : A.le τ σ = true) (hΦ : A.le Φ σ = true) :
    ∃ σ', A.checkChunks σ is (ms.map (J · Φ)) = some σ' ∧ A.le τ' σ' = true ∧
      A.le Φ σ' = true := by
  induction ms generalizing τ σ is with
  | nil => exact checkBlock_frame h hk hΦF hle hΦ
  | cons m ms ih =>
    simp only [checkChunks, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, h₁, h₂⟩ := h
    split at h₂ <;> [rename_i hm₁; cases h₂]
    have hk' : (is.take chunk ++ is.drop chunk).all (Frame.keeps (A := A) F) = true := by
      rw [List.take_append_drop]; exact hk
    rw [List.all_append, Bool.and_eq_true] at hk'
    obtain ⟨σ₁, h₁', hle₁, hΦ₁⟩ := checkBlock_frame h₁ hk'.1 hΦF hle hΦ
    obtain ⟨σ', h', hle', hΦ'⟩ := ih h₂ hk'.2 (hm.le_join_left m Φ) (hm.le_join_right m Φ)
    refine ⟨σ', ?_, hle', hΦ'⟩
    simp only [List.map_cons, checkChunks, Option.bind_eq_some_iff]
    exact ⟨σ₁, h₁', by rw [if_pos' (hm.join_le (hm.le_trans hm₁ hle₁) hΦ₁)]; exact h'⟩

theorem AllOk.get {S : List (Summary M A.T)} (hS : AllOk A S) {k : Nat}
    {s : Summary M A.T} (h : S[k]? = some s) : SumOk A s := by
  induction S generalizing k with
  | nil => cases h
  | cons s' S ih =>
    cases k with
    | zero => cases h; exact hS.1
    | succ k => exact ih hS.2 h

/-- A successful `checkSum`, with summaries that hold, used for their code
(`fill`), is a successful `check` from any taint with more public, which keeps
public what was of `F` if nothing writes it (`keepsSum`). -/
theorem checkSum_frame [hm : Frame A] {S : List (Summary M A.T)} (hS : AllOk A S) {F Φ : A.T}
    (hΦF : A.le Φ F = true) :
    ∀ {hc : SHint A.T} {c : Prog M} {τ σ τ' : A.T}, A.checkSum S τ c hc = some τ' →
      fill S c hc = c → keepsSum A S F c hc = true → A.le τ σ = true → A.le Φ σ = true →
      ∃ h σ', A.check σ c h = some σ' ∧ A.le τ' σ' = true ∧ A.le Φ σ' = true := by
  intro hc
  induction hc with
  | sum k =>
    intro c τ σ τ' h hf hk hle hΦ
    replace h : (match S[k]? with
      | some (_, pre, post, F) => if A.le pre τ then some (J post (A.meet τ F)) else none
      | none => none) = some τ' := h
    rw [fill] at hf
    rw [keepsSum] at hk
    cases hks : S[k]? with
    | none => rw [hks] at h; cases h
    | some s =>
      obtain ⟨b, pre, post, F'⟩ := s
      rw [hks] at h hf hk
      simp only at h hf hk
      subst hf
      split at h <;> [rename_i hl; cases h]
      cases h
      obtain ⟨g, σ', h', hpost, hfr⟩ := hS.get hks σ (hm.le_trans hl hle)
      refine ⟨g, σ', h', hm.join_le hpost
        (hm.le_trans (hm.meet hle (hm.le_refl F')) hfr), ?_⟩
      exact hm.le_trans (hm.le_meet hΦ (hm.le_trans hΦF hk)) hfr
  | block ms =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | block is =>
      obtain ⟨σ', h', hle', hΦ'⟩ := checkChunks_frame (ms := ms) (A := A) h hk hΦF hle hΦ
      exact ⟨.block (ms.map (J · Φ)), σ', h', hle', hΦ'⟩
    | _ => cases (h : (none : Option A.T) = some τ')
  | seq mid g₁ g₂ ih₁ ih₂ =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | seq c₁ c₂ =>
      have h : ((A.checkSum S τ c₁ g₁).bind fun τ' =>
        if A.le mid τ' then A.checkSum S mid c₂ g₂ else none) = some τ' := h
      have hf : Code.seq (fill S c₁ g₁) (fill S c₂ g₂) = .seq c₁ c₂ := hf
      have hk : (keepsSum A S F c₁ g₁ && keepsSum A S F c₂ g₂) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hl; cases h₂]
      obtain ⟨g₁', σ₁, h₁', hle₁, hΦ₁⟩ := ih₁ h₁ hf_1 hk.1 hle hΦ
      obtain ⟨g₂', σ₂, h₂', hle₂, hΦ₂⟩ := ih₂ h₂ hf_2 hk.2 (hm.le_join_left mid Φ)
        (hm.le_join_right mid Φ)
      refine ⟨.seq (J mid Φ) g₁' g₂', σ₂, ?_, hle₂, hΦ₂⟩
      show ((A.check σ c₁ g₁').bind fun τ' =>
        if A.le (J mid Φ) τ' then A.check (J mid Φ) c₂ g₂' else none) = some σ₂
      rw [h₁', Option.bind_some, if_pos' (hm.join_le (hm.le_trans hl hle₁) hΦ₁)]; exact h₂'
    | _ => cases (h : (none : Option A.T) = some τ')
  | ite g₁ g₂ ih₁ ih₂ =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | ite cd t e =>
      have h : (if A.condPub τ cd then
          (A.checkSum S τ t g₁).bind fun τ₁ => (A.checkSum S τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      have hf : Code.ite cd (fill S t g₁) (fill S e g₂) = .ite cd t e := hf
      have hk : (keepsSum A S F t g₁ && keepsSum A S F e g₂) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2 hf_3
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, rfl⟩ := h
      obtain ⟨g₁', σ₁, h₁', hle₁, hΦ₁⟩ := ih₁ h₁ hf_2 hk.1 hle hΦ
      obtain ⟨g₂', σ₂, h₂', hle₂, hΦ₂⟩ := ih₂ h₂ hf_3 hk.2 hle hΦ
      refine ⟨.ite g₁' g₂', A.meet σ₁ σ₂, ?_, hm.meet hle₁ hle₂, hm.le_meet hΦ₁ hΦ₂⟩
      show (if A.condPub σ cd then
          (A.check σ t g₁').bind fun τ₁ => (A.check σ e g₂').map fun τ₂ => A.meet τ₁ τ₂
        else none) = _
      rw [if_pos' (hm.condPub cd hle hp), h₁', Option.bind_some, h₂', Option.map_some]
    | _ => cases (h : (none : Option A.T) = some τ')
  | loop inv g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | loop body cd =>
      have h : (if A.le inv τ then
          (A.checkSum S inv body g).bind fun σ' =>
            if A.le inv σ' && A.condPub σ' cd then some σ' else none
        else none) = some τ' := h
      have hf : Code.loop (fill S body g) cd = .loop body cd := hf
      have hk : keepsSum A S F body g = true := hk
      injection hf with hf_1
      split at h <;> [rename_i hl; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, h₂⟩ := h
      split at h₂ <;> [rename_i hc; cases h₂]
      cases h₂
      simp only [Bool.and_eq_true] at hc
      obtain ⟨g', σ₁, h₁', hle₁, hΦ₁⟩ := ih h₁ hf_1 hk (hm.le_join_left inv Φ)
        (hm.le_join_right inv Φ)
      refine ⟨.loop (J inv Φ) g', σ₁, ?_, hle₁, hΦ₁⟩
      show (if A.le (J inv Φ) σ then
          (A.check (J inv Φ) body g').bind fun σ' =>
            if A.le (J inv Φ) σ' && A.condPub σ' cd then some σ' else none
        else none) = some σ₁
      rw [if_pos' (hm.join_le (hm.le_trans hl hle) hΦ), h₁', Option.bind_some,
        if_pos' (by rw [hm.join_le (hm.le_trans hc.1 hle₁) hΦ₁, hm.condPub cd hle₁ hc.2]; rfl)]
    | _ => cases (h : (none : Option A.T) = some τ')
  | call g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | call n body =>
      have h : ((A.call τ).bind fun τ₁ => (A.checkSum S τ₁ body g).bind A.ret) = some τ' := h
      have hf : Code.call n (fill S body g) = .call n body := hf
      have hk : (Frame.keepsCall (A := A) F && keepsSum A S F body g) = true := hk
      rw [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      obtain ⟨σ₁, h₁', hle₁⟩ := hm.call hle h₁
      obtain ⟨g', σ₂, h₂', hle₂, hΦ₂⟩ := ih h₂ hf_2 hk.2 hle₁ (hm.call_keeps hk.1 hΦF hΦ h₁')
      obtain ⟨σ₃, h₃', hle₃⟩ := hm.ret hle₂ h₃
      refine ⟨.call g', σ₃, ?_, hle₃, hm.ret_keeps hk.1 hΦF hΦ₂ h₃'⟩
      show ((A.call σ).bind fun τ₁ => (A.check τ₁ body g').bind A.ret) = some σ₃
      rw [h₁', Option.bind_some, h₂', Option.bind_some, h₃']
    | _ => cases (h : (none : Option A.T) = some τ')
  | frame g ih =>
    intro c τ σ τ' h hf hk hle hΦ
    cases c with
    | frame i body j =>
      have h : ((A.push τ i).bind fun τ₁ => (A.checkSum S τ₁ body g).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      have hf : Code.frame i (fill S body g) j = .frame i body j := hf
      have hk : (Frame.keeps (A := A) F i && keepsSum A S F body g && Frame.keeps (A := A) F j) = true :=
        hk
      simp only [Bool.and_eq_true] at hk
      injection hf with hf_1 hf_2 hf_3
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      obtain ⟨σ₁, h₁', hle₁⟩ := hm.push i hle h₁
      obtain ⟨g', σ₂, h₂', hle₂, hΦ₂⟩ := ih h₂ hf_2 hk.1.2 hle₁
        (hm.push_keeps i hk.1.1 hΦF hΦ h₁')
      obtain ⟨σ₃, h₃', hle₃⟩ := hm.pop j hle₂ h₃
      refine ⟨.frame g', σ₃, ?_, hle₃, hm.pop_keeps j hk.2 hΦF hΦ₂ h₃'⟩
      show ((A.push σ i).bind fun τ₁ => (A.check τ₁ body g').bind fun τ₂ => A.pop τ₂ j) =
        some σ₃
      rw [h₁', Option.bind_some, h₂', Option.bind_some, h₃']
    | _ => cases (h : (none : Option A.T) = some τ')

/-- Nothing writes `bot`. -/
theorem keepsSum_bot [hm : Frame A] {S : List (Summary M A.T)} :
    ∀ {hc : SHint A.T} {c : Prog M}, keepsSum A S (Frame.bot (A := A)) c hc = true := by
  intro hc
  induction hc with
  | sum k =>
    intro c
    rw [keepsSum]
    cases S[k]? with
    | none => rfl
    | some s => exact hm.bot_le _
  | block ms =>
    intro c
    cases c with
    | block is => exact List.all_eq_true.mpr fun i _ => hm.keeps_bot i
    | _ => rfl
  | seq _ g₁ g₂ ih₁ ih₂ =>
    intro c
    cases c with
    | seq a b => exact (Bool.and_eq_true _ _).mpr ⟨ih₁, ih₂⟩
    | _ => rfl
  | ite g₁ g₂ ih₁ ih₂ =>
    intro c
    cases c with
    | ite _ a b => exact (Bool.and_eq_true _ _).mpr ⟨ih₁, ih₂⟩
    | _ => rfl
  | loop _ g ih =>
    intro c
    cases c with
    | loop b _ => exact ih
    | _ => rfl
  | call g ih =>
    intro c
    cases c with
    | call _ b => exact (Bool.and_eq_true _ _).mpr ⟨hm.keepsCall_bot, ih⟩
    | _ => rfl
  | frame g ih =>
    intro c
    cases c with
    | frame i b j =>
      simp only [keepsSum, hm.keeps_bot, ih, Bool.and_self]
    | _ => rfl

/-- A summary proven with other summaries. -/
theorem sumOk_of_checkSum [hm : Frame A] {S : List (Summary M A.T)} (hS : AllOk A S)
    {c : Prog M} {pre post F : A.T} {hc : SHint A.T} (h : checkSumLe A S pre c hc post = true)
    (hf : fill S c hc = c) (hk : keepsSum A S F c hc = true) : SumOk A (c, pre, post, F) := by
  unfold checkSumLe at h
  split at h <;> [rename_i τ' hτ; cases h]
  intro τ hτ'
  obtain ⟨g, σ', h', hle', hΦ'⟩ := checkSum_frame hS (hm.meet_le_right τ F) hτ hf hk hτ'
    (hm.meet_le_left τ F)
  exact ⟨g, σ', h', hm.le_trans h hle', hΦ'⟩

/-- A successful `checkSum` with summaries that hold, used for their code, is
a successful `check`. -/
theorem exists_check_of_checkSum [hm : Frame A] {S : List (Summary M A.T)} (hS : AllOk A S)
    {c : Prog M} {τ : A.T} {hc : SHint A.T} (h : (checkSum A S τ c hc).isSome = true)
    (hf : fill S c hc = c) : ∃ h, (A.check τ c h).isSome = true := by
  obtain ⟨τ', hτ⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨g, σ', h', -⟩ := checkSum_frame hS (hm.le_refl _) hτ hf keepsSum_bot (hm.le_refl τ)
    (hm.bot_le τ)
  exact ⟨g, by rw [h']; rfl⟩

/-- The analysis of a function, from a summary of a call of it, from a taint
that the call does not change. -/
theorem exists_check_of_sumOk_call {n : String} {c : Prog M} {pre post F τ : A.T}
    (h : SumOk A (.call n c, pre, post, F)) (hτ : A.le pre τ = true) (hc : A.call τ = some τ) :
    ∃ h, (A.check τ c h).isSome = true := by
  obtain ⟨g, τ', hg, -⟩ := h τ hτ
  cases g with
  | call g =>
    have hg : ((A.call τ).bind fun τ₁ => (A.check τ₁ c g).bind A.ret) = some τ' := hg
    rw [hc, Option.bind_some, Option.bind_eq_some_iff] at hg
    obtain ⟨τ₂, h₂, -⟩ := hg
    exact ⟨g, by rw [h₂]; rfl⟩
  | _ => cases (hg : (none : Option A.T) = some τ')

/-! ## Computing hints

Nothing here needs to be sound: `checkSum` and `fill` check the hint. -/

variable (A)

/-- The first summary of a call of `n` that applies from `τ`: its index and
`post`. -/
def findSum [Frame A] (n : String) (τ : A.T) : List (Summary M A.T) → Nat → Option (Nat × A.T)
  | [], _ => none
  | (c, pre, post, F) :: S, k => match c with
    | .call n' _ =>
      if n' == n && A.le pre τ then some (k, Frame.join post (A.meet τ F)) else findSum n τ S (k + 1)
    | _ => findSum n τ S (k + 1)

/-- `hint`, using the first summary that applies at each call. -/
def hintSum [Frame A] (S : List (Summary M A.T)) : A.T → Prog M → Option (A.T × SHint A.T)
  | τ, .block is => (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A τ is is.length))
  | τ, .seq c₁ c₂ =>
    (hintSum S τ c₁).bind fun (τ₁, h₁) => (hintSum S τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite _ t e =>
    (hintSum S τ t).bind fun (τ₁, h₁) => (hintSum S τ e).map fun (τ₂, h₂) =>
      (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hintSum S · body) loopFuel τ
  | τ, .call n body => match findSum A n τ S 0 with
    | some (k, post) => some (post, .sum k)
    | none => (A.call τ).bind fun τ₁ => (hintSum S τ₁ body).bind fun (τ₂, h) =>
      (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hintSum S τ₁ body).bind fun (τ₂, h) =>
      (A.pop τ₂ j).map (·, .frame h)
where
  go (c : M.Cond) (body : A.T → Option (A.T × SHint A.T)) :
      Nat → A.T → Option (A.T × SHint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- The hint of `hintSum` (any hint, if the analysis fails). -/
def hintSumOf [Frame A] (S : List (Summary M A.T)) (τ : A.T) (c : Prog M) : SHint A.T :=
  ((hintSum A S τ c).map (·.2)).getD (.block [])

/-- The taint at the end of `hintSum` (`τ`, if the analysis fails). -/
def postSumOf [Frame A] (S : List (Summary M A.T)) (τ : A.T) (c : Prog M) : A.T :=
  ((hintSum A S τ c).map (·.1)).getD τ

end Taint

namespace TaintSum

open Lean Meta Elab Tactic

/-- The summaries `ls` (theorems `Taint.SumOk A s`): the list of their `s`, and a
proof that they hold (`Taint.AllOk A`). -/
def summaries (M A : Expr) (ls : Array Name) : MetaM (Expr × Expr) := do
  let T := mkApp2 (mkConst ``Taint.T) M A
  let sTy := mkApp2 (mkConst ``Taint.Summary) M T
  let mut ss := #[]
  for l in ls do
    let ty ← instantiateMVars (← inferType (mkConst l))
    unless ty.isAppOfArity ``Taint.SumOk 3 do
      throwError "taint summaries: {l} is not a `Taint.SumOk`: {ty}"
    ss := ss.push (ty.getArg! 2)
  let S ← mkListLit sTy ss.toList
  let mut prf := mkConst ``True.intro
  for i in [0:ls.size] do
    let j := ls.size - 1 - i
    prf := mkApp4 (mkConst ``And.intro) (← inferType (mkConst ls[j]!))
      (← inferType prf) (mkConst ls[j]!) prf
  return (S, prf)

/-- Evaluates `e : α` in compiled code, as an expression. -/
def evalToExpr (α e : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) α)
  unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) α inst e)

/-- Proves the main goal `fill S c h = c` by the kernel's unfolding, after
rewriting code to its literals. -/
def fillRfl : TacticM Unit := do
  evalTactic (← `(tactic| rw_lit))
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, _, rhs) := ty.eq? | throwError "taint summaries: not an equation: {ty}"
  let u ← getLevel α
  let n ← mkAuxLemma [] ty (mkApp2 (mkConst ``Eq.refl [u]) α rhs)
  g.assign (mkConst n)
  replaceMainGoal []

/-- Proves `p` (with summaries `S`, which `hS` proves): `p` applied to the
hint, then to proofs of `check` (by `lit_decide`) and of `fill` (`fillRfl`). -/
def proveWith (M A S hS τ c : Expr) (p : Name) (extra : Array Expr) : TacticM Unit := do
  let g ← getMainGoal
  let T ← whnfD (mkApp2 (mkConst ``Taint.T) M A)
  let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let hint ← evalToExpr (mkApp (mkConst ``Taint.SHint) T)
    (mkApp6 (mkConst ``Taint.hintSumOf) M A fr S τ c)
  let mono ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let e ← mkAppOptM p (#[some M, some A, some mono, some S, some hS, some c] ++
    extra.map some ++ #[some hint])
  let (mvs, _, _) ← forallMetaTelescope (← inferType e)
  let pf := mkAppN e mvs
  let ty ← inferType pf
  unless ← isDefEq ty (← g.getType) do
    throwError "taint summaries: {ty} does not match the goal {← g.getType}"
  g.assign pf
  let m₁ :: m₂ :: ms := mvs.toList | throwError "taint summaries: unexpected {p}"
  setGoals [m₁.mvarId!]
  evalTactic (← `(tactic| lit_decide))
  setGoals [m₂.mvarId!]
  fillRfl
  -- `keepsSum`, for a summary: nothing to check for `bot`.
  for m in ms do
    setGoals [m.mvarId!]
    if extra.back?.any (·.isAppOf ``Taint.Frame.bot) then
      evalTactic (← `(tactic| exact Taint.keepsSum_bot))
    else
      evalTactic (← `(tactic| lit_decide))

end TaintSum

open Lean Meta Elab Tactic TaintSum in
/-- `taint_decide_sum [l₁, …]` proves `∃ h, (Taint.check A τ c h).isSome = true`
like `taint_decide`, but with the summaries `lᵢ : Taint.SumOk A (code, pre, post, F)`
(`taint_summary`) in place of the analysis of each call that one of them
applies to (the first call of the same name, from at least `pre` public). -/
elab "taint_decide_sum " "[" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, body) := ty.app2? ``Exists
    | throwError "taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let .lam _ _ b _ := body
    | throwError "taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let some chk := b.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "taint_decide_sum: the goal is not `∃ h, (Taint.check A τ c h).isSome = true`"
  let args := chk.getAppArgs
  let (M, A, τ, c) := (args[0]!, args[1]!, args[2]!, args[3]!)
  let names ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS) ← summaries M A names
  proveWith M A S hS τ c ``Taint.exists_check_of_checkSum #[τ]

open Lean Meta Elab Term Tactic TaintSum in
/-- The theorem `N : Taint.SumOk A (c, τ, post)` of `taint_summary`. -/
def TaintSum.summaryCmd (id : Ident) (a τ c : Term) (f : Option Term) (ls : Array Ident) :
    TermElabM Unit := do
  let A ← instantiateMVars (← elabTerm a none)
  let aTy ← whnf (← inferType A)
  unless aTy.isAppOfArity ``Taint 1 do throwError "taint_summary: {A} is not a `Taint`"
  let M := aTy.appArg!
  let T := mkApp2 (mkConst ``Taint.T) M A
  let τ ← elabTermEnsuringType τ T
  let c ← elabTermEnsuringType c (mkApp (mkConst ``Prog) M)
  let fr ← synthInstance (mkApp2 (mkConst ``Taint.Frame) M A)
  let F ← match f with
    | some f => elabTermEnsuringType f T
    | none => pure (mkApp3 (mkConst ``Taint.Frame.bot) M A fr)
  synthesizeSyntheticMVarsNoPostponing
  let τ ← instantiateMVars τ
  let c ← instantiateMVars c
  let F ← instantiateMVars F
  if τ.hasMVar || c.hasMVar || F.hasMVar then
    throwError "taint_summary: the taints and the code must be closed"
  let names ← ls.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let (S, hS) ← summaries M A names
  let post ← evalToExpr (← whnfD T) (mkApp6 (mkConst ``Taint.postSumOf) M A fr S τ c)
  let s ← mkAppM ``Prod.mk #[c, ← mkAppM ``Prod.mk #[τ, ← mkAppM ``Prod.mk #[post, F]]]
  let ty := mkApp3 (mkConst ``Taint.SumOk) M A s
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let gs ← Tactic.run mv.mvarId! (proveWith M A S hS τ c ``Taint.sumOk_of_checkSum #[τ, post, F])
  unless gs.isEmpty do throwError "taint_summary: goals remain"
  let v ← instantiateMVars mv
  addDecl <| .thmDecl
    { name := (← getCurrNamespace) ++ id.getId, levelParams := [], type := ty, value := v }

/-- `taint_summary N : A τ code keeping F using l₁ …` proves the summary
`N : Taint.SumOk A (code, τ, post, F)`, with `post` what the analysis of
`code` from `τ` ends with, and `F` what `code` does not write (`Frame.keeps`,
by default nothing), by evaluation (`lit_decide`), with the summaries `lᵢ` in
place of the calls they apply to (as `taint_decide_sum`). -/
syntax "taint_summary " ident " : " term:max term:max term:max (" keeping " term:max)?
  (" using " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(taint_summary $id : $a $τ $c $[keeping $f]? $[using $ls*]?) =>
    liftTermElabM (TaintSum.summaryCmd id a τ c f (ls.getD #[]))

end VG
