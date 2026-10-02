import VerifiedGarbage.Proof.MlDsa.X86.Message.Args
import VerifiedGarbage.Proof.MlKem.X86.CallRet

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: calls, correct and constant time

Untrusted: everything here is checked by Lean. The body is proven piece by
piece (`Piece`, `Proof/MlKem/X86/Piece.lean`) from the entry state `s₀` of
each run, with the layout `lay s₀`. Two runs whose entry states are related
by the contract's public data have layouts with the same public data
(`PubL`): the stack pointer, the arguments and the 1 KiB. In the body
(`CtxO`), the moves of a call's arguments (`setArgs_piece`) are checked by
the taint analysis, their addresses depending only on `esp` and `esi`; and a
call with them (`argsRet_piece`, `argsWith_piece`) is constant time when
correctness determines its arguments from public data.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlKem.X86 (Only Piece P0)

/-- Two layouts with the same public data. -/
structure PubL (L L' : Lay) : Prop where
  sp : L.SP = L'.SP
  argv : L.argv = L'.argv
  x : L.X32 = L'.X32
  nA : L.nA = L'.nA
  key : L.key = L'.key
  msg : L.msg = L'.msg
  len : L.len = L'.len
  ctx : L.ctx = L'.ctx
  ctxLen : L.ctxLen = L'.ctxLen

/-- In the body of the leaf, from the entry state `s₀`, with the layout `lay s₀`. -/
structure CtxO (lay : State → Lay) (s₀ s : State) : Prop where
  ok : (lay s₀).Ok
  ctx : Ctx (lay s₀) (P0 s₀).mem s

/-- The moves of the arguments `as` from `s` to `s₁`. -/
def SetPost (as : List (Reg × Arg)) (s s₁ : State) : Prop :=
  (∀ da ∈ as, s₁.gpr da.1 = da.2.val s) ∧ Only (as.map (·.1)) s s₁

theorem argsOk_regs {n : Nat} : ∀ {as : List (Reg × Arg)}, argsOk n as = true →
    ∀ r ∈ as.map (·.1), r ≠ .esp ∧ r ≠ .esi
  | [], _, _, h => by simp at h
  | (d, a) :: as, h, r, hr => by
    simp only [argsOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨h.1.1.1.2, h.1.1.2⟩
    · exact argsOk_regs h.2 r hr

theorem SetPost.esp {n : Nat} {as : List (Reg × Arg)} (ho : argsOk n as = true) {s s₁ : State}
    (h : SetPost as s s₁) : s₁.gpr .esp = s.gpr .esp :=
  h.2.gpr _ fun hm => (argsOk_regs ho _ hm).1 rfl

theorem SetPost.esi {n : Nat} {as : List (Reg × Arg)} (ho : argsOk n as = true) {s s₁ : State}
    (h : SetPost as s s₁) : s₁.gpr .esi = s.gpr .esi :=
  h.2.gpr _ fun hm => (argsOk_regs ho _ hm).2 rfl

/-- The value of an argument but `eax` is public. -/
theorem Arg.val_pub {L L' : Lay} {m m' : Mem} {s s' : State} (hc : Ctx L m s) (hc' : Ctx L' m' s')
    (hp : PubL L L') {a : Arg} (ha : a.ok L.nA = true) (hr : a.isRet = false) : a.val s = a.val s' := by
  cases a with
  | arg i =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    rw [hc.argV ha, hc'.argV (hp.nA ▸ ha), hp.argv]
  | argOff i o =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    rw [hc.argOffV ha, hc'.argOffV (hp.nA ▸ ha), hp.argv]
  | off o => rw [hc.off, hc'.off, hp.x]
  | imm v => rfl
  | ret => simp [Arg.isRet] at hr

/-- Registers set by the moves of two runs agree, if the values do. -/
theorem SetPost.agree {as : List (Reg × Arg)} {s s' s₁ s₁' : State} (h : SetPost as s s₁)
    (h' : SetPost as s' s₁') (hv : ∀ da ∈ as, da.2.val s = da.2.val s') {r : Reg} {a : Arg}
    (hr : (r, a) ∈ as) : s₁.gpr r = s₁'.gpr r := by
  rw [h.1 _ hr, h'.1 _ hr]; exact hv _ hr

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {A B : State → State → Prop}

/-- The moves of a call's arguments. -/
theorem setArgs_piece (as : List (Reg × Arg)) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA as = true) :
    Piece Pre Pub A (fun s₀ s₁ => ∃ s, A s₀ s ∧ SetPost as s s₁) (.block (setArgs as)) :=
  Piece.taint [.esp, .esi] (fun s₀ s h₀ ha => by
      have h := hA s₀ s h₀ ha
      exact (setArgs_ok as (hok s₀ h₀) s (h.ctx.aOk h.ok)).mono fun s₁ h₁ => ⟨s, ha, h₁⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq ha ha' r hr => by
      have h := hA s₀ s h₀ ha
      have h' := hA s₀' s' h₀' ha'
      have hp := hpub s₀ s₀' h₀ h₀' hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.ctx.esp, h'.ctx.esp, Lay.E1, Lay.E1, hp.sp]
      · rw [h.ctx.esi, h'.ctx.esi, hp.x]) tt

/-- A call of verified code, returning a value in `eax`, with the arguments `as`. -/
theorem argsRet_piece {as : List (Reg × Arg)} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA as = true)
    (rd wr : State → List Region)
    (hrw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀')
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (lay s₀).E1.toNat)
    (hk : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost as s s₁ → CallPre k rs (rd s₀) (wr s₀) s₁)
    (hkp : ∀ s₀ s₀' s s' s₁ s₁', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      SetPost as s s₁ → SetPost as s' s₁' →
      k.pub ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s₁').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s₁ s', Pre s₀ → A s₀ s → SetPost as s s₁ → s'.rd = s₁.rd → s'.wr = s₁.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r) →
      Frame (wr s₀ ++ [below (s₁.gpr .esp) (4 * rs.length + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.seq (.block (setArgs as)) (Impl.MlKem.X86.callRet rs n c)) := by
  refine Piece.seq (setArgs_piece as tt hpub hA hok) (Piece.callRet hv hct hsp hne hrs rd wr ?_ ?_ ?_ ?_)
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]
    exact hd s₀ s h₀ ha
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    exact hk s₀ s s₁ h₀ ha hs
  · rintro s₀ s₀' s₁ s₁' h₀ h₀' hq ⟨s, ha, hs⟩ ⟨s', ha', hs'⟩
    obtain ⟨e₁, e₂⟩ := hrw s₀ s₀' h₀ h₀' hq
    refine ⟨e₁, e₂, ?_, hkp s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs'⟩
    rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
      Lay.E1, Lay.E1, (hpub s₀ s₀' h₀ h₀' hq).sp]
  · rintro s₀ s₁ s' h₀ ⟨s, ha, hs⟩ e₁ e₂ e₃ fr post
    exact hQ s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post

/-- A call of verified code, popping its frame into `eax`, with the arguments `as`. -/
theorem argsWith_piece {as : List (Reg × Arg)} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs as)) ht).isSome = true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hok : ∀ s₀, Pre s₀ → argsOk (lay s₀).nA as = true)
    (rd wr : State → List Region)
    (hrw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀')
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (lay s₀).E1.toNat)
    (hk : ∀ s₀ s s₁, Pre s₀ → A s₀ s → SetPost as s s₁ → CallPre k rs (rd s₀) (wr s₀) s₁)
    (hkp : ∀ s₀ s₀' s s' s₁ s₁', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      SetPost as s s₁ → SetPost as s' s₁' →
      k.pub ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s₁').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s₁ s', Pre s₀ → A s₀ s → SetPost as s s₁ → s'.rd = s₁.rd → s'.wr = s₁.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s₁.gpr r) →
      Frame (wr s₀ ++ [below (s₁.gpr .esp) (4 * rs.length + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧
        k.post ((pushed rs s₁).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.seq (.block (setArgs as)) (Impl.MlKem.X86.callWith rs n c)) := by
  refine Piece.seq (setArgs_piece as tt hpub hA hok) (Piece.callWith hv hct hsp hne hrs rd wr ?_ ?_ ?_ ?_)
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    rw [hs.esp (hok s₀ h₀), (hA s₀ s h₀ ha).ctx.esp]
    exact hd s₀ s h₀ ha
  · rintro s₀ s₁ h₀ ⟨s, ha, hs⟩
    exact hk s₀ s s₁ h₀ ha hs
  · rintro s₀ s₀' s₁ s₁' h₀ h₀' hq ⟨s, ha, hs⟩ ⟨s', ha', hs'⟩
    obtain ⟨e₁, e₂⟩ := hrw s₀ s₀' h₀ h₀' hq
    refine ⟨e₁, e₂, ?_, hkp s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs'⟩
    rw [hs.esp (hok s₀ h₀), hs'.esp (hok s₀' h₀'), (hA s₀ s h₀ ha).ctx.esp, (hA s₀' s' h₀' ha').ctx.esp,
      Lay.E1, Lay.E1, (hpub s₀ s₀' h₀ h₀' hq).sp]
  · rintro s₀ s₁ s' h₀ ⟨s, ha, hs⟩ e₁ e₂ e₃ fr post
    exact hQ s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post

end

end VG.Proof.MlDsa.X86.Message
