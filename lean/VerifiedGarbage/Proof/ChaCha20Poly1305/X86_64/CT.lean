import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Correct
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# ChaCha20-Poly1305 on x86-64: constant time

Untrusted: everything here is checked by Lean. `seal` and `open` call an
implementation of `vg_chacha20_xor` that the proof does not know, so the
taint analysis cannot follow them into it. The code before the call and the
code after it are checked by the taint analysis; the call is constant time
by the implementation's own proof (`RelCT.callEx`), since its arguments,
which correctness determines (`XArgs`), agree in two runs; and after it,
correctness says again where `rsi` points (`After`), from which the rest is
checked.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64

/-- The public registers and what is known about memory on entry: the lengths
of the context and the data (the data's varies) and the registers holding
their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [1024, 0],
    bases := [(.rdi, 0, 0), (.rcx, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : preX86_64 s₁) (h₂ : preX86_64 s₂) (hpub : pubX86_64 s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, preX86_64 s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, -, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d], by simp [hw, (s.gpr .r8).isLt.le]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p4, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-! ## The code around the call -/

/-- `seal` up to the call of `vg_chacha20_xor`. -/
def sealPre : Prog isa :=
  .seq prologue (.seq (macPad .rbx .rbp) (.seq (.block lengths) (.block cryptArgs)))

/-- `seal` after the call of `vg_chacha20_xor`. -/
def sealPost : Prog isa :=
  .seq (.block (anchor .rsi 128))
    (.seq (macPad .r14 .r13) (.seq absorbLengths (.seq (finalizeTo 48) (.block restore))))

/-- `open` up to the call of `vg_chacha20_xor`. -/
def openPre : Prog isa :=
  .seq prologue (.seq (macPad .rbx .rbp) (.seq (macPad .r14 .r13) (.seq (.block lengths)
    (.seq absorbLengths (.block cryptArgs)))))

/-- `open` after the call of `vg_chacha20_xor`. -/
def openPost : Prog isa :=
  .seq (.block (anchor .rsi 128)) (.seq (finalizeTo 640) (.block (compare ++ restore)))

theorem seal_exec {x : Impl.ChaCha20.X86_64.Callee} {s s' : State} {t : List Leak}
    (h : Exec isa («seal» x) s t s') : Exec isa (.seq sealPre (.seq (.call x.name x.code) sealPost)) s t s' := by
  cases h with | seq e₁ h => cases h with | seq e₂ h => cases h with | seq e₃ h => cases h with | seq h e₆ =>
  cases h with | seq e₄ h => cases h with | seq c e₅ =>
  have := Exec.seq (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄))) (Exec.seq c (Exec.seq e₅ e₆))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem open_exec {x : Impl.ChaCha20.X86_64.Callee} {s s' : State} {t : List Leak}
    (h : Exec isa («open» x) s t s') : Exec isa (.seq openPre (.seq (.call x.name x.code) openPost)) s t s' := by
  cases h with | seq e₁ h => cases h with | seq e₂ h => cases h with | seq e₃ h => cases h with | seq e₄ h =>
  cases h with | seq e₅ h => cases h with | seq h e₈ => cases h with | seq e₆ h => cases h with | seq c e₇ =>
  have := Exec.seq (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))))
    (Exec.seq c (Exec.seq e₇ e₈))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem RelCT.of_exec {P Q : State → State → Prop} {c c' : Prog isa}
    (he : ∀ {s t s'}, Exec isa c s t s' → Exec isa c' s t s') (h : RelCT isa P c' Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (he e₁) (he e₂)

theorem sealPre_ok {s₀ : State} (hp : APre s₀) : WP isa sealPre s₀ (XArgs s₀) := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  exact WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun _ ⟨i₃, _⟩ => cryptArgs_ok hp i₃)

theorem openPre_ok {s₀ : State} (hp : APre s₀) : WP isa openPre s₀ (XArgs s₀) := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (macPad_ok hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₂.r15
    i₂.rsp i₂.rd i₂.wr i₂.r14 (by rw [i₂.r13]; exact hL s₀))
    fun s₃ ⟨cs₃, rd₃, wr₃, f₃, _⟩ => ?_)
  have i₃ := mac_inv hp i₂ cs₃ rd₃ wr₃ f₃
  refine WP.seq (WP.mono (lengths_ok hp i₃ (by rw [cs₃ _ (by simp [calleeSaved]),
    cs₂ _ (by simp [calleeSaved]), h₁.rbp])) fun s₄ ⟨i₄, _⟩ => ?_)
  exact WP.seq (WP.mono (absorbLengths_ok hp i₄) fun _ ⟨i₅, _⟩ => cryptArgs_ok hp i₅)

/-! ## After the call -/

/-- What is known after the call of `vg_chacha20_xor`, in one run. -/
structure After (s₀ s : State) : Prop where
  rsi : s.gpr .rsi = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r8
  r14 : s.gpr .r14 = dp s₀
  wr : s.wr = s₀.wr

/-- The taint after the call: `rsi` points at `ctx + 128`, and the lengths of
the regions are those on entry. -/
def τ₁ : X86_64.Taint.T :=
  { regs := .ofList [.rsi, .rsp, .r13, .r14], flags := false, lens := [1024, 0], bases := [(.rsi, 0, 128)] }

section
variable {s₀ s₀' : State} (hp : APre s₀) (hp' : APre s₀') (hq : pubX86_64 s₀ s₀')

omit hp' in
include hp in
theorem After.wf {s : State} (h : After s₀ s) : X86_64.Taint.Wf τ₁ s := by
  have hw : s.wr = [ctxR s₀, dR s₀] := by rw [h.wr, hp.wr]
  refine ⟨fun _ => ⟨by simp [hw, τ₁], by simp [hw, hp.c_d], by simp [hw, (s₀.gpr .r8).isLt.le]⟩, fun p hm => ?_⟩
  simp only [τ₁, List.mem_singleton] at hm
  subst hm
  simp [X86_64.Taint.region, hw, h.rsi, off_eq]

include hp hp' hq in
theorem agree₁ {s₁ s₂ : State} (h₁ : After s₀ s₁) (h₂ : After s₀' s₂) : X86_64.Taint.Agree τ₁ s₁ s₂ := by
  obtain ⟨p1, -, -, p4, p5, p6⟩ := hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τ₁, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.rsi, h₂.rsi, cx, cx, p1]
    · rw [h₁.rsp, h₂.rsp, p6]
    · rw [h₁.r13, h₂.r13, p5]
    · rw [h₁.r14, h₂.r14, dp, dp, p4]
  · rw [h₁.wr, h₂.wr, hp.wr, hp'.wr, ctxR, ctxR, dR, dR, cx, cx, dp, dp, L, L, p1, p4, p5]
  · intro sl h; simp [τ₁] at h
  · intro sl h; simp [τ₁] at h

include hp hp' hq in
/-- The call of any implementation `v` of `vg_chacha20_xor`. -/
theorem call_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun s₁ s₂ => XArgs s₀ s₁ ∧ XArgs s₀' s₂) (.call v.callee.name v.callee.code)
      fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  obtain ⟨p1, -, -, p4, p5, p6⟩ := hq
  have ct := RelCT.callEx (n := v.callee.name) (P := fun s₁ s₂ => XArgs s₀ s₁ ∧ XArgs s₀' s₂) v.ok v.ct fun s₁ s₂ ⟨a₁, a₂⟩ =>
    ⟨[], _, [], _, a₁.pre hp v, a₂.pre hp' v, by
      simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.rsp, a₂.rdi,
        a₂.rsi, a₂.rdx, a₂.rcx, a₂.rsp, cx, dp, p1, p4, p5, p6]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩,
      covers_nil_append (covers_left _ (a₁.hw hp)), a₁.hw hp, covers_nil_append (covers_left _ (a₂.hw hp')),
      a₂.hw hp', by rw [a₁.rsp, a₂.rsp, p6]⟩
  have after : ∀ {σ₀ s : State}, APre σ₀ → XArgs σ₀ s →
      WP isa (.call v.callee.name v.callee.code) s (After σ₀) := fun hp a =>
    a.call hp v fun _ _ wr cs _ rsi _ =>
      ⟨rsi, by rw [cs _ calleeSaved_rsp, a.rsp], by rw [cs _ (by simp [calleeSaved]), a.r13],
        by rw [cs _ (by simp [calleeSaved]), a.r14], by rw [wr, a.wr]⟩
  exact (ct.wp fun _ _ h => ⟨after hp h.1, after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end

/-! ## `seal` and `open` -/

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (h₀ : preX86_64 s₀) (h₀' : preX86_64 s₀')
  (hq : pubX86_64 s₀ s₀')
include h₀ h₀' hq

theorem seal_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have pre := ((RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') τ₀ (fun _ _ h => h.1 ▸ h.2 ▸ agree₀ h₀ h₀' hq) (c := sealPre)
    (by taint_decide)).wp (F₁ := XArgs s₀) (F₂ := XArgs s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact sealPre_ok hp, by rw [h.2]; exact sealPre_ok hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have post := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) τ₁ (fun _ _ h => agree₁ hp hp' hq h.1 h.2) (c := sealPost)
    (by taint_decide)
  exact RelCT.of_exec seal_exec (pre.seq ((call_rel hp hp' hq v).seq post))

theorem open_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have pre := ((RelCT.taint (A := taint) (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') τ₀ (fun _ _ h => h.1 ▸ h.2 ▸ agree₀ h₀ h₀' hq) (c := openPre)
    (by taint_decide)).wp (F₁ := XArgs s₀) (F₂ := XArgs s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact openPre_ok hp, by rw [h.2]; exact openPre_ok hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have post := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) τ₁ (fun _ _ h => agree₁ hp hp' hq h.1 h.2) (c := openPost)
    (by taint_decide)
  exact RelCT.of_exec open_exec (pre.seq ((call_rel hp hp' hq v).seq post))

end

end VG.Proof.ChaCha20Poly1305.X86_64
