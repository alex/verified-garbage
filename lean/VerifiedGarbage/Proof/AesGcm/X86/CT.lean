import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# AES-GCM on x86: constant time, piece by piece

Untrusted: everything here is checked by Lean.

`CT I c`: any two runs of `c` from states satisfying `I` leak the same
trace. The AES-GCM pieces are proven constant time from their (public)
preconditions: every precondition of a piece is about public values (the
pointers, the lengths, `esp`), and what a piece computes from secrets is
stated in its postcondition as an implication from the memory it started
from, so the same `I` holds of both runs. The pieces are put together as the
code is (`CT.seq` takes the precondition of the second piece from the
correctness of the first, by determinism; `CT.ite` a condition that `I`
determines); straight-line code and loops without calls are proven by the
taint analysis, from the registers `I` pins (`CT.taint`), and each call in a
frame of its arguments by the callee's own proof (`CT.callWith`).
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86

/-- Two runs of `c` from states satisfying `I` leak the same trace. -/
def CT (I : State → Prop) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => I s₁ ∧ I s₂) c fun _ _ => True

namespace CT

theorem mono {I I' : State → Prop} {c : Prog isa} (h : CT I c) (hi : ∀ s, I' s → I s) : CT I' c :=
  RelCT.mono h (fun _ _ h => ⟨hi _ h.1, hi _ h.2⟩) fun _ _ _ => trivial

theorem seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : CT I c₁) (hw : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT J c₂) : CT I (.seq c₁ c₂) :=
  have h₁' : RelCT isa (fun a b => I a ∧ I b) c₁ fun a b => J a ∧ J b :=
    RelCT.mono (RelCT.wp h₁ (F₁ := J) (F₂ := J) fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩) (fun _ _ h => h)
      fun _ _ h => h.2
  RelCT.seq h₁' h₂

theorem ite {I : State → Prop} {c : Cond} {t e : Prog isa} (b : Bool)
    (hc : ∀ s, I s → isa.eval c s = some b) (ht : b = true → CT I t) (he : b = false → CT I e) :
    CT I (.ite c t e) := by
  refine RelCT.ite (fun s₁ s₂ h => by rw [hc _ h.1, hc _ h.2]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun s₁ _ h => by rw [hc _ h.1.1] at h; simp at h
    · exact RelCT.mono (ht rfl) (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact RelCT.mono (he rfl) (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun s₁ _ h => by rw [hc _ h.1.1] at h; simp at h

/-- Code the taint analysis proves constant time from the registers `rs`, on
which any two states satisfying `I` agree. -/
theorem taint {I : State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) c hc).isSome = true) : CT I c :=
  RelCT.taint (A := VG.X86.taint) (τr rs) (fun _ _ hp => agree_regs (hr _ _ hp.1 hp.2)) h

/-- A call of verified code in a frame of its arguments. -/
theorem callWith {I : State → Prop} {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : List Region)
    (hP : ∀ s₁ s₂, I s₁ → I s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    CT I (.frame (.push rs) (.call n c) (.pop .eax rs.length)) :=
  RelCT.callWith hv hct rd wr fun _ _ h => hP _ _ h.1 h.2

theorem nil {I : State → Prop} : CT I (.block []) := RelCT.nil fun _ _ _ => trivial

/-- Cases on a public value. -/
theorem cases {α : Sort _} {I : α → State → Prop} {c : Prog isa} (h : ∀ a, CT (I a) c)
    (hu : ∀ a b s₁ s₂, I a s₁ → I b s₂ → a = b) : CT (fun s => ∃ a, I a s) c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨a, h₁⟩, ⟨b, h₂⟩⟩ e₁ e₂
  obtain rfl := hu a b s₁ s₂ h₁ h₂
  exact h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

end CT

/-- Constant time of a whole function, from `CT` for each value of what is
public (`f`). -/
theorem CT.constantTime {α : Sort _} {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa}
    (f : State → α) (hf : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → f s₁ = f s₂)
    (h : ∀ a, CT (fun s => Pre s ∧ f s = a) c) : ConstantTime isa Pre Pub c :=
  fun s₁ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (h (f s₁) _ _ _ _ _ _ ⟨⟨h₁, rfl⟩, ⟨h₂, (hf _ _ h₁ h₂ hp).symm⟩⟩ e₁ e₂).1

/-! ## Pieces: correctness and constant time together

`Pc P c Q`: from a state satisfying `P a`, `c` ends in one satisfying `Q a`,
and any two runs from states satisfying `P a` and `P b` leak the same
trace. The index `a` is what is secret about the run (the memory it starts
from, say): it may differ between the two runs; everything `P` says of the
registers the code branches on or addresses memory with must not depend on
it. -/

structure Pc {α : Sort _} (P : α → State → Prop) (c : Prog isa) (Q : α → State → Prop) : Prop where
  wp : ∀ a s, P a s → WP isa c s (Q a)
  ct : CT (fun s => ∃ a, P a s) c

namespace Pc

variable {α : Sort _}

theorem mono {P P' Q Q' : α → State → Prop} {c : Prog isa} (h : Pc P c Q) (hp : ∀ a s, P' a s → P a s)
    (hq : ∀ a s, Q a s → Q' a s) : Pc P' c Q' :=
  ⟨fun a s hs => WP.mono (h.wp a s (hp a s hs)) (hq a), h.ct.mono fun _ ⟨a, h⟩ => ⟨a, hp a _ h⟩⟩

theorem seq {P Q R : α → State → Prop} {c₁ c₂ : Prog isa} (h₁ : Pc P c₁ Q) (h₂ : Pc Q c₂ R) :
    Pc P (.seq c₁ c₂) R :=
  ⟨fun a s hs => WP.seq (WP.mono (h₁.wp a s hs) fun s' h => h₂.wp a s' h),
    CT.seq h₁.ct (fun _ ⟨a, h⟩ => WP.mono (h₁.wp a _ h) fun _ h => ⟨a, h⟩) h₂.ct⟩

/-- A piece proven on its own, with a precondition `I` that `P` implies and a
postcondition relating the states before and after. -/
theorem of {I : State → Prop} {R : State → State → Prop} {c : Prog isa}
    (hw : ∀ s, I s → WP isa c s (R s)) (hct : CT I c) (P : α → State → Prop) (hP : ∀ a s, P a s → I s) :
    Pc P c fun a s' => ∃ s, P a s ∧ R s s' :=
  ⟨fun a s hs => WP.mono (hw s (hP a s hs)) fun _ h => ⟨s, hs, h⟩,
    hct.mono fun _ ⟨a, h⟩ => hP a _ h⟩

/-- A branch on a condition that `P` determines. -/
theorem ite {P Q : α → State → Prop} {c : Cond} {t e : Prog isa} (b : Bool)
    (hc : ∀ a s, P a s → isa.eval c s = some b) (ht : b = true → Pc P t Q) (he : b = false → Pc P e Q) :
    Pc P (.ite c t e) Q := by
  refine ⟨fun a s hs => WP.ite b (hc a s hs) (fun h => (ht h).wp a s hs) (fun h => (he h).wp a s hs), ?_⟩
  exact CT.ite b (fun s ⟨a, h⟩ => hc a s h) (fun h => (ht h).ct) (fun h => (he h).ct)

/-- Code the taint analysis proves constant time from the registers `rs`, on
which `P` pins the same values whatever the index. -/
theorem taint {P Q : α → State → Prop} {c : Prog isa} (rs : List Reg) (hw : ∀ a s, P a s → WP isa c s (Q a))
    (hr : ∀ a b s₁ s₂, P a s₁ → P b s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) c hc).isSome = true) : Pc P c Q :=
  ⟨hw, CT.taint rs (fun _ _ ⟨a, h₁⟩ ⟨b, h₂⟩ => hr a b _ _ h₁ h₂) h⟩

theorem nil {P : α → State → Prop} : Pc P (.block []) P :=
  ⟨fun _ _ h => WP.block_nil h, CT.nil⟩

/-- A piece indexed by `α`, in code indexed by `β`: the index of the piece
from that of the code and the state it starts in. Its postcondition holds
of the state the piece started in, which has the permissions of the one it
ends in. -/
theorem lift {β : Sort _} {P : α → State → Prop} {Q : α → State → Prop} {c : Prog isa} (h : Pc P c Q)
    {P' : β → State → Prop} (f : β → State → α) (hP : ∀ b s, P' b s → P (f b s) s) :
    Pc P' c fun b s' => ∃ s, P' b s ∧ Q (f b s) s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨fun b s hs => ?_, h.ct.mono fun s ⟨b, hb⟩ => ⟨f b s, hP b s hb⟩⟩
  obtain ⟨t, s', he, hq⟩ := h.wp _ s (hP b s hs)
  exact ⟨t, s', he, s, hs, hq, Exec.rdwr he⟩

/-- Correctness and constant time of a whole function. -/
theorem constantTime {β : Sort _} {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa}
    {P : β → State → State → Prop} {Q : β → State → State → Prop} (f : State → β)
    (hf : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → f s₁ = f s₂) (h : ∀ p, Pc (P p) c (Q p))
    (hp : ∀ s, Pre s → P (f s) s s) : ConstantTime isa Pre Pub c :=
  CT.constantTime f hf fun p => (h p).ct.mono fun s ⟨h₁, h₂⟩ => ⟨s, h₂ ▸ hp s h₁⟩

end Pc

end VG.Proof.AesGcm.X86
