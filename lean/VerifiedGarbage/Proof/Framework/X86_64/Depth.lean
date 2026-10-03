import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-!
# Stack depth (x86-64)

How much stack below `rsp` code uses at once (`Code.x86_64Depth`), in bytes:
its frames, of registers (`push`) or of buffers (`alloc`), and the return
addresses of its calls. Code whose instructions never write `rsp` but as the
pushes and pops of its frames (`SpSafe`, what `Artifact.spSafe` checks)
keeps `rsp` (`Exec.rsp`), and changes memory only within the regions it may
write and that many bytes below `rsp` (`Exec.stackFrame`), as
`Exec.frameSp` says of code without frames.
-/

namespace VG

/-- The bytes of stack a frame's push takes. -/
def X86_64.Instr.frameBytes : X86_64.Instr → Nat
  | .push rs => 8 * rs.length
  | .alloc bytes => bytes
  | _ => 0

/-- The most stack below `rsp` that `c` uses at once, in bytes. -/
def Code.x86_64Depth : Prog X86_64.isa → Nat
  | .block _ => 0
  | .seq a b => max a.x86_64Depth b.x86_64Depth
  | .ite _ t e => max t.x86_64Depth e.x86_64Depth
  | .loop b _ => b.x86_64Depth
  | .call _ b => b.x86_64Depth + 8
  | .frame i b _ => b.x86_64Depth + i.frameBytes

/-- `Code.all p` holds of every instruction. -/
theorem Code.all_instrs {I C : Type} {p : I → Bool} {c : Code I C} (h : c.all p = true) :
    ∀ i ∈ instrs c, p i = true := by
  induction c with
  | block is => simpa [Code.all, instrs, List.all_eq_true] using h
  | seq a b iha ihb =>
    simp only [Code.all, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    exacts [iha h.1 i hi, ihb h.2 i hi]
  | ite _ t e iht ihe =>
    simp only [Code.all, Bool.and_eq_true] at h
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    exacts [iht h.1 i hi, ihe h.2 i hi]
  | loop b _ ih => exact ih h
  | call _ b ih => exact ih h
  | frame x b y ih =>
    simp only [Code.all, Bool.and_eq_true] at h
    intro i hi
    simp only [instrs, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | hi | rfl
    exacts [h.1.1, ih h.1.2 i hi, h.2]

end VG

namespace VG.X86_64

/-- Code whose instructions never write `rsp`, but as the pushes and pops of
its frames. -/
abbrev SpSafe (c : Prog isa) : Prop := ∀ i ∈ instrs c, isa.writesSp i = false

theorem SpSafe.of_all {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) : SpSafe c :=
  fun i hi => by simpa using Code.all_instrs h i hi

/-- An instruction that does not write `rsp` keeps it. -/
theorem exec_rsp {i : Instr} {s s' : State} (hw : isa.writesSp i = false) (h : exec i s = some s') :
    s'.gpr .rsp = s.gpr .rsp := by
  refine exec_gpr ?_ h
  cases i <;> first
    | (simp only [exec, reduceCtorEq] at h; done)
    | (simp only [Instr.dst, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        reduceCtorEq, Option.some.injEq] at hw
       simp only [Taint.clobbers, Taint.dstOf, Bool.or_eq_false_iff,
         beq_eq_false_iff_ne, ne_eq, reduceCtorEq, Option.some.injEq]
       first | exact hw | exact ⟨fun h => hw.1 h.symm, fun h => hw.2 h.symm⟩ | decide)

/-- A frame restores `rsp`. -/
theorem frame_rsp {i j : Instr} {s s₁ s₂ s' : State} (hp : isa.push i s = some s₁)
    (hq : isa.pop j s₁ s₂ = some s') (hb : s₂.gpr .rsp = s₁.gpr .rsp) : s'.gpr .rsp = s.gpr .rsp := by
  obtain ⟨k, -, w₁, -, e₁⟩ := push_eq hp
  obtain ⟨-, -, -, -, -, k', h₃, e₃⟩ := pop_eq hq
  rw [w₁] at h₃
  simp only [List.head?_cons, Option.some.injEq, Region.mk.injEq] at h₃
  have : k = k' := by omega
  subst this
  rw [e₃, hb, e₁, BitVec.sub_add_cancel]

/-- Code that writes `rsp` only in its frames keeps it. -/
theorem Exec.rsp {c : Prog isa} (hc : SpSafe c) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : s'.gpr .rsp = s.gpr .rsp :=
  Exec.keep (fun s : State => s.gpr .rsp) (ok := fun i => isa.writesSp i = false)
    (fun hi he => exec_rsp hi he) (fun _ hp hq hb => frame_rsp hp hq hb) hc
    (.inr fun _ _ _ _ hc hr hb => call_ret_gpr hc hr hb) h

/-- A frame's push takes `i.frameBytes` bytes below `rsp`, which become the
head of the writable regions, and stores only within them. -/
theorem push_frame {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    s₁.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 i.frameBytes ∧
      s₁.wr = ⟨s₁.gpr .rsp, i.frameBytes⟩ :: s.wr ∧ i.frameBytes ≤ (s.gpr .rsp).toNat ∧
      Frame [below (s.gpr .rsp) i.frameBytes] s.mem s₁.mem := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case push rs =>
    split at h <;> cases h
    rename_i hc
    obtain ⟨-, -, h₃, -⟩ := pushRegs_eq s rs
    exact ⟨h₃, by simp only [Instr.frameBytes]; rw [h₃], hc.2.2, (pushRegs_mem s rs hc.2.1 hc.2.2).1⟩
  case alloc bytes =>
    split at h <;> cases h
    rename_i hc
    refine ⟨?_, ?_, hc.2.2.2, Frame.refl _ _⟩ <;> simp [State.setReg, Instr.frameBytes]

/-- A frame's pop changes no memory. -/
theorem pop_mem {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mem = s₂.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case pop => split at h <;> cases h; exact popReg_mem _ _ _
  case free => split at h <;> cases h; rfl

/-- The stack below `sp - a`, within the stack below `sp`. -/
theorem below_below (sp : Addr) (a n : Nat) : Region.Sub (below (sp - BitVec.ofNat 64 a) n) (below sp (n + a)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (n + a)) = x - (sp - BitVec.ofNat 64 a - BitVec.ofNat 64 n) by
    rw [BitVec.sub_sub sp, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 n)]]
  omega

/-- Code that writes `rsp` only in its frames changes memory only within the
regions it may write, and within `c.x86_64Depth` bytes below `rsp` (its
frames and its calls' return addresses). -/
theorem Exec.stackFrame {c : Prog isa} (hc : SpSafe c) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hd : c.x86_64Depth < 2 ^ 64) :
    Frame (s.wr ++ [below (s.gpr .rsp) c.x86_64Depth]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    have hc₁ : SpSafe c₁ := fun i hi => hc i (List.mem_append_left _ hi)
    have hc₂ : SpSafe c₂ := fun i hi => hc i (List.mem_append_right _ hi)
    simp only [Code.x86_64Depth] at hd ⊢
    have f₁ := Frame.below_mono (ih₁ hc₁ (by omega)) (b := max c₁.x86_64Depth c₂.x86_64Depth)
      (by omega) (by omega)
    have f₂ := Frame.below_mono (ih₂ hc₂ (by omega)) (b := max c₁.x86_64Depth c₂.x86_64Depth)
      (by omega) (by omega)
    rw [(Exec.rdwr h₁).2, Exec.rsp hc₁ h₁] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [Code.x86_64Depth] at hd ⊢
    exact Frame.below_mono (ih (fun i hi => hc i (List.mem_append_left _ hi)) (by omega)) (by omega)
      (by omega)
  | iteF _ _ ih =>
    simp only [Code.x86_64Depth] at hd ⊢
    exact Frame.below_mono (ih (fun i hi => hc i (List.mem_append_right _ hi)) (by omega)) (by omega)
      (by omega)
  | loopExit _ _ ih => exact ih hc hd
  | @loopNext body _ _ _ _ _ _ h₁ _ _ ih₁ ih₂ =>
    have f₂ := ih₂ hc hd
    rw [(Exec.rdwr h₁).2, Exec.rsp (c := body) hc h₁] at f₂
    exact Frame.trans (ih₁ hc hd) f₂
  | @frame i j b s₀ s₁ s₂ s₃ _ hp _ hq ih =>
    simp only [Code.x86_64Depth] at hd ⊢
    have hb : SpSafe b := fun x hx => hc x (by simp [instrs, hx])
    obtain ⟨e₁, w₁, -, f₀⟩ := push_frame hp
    have f₁ := ih hb (by omega)
    rw [w₁, e₁] at f₁
    rw [pop_mem hq]
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub f₁ fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) (by omega)⟩
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) (by omega)⟩
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_below _ _ _⟩
  | @call _ b s₀ s₁ s₂ s₃ _ hc₁ hb hr ih =>
    simp only [Code.x86_64Depth] at hd ⊢
    have e₁ : s₁ = s₀.callEntry := (Option.some.inj ((call_callEntry s₀).symm.trans hc₁)).symm
    subst e₁
    have hm : s₃.mem = s₂.mem := by
      simp only [isa, ret] at hr; split at hr <;> cases hr; rfl
    have f₀ : Frame (s₀.wr ++ [below (s₀.gpr .rsp) (b.x86_64Depth + 8)]) s₀.mem s₀.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega) (by omega))
    have f₁ := ih hc (by omega)
    simp only [State.callEntry_wr, State.callEntry_rsp] at f₁
    have f₁' : Frame (s₀.wr ++ [below (s₀.gpr .rsp) (b.x86_64Depth + 8)]) s₀.callEntry.mem s₂.mem :=
      Frame.sub f₁ fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_callee _ _⟩
    rw [hm]; exact Frame.trans f₀ f₁'

end VG.X86_64
