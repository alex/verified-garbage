import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# Calls in a frame of their arguments (x86, 32-bit)

cdecl code passes a callee's arguments in a frame of their own around the
call, `push rs; call n; pop r` (`rs.length` words). `WP.callWith` runs one,
combining `WP.frame` and `WP.call`, from what the callee's contract needs of
the state the frame is pushed from (`CallPre`). The callee sees the
registers pushed as its arguments, the last one first (`callEntry_arg`).
-/

namespace VG.X86

theorem instrs_eq_instrs (c : Prog isa) : instrs c = VG.instrs c := by
  induction c <;> simp [instrs, VG.instrs, *]

/-- `NoSp`, from a check the kernel evaluates (`by decide +kernel`). -/
theorem NoSp.of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) :
    NoSp c := by
  intro i hi
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  simpa using h i (instrs_eq_instrs c ▸ hi)

/-! ## The frame's pop -/

theorem popped_esp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) := (popReg_eq s r k).2.2.1

theorem popped_gpr (r : Reg) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .esp) (h₂ : q ≠ r) :
    (popped r k s).gpr q = s.gpr q := (popReg_eq s r k).2.2.2 q h₁ h₂

@[simp] theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd := (popReg_eq s r k).1

@[simp] theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl

@[simp] theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  (popReg_rest s r k).1

/-! ## The callee's view of a frame of arguments -/

section
variable (rs : List Reg) (s : State)

theorem callEntry_esp' :
    (pushed rs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) := by
  rw [State.callEntry_esp, pushed_esp, BitVec.ofNat_add, BitVec.sub_sub]; rfl

theorem callEntry_gpr' {r : Reg} (h : r ≠ .esp) : (pushed rs s).callEntry.gpr r = s.gpr r := by
  rw [State.callEntry_gpr _ h, pushed_gpr _ _ h]

/-- The first argument's address: the frame's base. -/
theorem callEntry_argAddr0 :
    argAddr (pushed rs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 (4 * rs.length)).setWidth 64 := by
  rw [argAddr_callEntry, pushed_esp]; simp

variable {rs s} (hfit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat)
include hfit

theorem callEntry_espNat :
    ((pushed rs s).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - (4 * rs.length + 4) := by
  rw [callEntry_esp', sub_toNat hfit]

/-- The push and the return address are within the stack below `esp`. -/
theorem callEntry_frame (hrs : Reg.esp ∉ rs) :
    Frame [below (s.gpr .esp) (4 * rs.length + 4)] s.mem (pushed rs s).callEntry.mem := by
  rw [State.callEntry_mem]
  have f₁ : Frame [below (s.gpr .esp) (4 * rs.length + 4)] s.mem (pushed rs s).mem :=
    (pushed_frame hrs (by omega)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, below_sub (by omega) hfit⟩
  refine f₁.writeW (List.mem_singleton_self _) _ ?_
  rw [pushed_esp, show s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) - 4 =
    s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) by rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl]
  exact below_top (Nat.le_refl _) hfit (by omega)

/-- Argument `i` is the `i`-th register from the end of those pushed. -/
theorem callEntry_arg (hrs : Reg.esp ∉ rs) {i : Nat} (hi : i < rs.length) :
    arg (pushed rs s).callEntry i = s.gpr rs[rs.length - 1 - i] := by
  have hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega
  have e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, sub_toNat hn]
  have := (s.gpr .esp).isLt
  rw [arg_callEntry (by rw [e]; omega) (by rw [e]; omega)]
  exact pushed_word hrs hn hi

end

/-- Two runs that agree on `esp` and on the registers pushed pass the same
arguments. -/
theorem callEntry_arg_eq {rs : List Reg} {s₁ s₂ : State} (hrs : Reg.esp ∉ rs)
    (h₁ : 4 * rs.length + 4 ≤ (s₁.gpr .esp).toNat) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {i : Nat} (hi : i < rs.length) :
    arg (pushed rs s₁).callEntry i = arg (pushed rs s₂).callEntry i := by
  rw [callEntry_arg h₁ hrs hi, callEntry_arg (hsp ▸ h₁) hrs hi]
  exact hr _ (List.getElem_mem _)

/-! ## A call in a frame of its arguments -/

/-- What a call of `k` with the arguments `rs` pushed needs of the state it is
made from: the callee's precondition, with its permissions narrowed to `rd`
and `wr`, and those permitted. -/
structure CallPre (k : Contract isa) (rs : List Reg) (rd wr : List Region) (s : State) : Prop where
  pre : k.pre ((pushed rs s).callEntry.withRegions rd wr)
  cov : Covers (rd ++ wr) (s.rd ++ below (s.gpr .esp) (4 * rs.length) :: s.wr)
  covw : Covers wr (below (s.gpr .esp) (4 * rs.length) :: s.wr)

/-- A call of verified code in a frame of its arguments: the state it
returns in has the permissions of `s` and its callee-saved registers
(`esp` among them); its memory differs from that of `s` only within `wr`
and the stack below `esp` that the frame and the call use, and is that of a
state satisfying the callee's postcondition. -/
theorem WP.callWith {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : CallPre k rs rd wr s) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) (.call n c) (.pop .eax rs.length)) s Q := by
  have hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega
  have e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, sub_toNat hn]
  refine WP.frame hne hrs (by decide) hn (fun i hi => hsp i hi) ?_
  refine WP.call hv hsp (by rw [e]; omega) hk.pre (by rw [pushed_rd, pushed_wr]; exact hk.cov)
    (by rw [pushed_wr]; exact hk.covw) fun s₂ rd₂ wr₂ cs₂ f₂ _ ⟨s₃, m₃, _, post₃⟩ => ?_
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) (fun r hr => ?_) ?_
    ⟨s₃, by rw [m₃, popped_mem], post₃⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, cs₂ .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .eax := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', cs₂ r hr, pushed_gpr _ _ h]
  · rw [popped_mem]
    refine ((pushed_frame hrs hn).sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp]
        exact below_inner (by omega) hd

end VG.X86
