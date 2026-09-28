import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# The stack of calls and frames (x86, 32-bit)

Untrusted: everything here is checked by Lean.

Code that never writes `esp` itself changes memory only within the regions
it may write and within the stack below `esp` that its calls (their return
addresses) and frames (their pushes) use: `stackUse` bytes (`Exec.frameSp`).
`WP.callS` runs a call of verified code that may itself call functions and
push frames, from the callee's `Verified` proof, as `WP.call` does for code
without calls.

cdecl code passes a callee's arguments in a frame of their own around the
call: `WP.callWith` and `RelCT.callWith` combine `WP.frame` and `WP.callS`
(`RelCT.frame` and `RelCT.call`), and `callEntry_arg` gives the arguments the
callee sees (the registers pushed, the last one first).
-/

namespace VG.X86

/-- The `n` bytes below the stack pointer `e`. -/
abbrev below (e : BitVec 32) (n : Nat) : Region := ⟨e.setWidth 64 - BitVec.ofNat 64 n, n⟩

theorem setWidth_sub32 {x : BitVec 32} {d : Nat} (h : d ≤ x.toNat) :
    (x - BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 - BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := d) (by omega)]
  omega

theorem toNat_sub32 {x : BitVec 32} {d : Nat} (h : d ≤ x.toNat) :
    (x - BitVec.ofNat 32 d).toNat = x.toNat - d := by
  have hx := x.isLt
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem toNat_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; omega

/-- A longer stretch of the stack below the same pointer. -/
theorem below_mono {e : BitVec 32} {a b : Nat} (hab : a ≤ b) (hb : b ≤ e.toNat) :
    Region.Sub (below e a) (below e b) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have he := e.isLt
  have e1 : x - (e.setWidth 64 - BitVec.ofNat 64 b) =
      (x - (e.setWidth 64 - BitVec.ofNat 64 a)) + BitVec.ofNat 64 (b - a) := by
    rw [show BitVec.ofNat 64 b = BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a) by
      rw [← BitVec.ofNat_add]; congr 1; omega]
    bv_omega
  rw [e1, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b - a) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stack below a lower pointer. -/
theorem below_shift {e : BitVec 32} {a n : Nat} (h : a + n ≤ e.toNat) :
    Region.Sub (below (e - BitVec.ofNat 32 a) n) (below e (a + n)) := by
  have hb : (e - BitVec.ofNat 32 a).setWidth 64 - BitVec.ofNat 64 n =
      e.setWidth 64 - BitVec.ofNat 64 (a + n) := by
    rw [setWidth_sub32 (by omega), BitVec.ofNat_add]; bv_omega
  intro x hx
  simp only [Region.Contains, hb] at hx ⊢
  omega

/-- The word at `e - 4` (a return address) is on the stack below `e`. -/
theorem below_ret {e : BitVec 32} {n : Nat} (h₁ : 4 ≤ n) (h₂ : n ≤ e.toNat) :
    (below e n).Contains ((e - 4).setWidth 64) (32 / 8) := by
  rw [show (e - 4 : BitVec 32) = e - BitVec.ofNat 32 4 from rfl, setWidth_sub32 (by omega)]
  simp only [Region.Contains]
  have he := e.isLt
  rw [show e.setWidth 64 - BitVec.ofNat 64 4 - (e.setWidth 64 - BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (n - 4) by
    rw [show BitVec.ofNat 64 n = BitVec.ofNat 64 4 + BitVec.ofNat 64 (n - 4) by
      rw [← BitVec.ofNat_add]; congr 1; omega]
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Pushes -/

theorem pushRegs_mem_cons (s : State) (x : Reg) (xs : List Reg) :
    pushRegs s (x :: xs) = pushRegs { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) } xs := rfl

/-- A push writes only the words it pushes. -/
theorem pushRegs_frame (s : State) (rs : List Reg) (h : 4 * rs.length ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) (4 * rs.length)] s.mem (pushRegs s rs).mem := by
  induction rs generalizing s with
  | nil => exact Frame.refl _ _
  | cons x xs ih =>
    simp only [List.length_cons] at h
    rw [pushRegs_mem_cons]
    set s₁ : State := { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) }
    have hsp : s₁.gpr .esp = s.gpr .esp - BitVec.ofNat 32 4 := by simp [s₁, State.setReg]
    have h₁ : 4 * xs.length ≤ (s₁.gpr .esp).toNat := by rw [hsp, toNat_sub32 (by omega)]; omega
    have f₀ : Frame [below (s.gpr .esp) (4 * (xs.length + 1))] s.mem s₁.mem :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_ret (by omega) h)
    refine f₀.trans ((ih s₁ h₁).sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [hsp, show 4 * (xs.length + 1) = 4 + 4 * xs.length by omega]
    exact below_shift (by omega)

/-- The `j`-th register pushed is `4 (j + 1)` bytes below the stack pointer. -/
theorem pushRegs_readW (s : State) (rs : List Reg) (hrs : Reg.esp ∉ rs)
    (h : 4 * rs.length ≤ (s.gpr .esp).toNat) {j : Nat} (hj : j < rs.length) :
    (pushRegs s rs).mem.readW ((s.gpr .esp - BitVec.ofNat 32 (4 * (j + 1))).setWidth 64) 32 =
      s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => simp at hj
  | cons x xs ih =>
    simp only [List.length_cons] at h hj
    rw [pushRegs_mem_cons]
    set s₁ : State := { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) }
    have hsp : s₁.gpr .esp = s.gpr .esp - BitVec.ofNat 32 4 := by simp [s₁, State.setReg]
    have hx : x ≠ .esp := fun e => hrs (e ▸ List.mem_cons_self ..)
    have h₁ : 4 * xs.length ≤ (s₁.gpr .esp).toNat := by rw [hsp, toNat_sub32 (by omega)]; omega
    have hg : ∀ r, r ≠ .esp → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.setReg, hr]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.zero_add, Nat.mul_one]
      have c : (below (s₁.gpr .esp) (4 * xs.length)).Disjoint
          ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ := by
        intro a h₁' h₂'
        rw [hsp] at h₁'
        simp only [Region.Contains, setWidth_sub32 (show 4 ≤ (s.gpr .esp).toNat by omega)] at h₁' h₂'
        have hE : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := toNat_setWidth64 _
        have := (s.gpr .esp).isLt
        generalize (s.gpr .esp).setWidth 64 = E at h₁' h₂' hE
        bv_omega
      rw [(pushRegs_frame s₁ xs h₁).readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact c.symm) (by decide)]
      exact Mem.readW_writeW_self32 _ _ _
    | succ j =>
      have e : s.gpr .esp - BitVec.ofNat 32 (4 * (j + 1 + 1)) =
          s₁.gpr .esp - BitVec.ofNat 32 (4 * (j + 1)) := by
        rw [hsp, show 4 * (j + 1 + 1) = 4 + 4 * (j + 1) by omega, BitVec.ofNat_add]; bv_omega
      rw [e, ih s₁ (fun h' => hrs (List.mem_cons_of_mem _ h')) h₁ (by omega), List.getElem_cons_succ,
        hg _ fun e' => hrs (e' ▸ List.mem_cons_of_mem _ (List.getElem_mem _))]

/-! ## The callee's view of a frame of arguments -/

section
variable (rs : List Reg) (s : State)

theorem callEntry_esp' :
    (pushed rs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) := by
  rw [State.callEntry_esp, pushed_esp, BitVec.ofNat_add]; bv_omega

theorem callEntry_gpr' {r : Reg} (h : r ≠ .esp) : (pushed rs s).callEntry.gpr r = s.gpr r := by
  rw [State.callEntry_gpr _ h, pushed_gpr _ _ h]

@[simp] theorem callEntry_rd' : (pushed rs s).callEntry.rd = s.rd := by simp

theorem callEntry_wr' :
    (pushed rs s).callEntry.wr =
      ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * rs.length)).setWidth 64, 4 * rs.length⟩ :: s.wr := by simp

variable {rs s} (hfit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat)
include hfit

theorem pushed_wr_below :
    (pushed rs s).wr = below (s.gpr .esp) (4 * rs.length) :: s.wr := by
  rw [pushed_wr, setWidth_sub32 (by omega)]

theorem callEntry_esp64 :
    ((pushed rs s).callEntry.gpr .esp).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (4 * rs.length + 4) := by
  rw [callEntry_esp', setWidth_sub32 hfit]

theorem callEntry_espNat :
    ((pushed rs s).callEntry.gpr .esp).toNat = (s.gpr .esp).toNat - (4 * rs.length + 4) := by
  rw [callEntry_esp', toNat_sub32 hfit]

/-- The push and the return address are within the stack below `esp`. -/
theorem callEntry_frame :
    Frame [below (s.gpr .esp) (4 * rs.length + 4)] s.mem (pushed rs s).callEntry.mem := by
  rw [State.callEntry_mem]
  have f₁ : Frame [below (s.gpr .esp) (4 * rs.length + 4)] s.mem (pushed rs s).mem :=
    (pushRegs_frame s rs (by omega)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, below_mono (by omega) hfit⟩
  refine f₁.writeW (List.mem_singleton_self _) _ ?_
  rw [pushed_esp, show s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) - 4 =
    s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) by rw [BitVec.ofNat_add]; bv_omega,
    setWidth_sub32 hfit]
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]
  omega

/-- The first argument's address: the frame's base. -/
theorem callEntry_argAddr0 :
    argAddr (pushed rs s).callEntry 0 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (4 * rs.length) := by
  simp only [argAddr]
  rw [callEntry_esp', show s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) + BitVec.ofNat 32 (4 + 4 * 0) =
    s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) by rw [BitVec.ofNat_add]; bv_omega,
    setWidth_sub32 (by omega)]

/-- Argument `i` is the `i`-th register from the end of those pushed. -/
theorem callEntry_arg (hrs : Reg.esp ∉ rs) {i : Nat} (hi : i < rs.length) :
    arg (pushed rs s).callEntry i = s.gpr rs[rs.length - 1 - i] := by
  have hp := pushRegs_readW s rs hrs (by omega) (j := rs.length - 1 - i) (by omega)
  have ea : argAddr (pushed rs s).callEntry i =
      (s.gpr .esp - BitVec.ofNat 32 (4 * (rs.length - 1 - i + 1))).setWidth 64 := by
    simp only [argAddr]
    rw [callEntry_esp']
    congr 1
    rw [show 4 * (rs.length - 1 - i + 1) = 4 * rs.length - 4 * i by omega]
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 4 * rs.length + 4) (by omega), Nat.mod_eq_of_lt (a := 4 + 4 * i) (by omega),
      Nat.mod_eq_of_lt (a := 4 * rs.length - 4 * i) (by omega)]
    omega
  show (pushed rs s).callEntry.mem.readW (argAddr (pushed rs s).callEntry i) 32 = _
  rw [State.callEntry_mem, ea, pushed_esp, Mem.readW_writeW_sep ?_ (by decide)]
  · exact hp
  · intro x h₁ h₂
    rw [setWidth_sub32 (by omega)] at h₁
    rw [show s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) - 4 =
      s.gpr .esp - BitVec.ofNat 32 (4 * rs.length + 4) by rw [BitVec.ofNat_add]; bv_omega,
      setWidth_sub32 hfit] at h₂
    have hE : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := toNat_setWidth64 _
    have := (s.gpr .esp).isLt
    generalize (s.gpr .esp).setWidth 64 = E at h₁ h₂ hE
    bv_omega

end

/-- Two runs that agree on `esp` and on the registers pushed pass the same
arguments. -/
theorem callEntry_arg_eq {rs : List Reg} {s₁ s₂ : State} (hrs : Reg.esp ∉ rs)
    (h₁ : 4 * rs.length + 4 ≤ (s₁.gpr .esp).toNat) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {i : Nat} (hi : i < rs.length) :
    arg (pushed rs s₁).callEntry i = arg (pushed rs s₂).callEntry i := by
  rw [callEntry_arg h₁ hrs hi, callEntry_arg (hsp ▸ h₁) hrs hi]
  exact hr _ (List.getElem_mem _)

/-! ## Code with calls and frames -/

/-- The bytes a frame's push stores. -/
def pushBytes : Instr → Nat
  | .push rs => 4 * rs.length
  | _ => 0

/-- The bytes of stack below `esp` that code uses: its calls' return
addresses, its frames' pushes, and those of the functions it calls. -/
def stackUse : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max (stackUse a) (stackUse b)
  | .ite _ t e => max (stackUse t) (stackUse e)
  | .loop b _ => stackUse b
  | .call _ b => stackUse b + 4
  | .frame i b _ => pushBytes i + stackUse b

/-- No instruction writes `esp` (as the push and pop of a frame move it, a
frame's push and pop do not count). -/
abbrev NoSp (c : Prog isa) : Prop := ∀ i ∈ instrs c, Taint.clobbers i .esp = false

theorem instrs_eq_instrs (c : Prog isa) : instrs c = VG.instrs c := by
  induction c <;> simp [instrs, VG.instrs, *]

theorem NoSp.of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) : NoSp c := by
  intro i hi
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  simpa using h i (instrs_eq_instrs c ▸ hi)

@[simp] theorem arg_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    arg (s.withRegions rd wr) i = arg s i := rfl

@[simp] theorem argAddr_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    argAddr (s.withRegions rd wr) i = argAddr s i := rfl

theorem Frame.below_mono' {wr : List Region} {e : BitVec 32} {a b : Nat} {m m' : Mem}
    (h : Frame (wr ++ [below e a]) m m') (hab : a ≤ b) (hb : b ≤ e.toNat) :
    Frame (wr ++ [below e b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_mono hab hb⟩

theorem push_facts {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    pushBytes i ≤ (s.gpr .esp).toNat ∧ s₁.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (pushBytes i) ∧
      s₁.wr = below (s.gpr .esp) (pushBytes i) :: s.wr ∧
      Frame [below (s.gpr .esp) (pushBytes i)] s.mem s₁.mem := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h
  rename_i rs hc
  refine ⟨hc.2.2, pushed_esp rs s, ?_, pushRegs_frame s rs hc.2.2⟩
  show (pushed rs s).wr = _
  rw [pushed_wr, setWidth_sub32 hc.2.2]; rfl

theorem pop_mem {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mem = s₂.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  exact popReg_mem _ _ _

/-- Code that never writes `esp` changes memory only within the regions it
may write and the `stackUse` bytes below `esp`. -/
theorem Exec.frameSp {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hc : NoSp c) (hd : stackUse c ≤ (s.gpr .esp).toNat) :
    Frame (s.wr ++ [below (s.gpr .esp) (stackUse c)]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    have hc₁ : NoSp c₁ := fun i hi => hc i (List.mem_append_left _ hi)
    have hc₂ : NoSp c₂ := fun i hi => hc i (List.mem_append_right _ hi)
    simp only [stackUse] at hd ⊢
    have e₁ := Exec.gpr hc₁ h₁
    have f₁ := Frame.below_mono' (ih₁ hc₁ (by omega)) (b := max (stackUse c₁) (stackUse c₂)) (by omega) hd
    have f₂ := ih₂ hc₂ (by rw [e₁]; omega)
    rw [(Exec.rdwr h₁).2, e₁] at f₂
    exact Frame.trans f₁ (Frame.below_mono' f₂ (by omega) hd)
  | iteT _ _ ih =>
    simp only [stackUse] at hd ⊢
    exact Frame.below_mono' (ih (fun i hi => hc i (List.mem_append_left _ hi)) (by omega)) (by omega) hd
  | iteF _ _ ih =>
    simp only [stackUse] at hd ⊢
    exact Frame.below_mono' (ih (fun i hi => hc i (List.mem_append_right _ hi)) (by omega)) (by omega) hd
  | loopExit _ _ ih => exact ih hc hd
  | @loopNext body _ _ _ _ _ _ h₁ _ _ ih₁ ih₂ =>
    have hcb : NoSp body := hc
    have e₁ := Exec.gpr hcb h₁
    have f₂ := ih₂ hc (by rw [e₁]; exact hd)
    rw [(Exec.rdwr h₁).2, e₁] at f₂
    exact Frame.trans (ih₁ hc hd) f₂
  | @call _ b s₀ s₁ s₂ s₃ _ hc₁ hb hr ih =>
    simp only [stackUse] at hd ⊢
    have e₁ : s₁ = s₀.callEntry := (Option.some.inj ((call_callEntry s₀).symm.trans hc₁)).symm
    subst e₁
    have hm : s₃.mem = s₂.mem := by
      simp only [isa, ret] at hr; split at hr <;> cases hr; rfl
    have f₀ : Frame (s₀.wr ++ [below (s₀.gpr .esp) (stackUse b + 4)]) s₀.mem s₀.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_ret (by omega) hd)
    have hd' : stackUse b ≤ (s₀.callEntry.gpr .esp).toNat := by
      rw [State.callEntry_esp, show (s₀.gpr .esp - 4 : BitVec 32) = s₀.gpr .esp - BitVec.ofNat 32 4 from rfl,
        toNat_sub32 (by omega)]; omega
    have f₁ := ih hc hd'
    simp only [State.callEntry_wr, State.callEntry_esp] at f₁
    have f₁' : Frame (s₀.wr ++ [below (s₀.gpr .esp) (stackUse b + 4)]) s₀.callEntry.mem s₂.mem :=
      Frame.sub f₁ fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [show stackUse b + 4 = 4 + stackUse b by omega]
          exact below_shift (e := s₀.gpr .esp) (a := 4) (by omega)
    rw [hm]; exact Frame.trans f₀ f₁'
  | @frame i j b s₀ s₁ s₂ s₃ _ hp hb hq ih =>
    simp only [stackUse] at hd ⊢
    obtain ⟨hk, hsp, hwr, f₀⟩ := push_facts hp
    have hcb : NoSp b := fun i' hi' => hc i' (by simp [instrs, hi'])
    have f₁ := ih hcb (by rw [hsp, toNat_sub32 hk]; omega)
    rw [hwr, hsp] at f₁
    rw [pop_mem hq]
    refine (f₀.sub fun r hr => ?_).trans (f₁.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_mono (by omega) hd⟩
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_mono (by omega) hd⟩
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_shift hd⟩

/-- Calling verified code, which may itself call functions and push frames:
from a state `s` such that, once the call has stored its return address
(`State.callEntry`), the callee's precondition holds with its permissions
narrowed to `rd` and `wr`, the call returns in a state that has the
permissions of `s`, its callee-saved registers and `esp`; whose memory
differs from that of `s` only within `wr` and the stack below `esp` the call
uses; and whose memory and registers (`esp` aside) are those of a state
satisfying the callee's postcondition. -/
theorem WP.callS {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) {s : State} (hd : stackUse c + 4 ≤ (s.gpr .esp).toNat)
    {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hd' : stackUse c ≤ (s.callEntry.gpr .esp).toNat := by
    rw [State.callEntry_esp, show (s.gpr .esp - 4 : BitVec 32) = s.gpr .esp - BitVec.ofNat 32 4 from rfl,
      toNat_sub32 (by omega)]; omega
  have hf := Exec.frameSp he hsp (by simpa using hd')
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem] at hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  set s₂ := s₁.withRegions s.rd s.wr with hs₂
  have hsp₂ : s₂.gpr .esp = s.gpr .esp - 4 := by
    rw [hs₂, State.withRegions_gpr, habi.1 .esp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₂ = some (s₂.setReg .esp (s₂.gpr .esp + 4)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₂, State.callEntry_esp], ?_⟩
    have := habi.2
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_esp] at this
    rw [hsp₂, State.callEntry_esp]; exact this
  have hesp : (s₂.setReg .esp (s₂.gpr .esp + 4)).gpr .esp = s.gpr .esp := by
    simp only [State.setReg, ite_true, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .esp → (s₂.setReg .esp (s₂.gpr .esp + 4)).gpr r = s₂.gpr r :=
    fun r h => by simp [State.setReg, h]
  have hr₁ := (Exec.rdwr he)
  simp only [State.withRegions_rd, State.withRegions_wr] at hr₁
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) ?_
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩⟩
  · by_cases h : r = .esp
    · subst h; exact hesp
    · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · -- The return address, then the callee.
    have f₀ : Frame (wr ++ [below (s.gpr .esp) (stackUse c + 4)]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_ret (by omega) hd)
    have f₁ : Frame (wr ++ [below (s.gpr .esp) (stackUse c + 4)]) s.callEntry.mem s₁.mem :=
      Frame.sub hf fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [State.callEntry_esp, show (s.gpr .esp - 4 : BitVec 32) = s.gpr .esp - BitVec.ofNat 32 4 from rfl,
            show stackUse c + 4 = 4 + stackUse c by omega]
          exact below_shift (by omega)
    exact Frame.trans f₀ f₁

/-! ## A call in a frame of its arguments -/

/-- What a call of `k` with the arguments `rs` pushed needs of the state it is
made from: the callee's precondition, with its permissions narrowed to `rd`
and `wr`, and those permitted. -/
structure CallPre (k : Contract isa) (rs : List Reg) (rd wr : List Region) (s : State) : Prop where
  pre : k.pre ((pushed rs s).callEntry.withRegions rd wr)
  cov : Covers (rd ++ wr) (s.rd ++ below (s.gpr .esp) (4 * rs.length) :: s.wr)
  covw : Covers wr (below (s.gpr .esp) (4 * rs.length) :: s.wr)

theorem WP.callWith {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : CallPre k rs rd wr s) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) (.call n c) (.pop .eax rs.length)) s Q := by
  have hfit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := by omega
  have hw := pushed_wr_below hfit
  refine WP.frame hne hrs (by omega) rfl (by decide) ?_
  refine WP.callS hv hsp (by rw [pushed_esp, toNat_sub32 (by omega)]; omega) hk.pre
    (by rw [pushed_rd, hw]; exact hk.cov) (by rw [hw]; exact hk.covw)
    fun s₂ rd₂ wr₂ cs₂ f₂ ⟨s₃, m₃, _, post₃⟩ => ⟨cs₂ .esp (by simp [calleeSaved]), ?_⟩
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, hw]; rfl) (fun r hr => ?_) ?_
    ⟨s₃, by rw [m₃, popped_mem], post₃⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, cs₂ .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .eax := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', cs₂ r hr, pushed_gpr _ _ h]
  · rw [popped_mem]
    have f₀ := pushRegs_frame s rs (by omega)
    refine (f₀.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_mono (by omega) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp, show 4 * rs.length + stackUse c + 4 = 4 * rs.length + (stackUse c + 4) by omega]
        exact below_shift (by omega)

/-- Two runs of a call in a frame of its arguments leak the same trace when
the callee's contract holds in both, its public data agrees, and so does
`esp`. -/
theorem RelCT.callWith {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → 4 * rs.length + 4 ≤ (s₁.gpr .esp).toNat ∧
      CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧ s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa P (.frame (.push rs) (.call n c) (.pop .eax rs.length)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.2.1) (RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨hfit, k₁, k₂, hsp, hpub⟩ := hP _ _ h
  have w₁ := pushed_wr_below hfit
  have w₂ := pushed_wr_below (hsp ▸ hfit)
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, w₁]; exact k₁.cov, by rw [w₁]; exact k₁.covw,
    by rw [pushed_rd, w₂]; exact k₂.cov, by rw [w₂]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

end VG.X86
