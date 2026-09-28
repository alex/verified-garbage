import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# Calls and frames (x86, 32-bit)

Untrusted: everything here is checked by Lean.

A call (`Code.call`) stores its return address at `esp - 4` and runs the
called function from there (`State.callEntry`). A frame's push stores its
registers below `esp` (`pushed`), where a cdecl caller puts the arguments of
the functions it calls, and its pop reloads them (`popped`). Code that never
writes `esp` itself changes memory only within the regions it may write and
the `stackUse` bytes below `esp` that its calls and frames use
(`Exec.frameSp`). `WP.call` runs a call of verified code from the callee's
`Verified` proof, as `WP.inline` does for inlined code, and `WP.frame` runs a
frame.
-/

namespace VG.X86

/-- The bytes a frame's push stores. -/
def frameBytes : Instr → Nat
  | .push rs => 4 * rs.length
  | _ => 0

/-- The bytes below `esp` that the calls and frames of `c`, and of the
functions it calls, use. -/
def stackUse : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max (stackUse a) (stackUse b)
  | .ite _ t e => max (stackUse t) (stackUse e)
  | .loop b _ => stackUse b
  | .call _ b => stackUse b + 4
  | .frame i b _ => stackUse b + frameBytes i

/-- The `n` bytes below `sp`. -/
abbrev below (sp : BitVec 32) (n : Nat) : Region := ⟨(sp - BitVec.ofNat 32 n).setWidth 64, n⟩

theorem belowSp_eq (s : State) (n : Nat) : Taint.belowSp s n = below (s.gpr .esp) n := rfl

/-- No instruction writes `esp` (frames move it, and restore it). -/
abbrev NoSp (c : Prog isa) : Prop := ∀ i ∈ instrs c, Taint.clobbers i .esp = false

theorem sub_toNat {sp : BitVec 32} {k : Nat} (h : k ≤ sp.toNat) :
    (sp - BitVec.ofNat 32 k).toNat = sp.toNat - k := by
  have := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  rw [show 2 ^ 32 - k + sp.toNat = (sp.toNat - k) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- The `a` bytes below `sp - k` are among the `b` bytes below `sp`. -/
theorem below_inner {sp : BitVec 32} {a b k : Nat} (h : a + k ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (below (sp - BitVec.ofNat 32 k) a) (below sp b) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have hk : a ≤ (sp - BitVec.ofNat 32 k).toNat := by rw [sub_toNat (by omega)]; omega
  rw [Taint.sub_setWidth hk, Taint.sub_setWidth (by omega)] at *
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem below_sub {sp : BitVec 32} {a b : Nat} (h : a ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (below sp a) (below sp b) := by
  have := below_inner (sp := sp) (a := a) (k := 0) (by omega) hb
  simpa using this

/-- The `k` bytes just below `sp` are among the `b ≥ k` bytes below `sp`. -/
theorem below_top {sp : BitVec 32} {k b n : Nat} (h : k ≤ b) (hb : b ≤ sp.toNat) (hn : n ≤ k) :
    (below sp b).Contains ((sp - BitVec.ofNat 32 k).setWidth 64) n := by
  simp only [Region.Contains]
  rw [Taint.sub_setWidth (by omega), Taint.sub_setWidth (by omega)]
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem Frame.below_mono {wr : List Region} {sp : BitVec 32} {a b : Nat} {m m' : Mem}
    (h : Frame (wr ++ [below sp a]) m m') (hab : a ≤ b) (hb : b ≤ sp.toNat) :
    Frame (wr ++ [below sp b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub hab hb⟩

/-- The state after a frame's push of `rs`. -/
def pushed (rs : List Reg) (s : State) : State :=
  { pushRegs s rs with wr := below (s.gpr .esp) (4 * rs.length) :: s.wr }

/-- The state after a frame's `pop r` (`k` times), from the state `s` its
body ends in. -/
def popped (r : Reg) (k : Nat) (s : State) : State := { popReg s r k with wr := s.wr.tail }

theorem push_some {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ rs, i = .push rs ∧ rs ≠ [] ∧ .esp ∉ rs ∧ 4 * rs.length ≤ (s.gpr .esp).toNat ∧
      s₁ = pushed rs s := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨_, rfl, hc.1, hc.2.1, hc.2.2, rfl⟩

theorem push_pushed {rs : List Reg} {s : State} (hne : rs ≠ []) (hrs : .esp ∉ rs)
    (hn : 4 * rs.length ≤ (s.gpr .esp).toNat) : isa.push (.push rs) s = some (pushed rs s) := by
  simp only [isa, push, ne_eq, hne, not_false_eq_true, hrs, hn, and_self, ite_true]
  rfl

theorem pop_mem {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mem = s₂.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  exact (popReg_rest _ _ _).1

@[simp] theorem pushed_rd (rs : List Reg) (s : State) : (pushed rs s).rd = s.rd :=
  (pushRegs_eq s rs).1
@[simp] theorem pushed_wr (rs : List Reg) (s : State) :
    (pushed rs s).wr = below (s.gpr .esp) (4 * rs.length) :: s.wr := rfl
theorem pushed_esp (rs : List Reg) (s : State) :
    (pushed rs s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * rs.length) := (pushRegs_eq s rs).2.2.1
theorem pushed_gpr (rs : List Reg) (s : State) {r : Reg} (h : r ≠ .esp) :
    (pushed rs s).gpr r = s.gpr r := (pushRegs_eq s rs).2.2.2 r h

/-- A frame's push changes memory only in the frame. -/
theorem pushed_frame {rs : List Reg} {s : State} (hrs : .esp ∉ rs)
    (hn : 4 * rs.length ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) (4 * rs.length)] s.mem (pushed rs s).mem := fun x hx =>
  (pushRegs_mem s rs hrs hn).1 x (hx _ (List.mem_singleton_self _))

/-- The `i`-th word of the frame holds the `i`-th register from the end of
`rs`: after pushing a function's arguments last to first, the frame holds
them in cdecl order. -/
theorem pushed_word {rs : List Reg} {s : State} (hrs : .esp ∉ rs)
    (hn : 4 * rs.length ≤ (s.gpr .esp).toNat) {i : Nat} (hi : i < rs.length) :
    (pushed rs s).mem.readW (((pushed rs s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s.gpr rs[rs.length - 1 - i] := by
  have := (pushRegs_mem s rs hrs hn).2 (rs.length - 1 - i) (by omega)
  rw [show rs.length - 1 - i + 1 = rs.length - i by omega] at this
  rw [← this, pushed_esp]
  show (pushRegs s rs).mem.readW _ 32 = _
  congr 2
  have := (s.gpr .esp).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, sub_toNat hn, sub_toNat (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := 4 * i) (by omega)]
  exact Nat.mod_eq_of_lt (by omega) |>.trans (by omega)

/-- The `j`-th argument of a function called from `s`. -/
theorem argAddr_callEntry (s : State) (j : Nat) :
    argAddr s.callEntry j = (s.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 := by
  simp only [argAddr, State.callEntry_esp]
  congr 1
  rw [show 4 + 4 * j = 4 * j + 4 by omega, BitVec.ofNat_add]
  bv_omega

theorem arg_callEntry {s : State} {j : Nat} (h₁ : 4 ≤ (s.gpr .esp).toNat)
    (h₂ : (s.gpr .esp).toNat + 4 * j + 4 ≤ 2 ^ 32) :
    arg s.callEntry j = s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64) 32 := by
  rw [arg, argAddr_callEntry, State.callEntry_mem]
  refine Frame.readW (rs := [below (s.gpr .esp) 4]) (r := ⟨(s.gpr .esp).setWidth 64 +
    BitVec.ofNat 64 (4 * j), 4⟩) ?_ ?_ ?_ (by decide)
  · exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (below_top (le_refl 4) h₁ (by decide))
  · simp only [Region.Contains, Nat.reduceDiv]
    rw [show (s.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = _ from
      addr_eq (x := s.gpr .esp) (k := 4 * j) (by omega)]
    simp
  · simp only [List.mem_singleton]
    rintro r rfl x hx hx'
    simp only [Region.Contains] at hx hx'
    rw [Taint.sub_setWidth h₁] at hx'
    have := (s.gpr .esp).isLt
    have hE : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    generalize (s.gpr .esp).setWidth 64 = E at *
    bv_omega

/-- Code that never writes `esp` changes memory only within the regions it
may write, and within the `stackUse` bytes below `esp` (its calls' return
addresses and its frames). -/
theorem Exec.frameSp {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hc : NoSp c) (hd : stackUse c ≤ (s.gpr .esp).toNat) :
    Frame (s.wr ++ [below (s.gpr .esp) (stackUse c)]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    have hc₁ : NoSp c₁ := fun i hi => hc i (List.mem_append_left _ hi)
    have hc₂ : NoSp c₂ := fun i hi => hc i (List.mem_append_right _ hi)
    simp only [stackUse] at hd ⊢
    have e := Exec.gpr hc₁ h₁
    have f₁ := Frame.below_mono (ih₁ hc₁ (by omega)) (b := max (stackUse c₁) (stackUse c₂))
      (by omega) hd
    have f₂ := Frame.below_mono (ih₂ hc₂ (by rw [e]; omega)) (b := max (stackUse c₁) (stackUse c₂))
      (by omega) (by rw [e]; exact hd)
    rw [(Exec.rdwr h₁).2, e] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [stackUse] at hd ⊢
    exact Frame.below_mono (ih (fun i hi => hc i (List.mem_append_left _ hi)) (by omega))
      (by omega) hd
  | iteF _ _ ih =>
    simp only [stackUse] at hd ⊢
    exact Frame.below_mono (ih (fun i hi => hc i (List.mem_append_right _ hi)) (by omega))
      (by omega) hd
  | loopExit _ _ ih => exact ih hc hd
  | @loopNext body _ _ _ _ _ _ h₁ _ _ ih₁ ih₂ =>
    have e := Exec.gpr (c := body) hc h₁
    have f₂ := ih₂ hc (by rw [e]; exact hd)
    rw [(Exec.rdwr h₁).2, e] at f₂
    exact Frame.trans (ih₁ hc hd) f₂
  | @call _ b s₀ s₁ s₂ s₃ _ hc₁ _ hr ih =>
    simp only [stackUse] at hd ⊢
    have e₁ : s₁ = s₀.callEntry := (Option.some.inj ((call_callEntry s₀).symm.trans hc₁)).symm
    subst e₁
    have hm : s₃.mem = s₂.mem := by
      simp only [isa, ret] at hr; split at hr <;> cases hr; rfl
    have f₀ : Frame (s₀.wr ++ [below (s₀.gpr .esp) (stackUse b + 4)]) s₀.mem s₀.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_top (k := 4) (by omega) hd (by decide))
    have e4 : (s₀.gpr .esp - 4).toNat = (s₀.gpr .esp).toNat - 4 := by bv_omega
    have f₁ := ih hc (by rw [State.callEntry_esp, e4]; omega)
    simp only [State.callEntry_wr, State.callEntry_esp] at f₁
    rw [hm]
    refine Frame.trans f₀ (Frame.sub f₁ fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        below_inner (k := 4) (le_refl _) hd⟩
  | @frame i _ b s₀ s₁ s₂ _ _ hp _ hq ih =>
    obtain ⟨rs, rfl, -, hrs, hn, rfl⟩ := push_some hp
    simp only [stackUse, frameBytes] at hd ⊢
    rw [pop_mem hq]
    have hc' : NoSp b := fun i hi => hc i (by simp [instrs, hi])
    have f₁ := ih hc' (by rw [pushed_esp, sub_toNat hn]; omega)
    rw [pushed_wr, pushed_esp] at f₁
    refine Frame.trans (fun x hx => pushed_frame hrs hn x fun r hr => ?_) (Frame.sub f₁ fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hx _ (List.mem_append_right _ (List.mem_singleton_self _))
        (below_sub (by omega) hd _ hc)
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) hd⟩
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          below_inner (by omega) hd⟩

/-- Calling verified code: from a state `s` such that, once the call has
stored its return address (`State.callEntry`), the callee's precondition
holds with its permissions narrowed to `rd` and `wr`, the call returns in a
state that has the permissions of `s`, its callee-saved registers (`esp`
among them), and every register the callee's instructions never write; that
differs from `s` in memory only within `wr` and the stack below `esp` that
the call uses; and whose memory and registers (`esp` aside) are those of a
state satisfying the callee's postcondition. -/
theorem WP.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) {s : State} (hd : stackUse c + 4 ≤ (s.gpr .esp).toNat)
    {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (stackUse c + 4)]) s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .esp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have e4 : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := by bv_omega
  have hf := Exec.frameSp he hsp (by
    simp only [State.withRegions_gpr, State.callEntry_esp, e4]; omega)
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_esp] at hf
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
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) ?_ (fun r h => ?_)
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩⟩
  · by_cases h : r = .esp
    · subst h; exact hesp
    · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · -- The return address, then the callee.
    have f₀ : Frame (wr ++ [below (s.gpr .esp) (stackUse c + 4)]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_top (k := 4) (by omega) hd (by decide))
    refine Frame.trans f₀ (Frame.sub hf fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        below_inner (k := 4) (le_refl _) hd⟩
  · by_cases hrs : r = .esp
    · subst hrs; exact hesp
    · rw [hkeep r hrs, Exec.gpr h he', State.callEntry_gpr _ hrs]

/-- A frame: its body, which never writes `esp`, runs from `pushed rs s`,
and the pop of the `rs.length` words leads to `popped r rs.length s₂`. -/
theorem WP.frame {rs : List Reg} {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hne : rs ≠ []) (hrs : .esp ∉ rs) (hr : r ≠ .esp) (hn : 4 * rs.length ≤ (s.gpr .esp).toNat)
    (hsp : NoSp body) (hb : WP isa body (pushed rs s) fun s₂ => Q (popped r rs.length s₂)) :
    WP isa (.frame (.push rs) body (.pop r rs.length)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hsp he
  have hpop : isa.pop (.pop r rs.length) (pushed rs s) s₂ = some (popped r rs.length s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨by simpa using hne, hr, hp, hw, ?_⟩
    rw [pushed_wr, pushed_esp]; rfl
  exact ⟨_, _, Exec.frame (push_pushed hne hrs hn) he hpop, hq⟩

end VG.X86
