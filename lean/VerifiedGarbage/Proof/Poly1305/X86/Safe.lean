import VerifiedGarbage.Proof.Poly1305.X86.Setup
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# Poly1305 on x86 (32-bit): straight-line code runs, whatever the values

Untrusted: everything here is checked by Lean. The lemmas of `Absorb.lean`
and `Reduce.lean` state what the code computes where the numbers are within
their bounds (as they are when the state represents a message). Whatever the
values, the code runs without a fault: it accesses only the state (at `edi`)
and the block (at `esi`), stores only some words of the state and writes only
some registers. `okList` checks this of a block of code, by evaluation, and
`okList_ok` proves it.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- A memory operand the code may read: a word of the state or of the block. -/
def memOk (blk : Bool) (m : MemOp) : Bool :=
  (m.base == .edi && m.disp + 4 ≤ 128) || (blk && m.base == .esi && m.disp + 4 ≤ 16)

def srcOk (blk : Bool) : Src → Bool
  | .mem m => memOk blk m
  | _ => true

/-- Whether an instruction only reads the state or the block, stores only
the words `S` of the state and writes only the registers `rs`, with `c`
whether CF is defined; and then whether CF is defined afterwards. -/
def okStep (blk : Bool) (rs : List Reg) (S : List Nat) (c : Bool) : Instr → Option Bool
  | .mov d src => if rs.contains d && srcOk blk src then some c else none
  | .store m _ =>
    if m.base == .edi && m.disp % 4 == 0 && S.contains (m.disp / 4) && m.disp + 4 ≤ 128 then some c
    else none
  | .alu op d src =>
    if rs.contains d && srcOk blk src && (!Taint.usesCarry op || c) then some true else none
  | .shift _ d n => if rs.contains d && 1 ≤ n && n ≤ 31 then some true else none
  | .mul _ => if rs.contains .eax && rs.contains .edx then some true else none
  | _ => none

def okList (blk : Bool) (rs : List Reg) (S : List Nat) : Bool → List Instr → Bool
  | _, [] => true
  | c, i :: is => match okStep blk rs S c i with
    | some c' => okList blk rs S c' is
    | none => false

/-- What an instruction or block that `okStep` accepts leaves. -/
structure Safe (st : BitVec 32) (rs : List Reg) (S : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sR st] s.mem s'.mem
  same : ∀ k < 32, k ∉ S → wv s'.mem st (4 * k) = wv s.mem st (4 * k)

theorem Safe.refl (st : BitVec 32) (rs : List Reg) (S : List Nat) (s : State) : Safe st rs S s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩

theorem Safe.trans {st : BitVec 32} {rs : List Reg} {S : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : Safe st rs S s₁ s₂) (h₂ : Safe st rs S s₂ s₃) : Safe st rs S s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.frame.trans h₂.frame, fun k hk hS => (h₂.same k hk hS).trans (h₁.same k hk hS)⟩

/-- The block's words may be read. -/
def BlkIn (s : State) : Prop := ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) d) 4

theorem readSrc_ok {st : BitVec 32} {s : State} {blk : Bool} (hc : Ctx st s) (hb : blk = true → BlkIn s)
    {src : Src} (h : srcOk blk src = true) : ∃ x, readSrc s src = some x := by
  cases src with
  | reg r => exact ⟨_, rfl⟩
  | imm w => exact ⟨_, rfl⟩
  | mem m =>
    have ea : s.ea m = addr (s.gpr m.base) m.disp := rfl
    simp only [srcOk, memOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨hb', hd⟩ | ⟨⟨hbk, hb'⟩, hd⟩
    · rw [hb', hc.edi] at ea
      exact ⟨_, readSrc_mem ea (hc.inRW hd (by omega))⟩
    · rw [hb'] at ea
      exact ⟨_, readSrc_mem ea (hb hbk _ hd)⟩

/-- An instruction that writes at most the register `d`, and no memory. -/
theorem safe_dst {st : BitVec 32} {rs : List Reg} {S : List Nat} {i : Instr} {d : Reg}
    (hd : Taint.dst i = some d) (hdr : d ∈ rs) {s s' : State} (h : exec i s = some s') :
    Safe st rs S s s' := by
  obtain ⟨hw, hm, hg⟩ := Taint.exec_dst hd h
  refine ⟨fun r hr => hg r fun e => hr (e ▸ hdr), (exec_regions h).1, hw, ?_, fun _ _ _ => ?_⟩
  · rw [hm]; exact Frame.refl _ _
  · rw [hm]

theorem okStep_ok {st : BitVec 32} {blk : Bool} {rs : List Reg} {S : List Nat} {c c' : Bool} {i : Instr}
    (h : okStep blk rs S c i = some c') {s : State} (hc : Ctx st s) (hb : blk = true → BlkIn s)
    (hcf : c = true → s.cf.isSome) :
    ∃ s', exec i s = some s' ∧ Safe st rs S s s' ∧ (c' = true → s'.cf.isSome) := by
  have hfit := hc.fit
  cases i with
  | mov d src =>
    simp only [okStep, Bool.and_eq_true, List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨x, hx⟩ := readSrc_ok hc hb hd.2
    have he : exec (.mov d src) s = some (s.setReg d x) := by simp [exec, hx]
    refine ⟨_, he, safe_dst rfl hd.1 he, ?_⟩
    simp only [Option.some.injEq] at h
    subst h; exact hcf
  | store m r =>
    simp only [okStep, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at h
    split at h <;> [skip; cases h]
    rename_i hm
    obtain ⟨⟨⟨hb', h4⟩, hS⟩, hd⟩ := hm
    have ea : s.ea m = addr (s.gpr m.base) m.disp := rfl
    rw [hb', hc.edi, show m.disp = 4 * (m.disp / 4) by omega] at ea
    refine ⟨{ s with mem := s.mem.writeW (addr st (4 * (m.disp / 4))) (s.gpr r) }, ?_, ⟨fun _ _ => rfl,
      rfl, rfl, frame_write (Frame.refl _ _) hfit (by omega) _, fun k hk hkS => ?_⟩, ?_⟩
    · simp only [exec, State.store32, ea, hc.inW (by omega : 4 * (m.disp / 4) + 4 ≤ 128) (by omega),
        ite_true]
    · show wv (s.mem.writeW _ _) st (4 * k) = _
      have : k ≠ m.disp / 4 := fun e => hkS (e ▸ hS)
      rw [wv, wd_write_ne _ _ (by omega) (by omega) (by omega)]
    · simp only [Option.some.injEq] at h
      subst h; exact hcf
  | alu op d src =>
    simp only [okStep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨⟨hdr, hsrc⟩, hcarry⟩ := hd
    obtain ⟨x, hx⟩ := readSrc_ok hc hb hsrc
    obtain ⟨o, ho⟩ : ∃ o, Taint.aluOut op (s.gpr d) x s.cf = some o := by
      cases op <;> simp only [Taint.aluOut] <;>
        first
        | exact ⟨_, rfl⟩
        | (obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp (hcf (hcarry.resolve_left (by decide)))
           rw [hc₀]; exact ⟨_, rfl⟩)
    obtain ⟨r, co, oo⟩ := o
    have he : exec (.alu op d src) s = some (if Taint.writes op then (arithFlags s r co oo).setReg d r
        else arithFlags s r co oo) := by
      simp only [exec, Taint.execAlu_eq, hx, Option.bind_some, ho, Option.map_some]
    refine ⟨_, he, safe_dst rfl hdr he, fun _ => ?_⟩
    split <;> rfl
  | shift op d n =>
    simp only [okStep, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨⟨hdr, h1⟩, h2⟩ := hd
    have hn : 1 ≤ n ∧ n ≤ 31 := ⟨h1, h2⟩
    obtain ⟨s', he⟩ : ∃ s', exec (.shift op d n) s = some s' := by
      cases op <;> exact ⟨_, by simp only [exec, execShift, hn, and_self, ite_true]; rfl⟩
    refine ⟨s', he, safe_dst rfl hdr he, fun _ => ?_⟩
    cases op <;> simp only [exec, execShift, hn, and_self, ite_true, Option.some.injEq] at he <;>
      subst he <;> rfl
  | mul q =>
    simp only [okStep, Bool.and_eq_true, List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    refine ⟨execMul q s, rfl, ⟨fun r hr => Taint.execMul_gpr q s (fun e => hr (e ▸ hd.1))
      (fun e => hr (e ▸ hd.2)), rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩, fun _ => rfl⟩
  | bswap | movzx8 | store8 | push | pop => simp [okStep] at h

/-- A block that `okList` accepts runs, whatever the values. -/
theorem okList_ok {st : BitVec 32} {blk : Bool} {rs : List Reg} {S : List Nat}
    (hrs : Reg.edi ∉ rs ∧ Reg.esi ∉ rs) :
    ∀ (is : List Instr) (c : Bool) (s : State), okList blk rs S c is = true → Ctx st s →
      (blk = true → BlkIn s) →
      (c = true → s.cf.isSome) → WP isa (.block is) s (Safe st rs S s) := by
  intro is
  induction is with
  | nil => intro _ s _ _ _ _; exact WP.block_nil (Safe.refl _ _ _ _)
  | cons i is ih =>
    intro c s h hc hb hcf
    simp only [okList] at h
    split at h <;> [skip; cases h]
    rename_i c' hi
    obtain ⟨s₁, he, hs, hcf₁⟩ := okStep_ok hi hc hb hcf
    refine WP.cons he (WP.mono (ih c' s₁ h (hc.keep (hs.gpr _ hrs.1) hs.wr) ?_ hcf₁)
      fun s₂ h₂ => hs.trans h₂)
    intro hbk d hd
    rw [hs.rd, hs.wr, hs.gpr _ hrs.2]; exact hb hbk d hd

/-- The words a `Safe` block leaves. -/
theorem Safe.after {st : BitVec 32} {rs : List Reg} {S : List Nat} {s s' : State}
    (h : Safe st rs S s s') : After st s s' (words s'.mem st) rs :=
  ⟨words_ok _ _, h.frame, h.gpr, h.rd, h.wr⟩

/-- A run of `c` satisfies `Q₁`, and `Q₂` where `C` holds (runs are deterministic). -/
theorem WP.cond {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} {C : Prop}
    (h₁ : WP isa c s Q₁) (h₂ : C → WP isa c s Q₂) : WP isa c s fun s' => Q₁ s' ∧ (C → Q₂ s') := by
  obtain ⟨t, s', he, hq⟩ := h₁
  refine ⟨t, s', he, hq, fun hC => ?_⟩
  obtain ⟨t₂, s₂, he₂, hq₂⟩ := h₂ hC
  rw [(Exec.det he he₂).2]; exact hq₂

theorem words_eq {m : Mem} {st : BitVec 32} {g : Nat → Nat} (hw : Words m st g) {k : Nat}
    (hk : k < 32) : words m st k = g k := hw k hk

end VG.Proof.Poly1305.X86
