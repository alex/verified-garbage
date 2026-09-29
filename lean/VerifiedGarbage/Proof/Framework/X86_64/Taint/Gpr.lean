import VerifiedGarbage.Proof.Framework.X86_64.Taint.Domain

/-!
# Taint tracking for x86-64: general-purpose instructions

Untrusted: everything here is checked by Lean.

The soundness of the analysis's step (`Taint.step`) for each general-purpose
instruction, including the stores of general-purpose registers.
-/

namespace VG.X86_64.Taint

/-! ### ALU instructions, uniformly -/

/-- The result, carry and overflow of an ALU operation at width `w`. -/
def aluOut {w : Nat} (op : AluOp) (a b : BitVec w) (cf : Option Bool) :
    Option (BitVec w × Bool × Bool) :=
  match op with
  | .add => let r := a + b; some (r, 2 ^ w ≤ a.toNat + b.toNat, addOverflow a b r)
  | .adc => cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth w
    (r, 2 ^ w ≤ a.toNat + b.toNat + c.toNat, addOverflow a b r)
  | .sub | .cmp => let r := a - b; some (r, a.toNat < b.toNat, subOverflow a b r)
  | .sbb => cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth w
    (r, a.toNat < b.toNat + c.toNat, subOverflow a b r)
  | .and | .test => some (a &&& b, false, false)
  | .or => some (a ||| b, false, false)
  | .xor => some (a ^^^ b, false, false)

theorem aluOut_cf {w : Nat} {op : AluOp} (h : usesCarry op = false) (a b : BitVec w)
    (c c' : Option Bool) : aluOut op a b c = aluOut op a b c' := by
  cases op <;> simp_all [usesCarry, aluOut]

theorem execAlu_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu op d src s = (readSrc s src).bind fun b =>
      (aluOut op (s.gpr d) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg d r else arithFlags s r c o := by
  cases op <;> simp [execAlu, aluOut, writes, Function.comp_def]

theorem execAlu32_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu32 op d src s = (readSrc32 s src).bind fun b =>
      (aluOut op ((s.gpr d).setWidth 32) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg32 d r else arithFlags s r c o := by
  cases op <;> simp [execAlu32, aluOut, writes, Function.comp_def]

section
variable {s : State} {r : Reg} {w : Nat} {v : BitVec 64} {x : BitVec w} {c o : Bool}
@[simp] theorem arithFlags_gpr : (arithFlags s x c o).gpr = s.gpr := rfl
@[simp] theorem arithFlags_cf : (arithFlags s x c o).cf = some c := rfl
@[simp] theorem arithFlags_of : (arithFlags s x c o).of = some o := rfl
@[simp] theorem arithFlags_zf : (arithFlags s x c o).zf = some (x == 0) := rfl
@[simp] theorem arithFlags_sf : (arithFlags s x c o).sf = some x.msb := rfl
@[simp] theorem setReg_cf : (s.setReg r v).cf = s.cf := rfl
@[simp] theorem setReg_of : (s.setReg r v).of = s.of := rfl
@[simp] theorem setReg_zf : (s.setReg r v).zf = s.zf := rfl
@[simp] theorem setReg_sf : (s.setReg r v).sf = s.sf := rfl
end

theorem regs_filter {τ : T} {s₁ s₂ s₁' s₂' : State} (h : ∀ r ∈ τ.regs, s₁.gpr r = s₂.gpr r)
    {d : Reg} (h₁ : ∀ r, r ≠ d → s₁'.gpr r = s₁.gpr r) (h₂ : ∀ r, r ≠ d → s₂'.gpr r = s₂.gpr r) :
    ∀ r ∈ τ.regs.erase d, s₁'.gpr r = s₂'.gpr r := by
  intro r hr
  simp only [RegSet.mem_erase] at hr
  rw [h₁ r hr.1, h₂ r hr.1, h r hr.2]

theorem not_pub_set {τ : T} {d : Reg} {p : Bool} (hp : ¬ p = true) : set τ d p = τ.regs.erase d := by
  simp [set, hp]

/-- ALU soundness, for both widths: `wr` writes the result register. -/
theorem alu_sound {w : Nat} {τ : T} {op : AluOp} {d : Reg} {src : Src} {s₁ s₂ : State}
    {b₁ b₂ : BitVec w} {out₁ out₂ : BitVec w × Bool × Bool}
    (ha : Agree τ s₁ s₂) (get : State → BitVec w) (wr : State → BitVec w → State)
    (hget : s₁.gpr d = s₂.gpr d → get s₁ = get s₂)
    (hwr : ∀ s x r, (wr s x).gpr r = if r = d then (wr s x).gpr d else s.gpr r)
    (hwrd : ∀ s₁ s₂ x, (wr s₁ x).gpr d = (wr s₂ x).gpr d)
    (hwrf : ∀ s x, (wr s x).cf = s.cf ∧ (wr s x).zf = s.zf ∧ (wr s x).sf = s.sf ∧ (wr s x).of = s.of)
    (hb : srcPub τ src = true → b₁ = b₂)
    (ho₁ : aluOut op (get s₁) b₁ s₁.cf = some out₁) (ho₂ : aluOut op (get s₂) b₂ s₂.cf = some out₂) :
    let p := pub τ d && srcPub τ src && (!usesCarry op || τ.flags)
    AgreeRF (if writes op then set τ d p else τ.regs) p
      (if writes op then wr (arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2) out₁.1
        else arithFlags s₁ out₁.1 out₁.2.1 out₁.2.2)
      (if writes op then wr (arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) out₂.1
        else arithFlags s₂ out₂.1 out₂.2.1 out₂.2.2) := by
  intro p
  by_cases hp : p = true
  · have hp' := hp
    simp only [p, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp'
    obtain ⟨⟨hd, hsp⟩, hc⟩ := hp'
    obtain rfl := hb hsp
    have hout : aluOut op (get s₁) b₁ s₁.cf = aluOut op (get s₂) b₁ s₂.cf := by
      rw [hget (ha.reg hd)]
      rcases hc with hc | hc
      · exact aluOut_cf hc _ _ _ _
      · rw [(ha.rf.2 hc).1]
    rw [hout, ho₂] at ho₁
    cases ho₁
    refine ⟨fun r hr => ?_, fun _ => ?_⟩
    · split
      · rename_i hw
        simp only [hw, ite_true] at hr
        rw [hwr _ _ r, hwr (arithFlags s₂ _ _ _) _ r]
        split
        · exact hwrd _ _ _
        · rename_i hrd
          simp only [set, hp, ite_true, RegSet.mem_insert, hrd, false_or] at hr
          simpa using ha.rf.1 r hr
      · rename_i hw
        simp only [hw, Bool.false_eq_true, ite_false] at hr ⊢
        simpa using ha.rf.1 r hr
    · split <;> simp [hwrf]
  · refine ⟨fun r hr => ?_, fun h => absurd h hp⟩
    split
    · rename_i hw
      simp only [hw, ite_true, not_pub_set hp] at hr
      refine regs_filter ha.rf.1 (fun r hr => ?_) (fun r hr => ?_) r hr <;>
        (rw [hwr]; simp [hr])
    · rename_i hw
      simp only [hw, Bool.false_eq_true, ite_false] at hr
      simpa using ha.rf.1 r hr

theorem setReg_gpr_eq (s : State) (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then (s.setReg d v).gpr d else s.gpr r := by
  simp only [State.setReg]; split <;> simp_all

/-! ### Instructions that write a register -/

/-- The general-purpose register an instruction writes, if it writes exactly
one (none for stores and SSE instructions, and for `mul`, which writes two). -/
def dstOf : Instr → Option Reg
  | .mov d _ | .mov32 d _ | .alu _ d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .movzx8 d _ | .bswap d | .shift _ d _ | .movImm64 d _ => some d
  | .store .. | .store32 .. | .store8 .. | .movdquLoad .. | .movdquStore .. | .xop _ | .vop _
  | .vmovdquLoad .. | .vmovdquStore .. | .vbroadcasti128 .. | .stmxcsr _ | .ldmxcsr _ | .lfence | .mul _ => none

/-- Whether an instruction may write the general-purpose register `r`. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .mul _ => r == .rax || r == .rdx
  | _ => dstOf i == some r

theorem exec_nonstore {i : Instr} {d : Reg} (hd : dstOf i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i <;> simp only [dstOf, Option.some.injEq, reduceCtorEq] at hd <;> subst hd
  case mov src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case mov32 src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case alu op src =>
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split
    · exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  case alu32 op src =>
    simp only [exec, execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split
    · exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  case shift32 op _ n =>
    simp only [exec, execShift32] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case bswap32 =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case movzx8 m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case bswap =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case movImm64 v =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, fun r h => setReg_ne h⟩

theorem aluBases_narrow (τ : T) (op : AluOp) (d : Reg) (src : Src) :
    aluBases τ op d src false = kill τ d := by
  unfold aluBases; split <;> simp

theorem aluBases_ok {τ : T} {s s' : State} (hw : Wf τ s) {op : AluOp} {d : Reg} {src : Src}
    (e : exec (.alu op d src) s = some s') :
    ∀ p ∈ aluBases τ op d src true, s'.gpr p.1 = (region s' p.2.1).base + BitVec.ofNat 64 p.2.2 := by
  obtain ⟨-, hwr, -, hg⟩ := exec_nonstore (d := d) rfl e
  unfold aluBases
  split
  · rename_i v
    split
    · rename_i hv
      simp only [Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      have hd : s'.gpr d = s.gpr d + BitVec.ofNat 64 v.toNat := by
        simp only [exec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
        subst e
        simp only [arithFlags, State.setFlags, State.setReg, ite_true]
        congr 1
        rw [BitVec.signExtend_eq_setWidth_of_msb_false hv]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      intro p hp
      simp only [List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq] at hp
      rcases hp with hp | ⟨q, ⟨hq, hqd⟩, rfl⟩
      · exact kill_bases hw hwr hg p hp
      · simp only
        rw [hd, ← hqd, hw.2 q hq, BitVec.add_assoc, ← BitVec.ofNat_add]
        simp [region, hwr]
    · exact kill_bases hw hwr hg
  · rename_i v
    split
    · rename_i hv
      simp only [Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hv
      have hd : s'.gpr d = s.gpr d - BitVec.ofNat 64 v.toNat := by
        simp only [exec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
        subst e
        simp only [arithFlags, State.setFlags, State.setReg, ite_true]
        congr 1
        rw [BitVec.signExtend_eq_setWidth_of_msb_false hv]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      intro p hp
      simp only [List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hp
      rcases hp with hp | ⟨q, ⟨hq, hqd, hle⟩, rfl⟩
      · exact kill_bases hw hwr hg p hp
      · simp only
        rw [hd, ← hqd, hw.2 q hq, show q.2.2 = (q.2.2 - v.toNat) + v.toNat by omega, BitVec.ofNat_add,
          ← BitVec.add_assoc, BitVec.add_sub_cancel, Nat.add_sub_cancel]
        simp [region, hwr]
    · exact kill_bases hw hwr hg
  · exact kill_bases hw hwr hg

theorem Agree.write {τ τ' : T} {i : Instr} {d : Reg} (hd : dstOf i = some d) {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hrf : AgreeRF τ'.regs τ'.flags s₁' s₂') (hl : τ'.lens = τ.lens) (hs : τ'.slots = τ.slots)
    (hb : ∀ p ∈ τ'.bases, p ∈ kill τ d) (hlo : τ'.lo = .empty) : Agree τ' s₁' s₂' := by
  obtain ⟨-, hw₁, hm₁, hg₁⟩ := exec_nonstore hd e₁
  obtain ⟨-, hw₂, hm₂, hg₂⟩ := exec_nonstore hd e₂
  exact ha.keep hrf hl hs hw₁ hw₂ hm₁ hm₂ (fun p h => kill_bases ha.wf₁ hw₁ hg₁ p (hb p h))
    (fun p h => kill_bases ha.wf₂ hw₂ hg₂ p (hb p h)) (hlo ▸ noLo)

theorem execMul_gpr (r : Reg) (s : State) {q : Reg} (h₁ : q ≠ .rax) (h₂ : q ≠ .rdx) :
    (execMul r s).gpr q = s.gpr q := by
  simp [execMul, State.setReg, State.setFlags, h₁, h₂]

theorem mul_bases {τ : T} {s : State} (hw : Wf τ s) (r : Reg) :
    ∀ p ∈ (kill τ .rax).filter (·.1 != .rdx),
      (execMul r s).gpr p.1 = (region (execMul r s) p.2.1).base + BitVec.ofNat 64 p.2.2 := by
  intro p hp
  simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
  rw [execMul_gpr r s hp.1.2 hp.2, hw.2 p hp.1.1]; rfl

theorem Agree.mul {τ : T} {r : Reg} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) :
    Agree (mulStep τ r) (execMul r s₁) (execMul r s₂) := by
  refine ha.keep ⟨fun q hq => ?_, fun hp => ?_⟩ rfl rfl rfl rfl rfl rfl (mul_bases ha.wf₁ r)
    (mul_bases ha.wf₂ r) noLo
  · simp only [mulStep] at hq
    by_cases hp : (pub τ .rax && pub τ r) = true
    · have hp' := hp
      simp only [Bool.and_eq_true] at hp'
      have e₁ := ha.reg hp'.1
      have e₂ := ha.reg hp'.2
      simp only [hp, ite_true, RegSet.mem_insert] at hq
      by_cases h₁ : q = .rax
      · subst h₁; simp [execMul, State.setReg, State.setFlags, e₁, e₂]
      by_cases h₂ : q = .rdx
      · subst h₂; simp [execMul, State.setReg, State.setFlags, e₁, e₂]
      simp only [h₁, h₂, false_or] at hq
      rw [execMul_gpr r s₁ h₁ h₂, execMul_gpr r s₂ h₁ h₂]; exact ha.rf.1 q hq
    · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hq
      rw [execMul_gpr r s₁ hq.2.1 hq.1, execMul_gpr r s₂ hq.2.1 hq.1]; exact ha.rf.1 q hq.2.2
  · simp only [mulStep, Bool.and_eq_true] at hp
    simp [execMul, State.setReg, State.setFlags, ha.reg hp.1, ha.reg hp.2]

theorem step_sound_mov {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : Reg} {src : Src}
    (ha : Agree τ s₁ s₂) (hs : step τ (.mov d src) = some τ')
    (e₁ : exec (.mov d src) s₁ = some s₁') (e₂ : exec (.mov d src) s₂ = some s₂') :
    addrs (.mov d src) s₁ = addrs (.mov d src) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
  refine ⟨ha.srcAddrs hok, ha.keep ⟨regs_set ha.rf.1 fun hp => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl
    (movBases_ok ha.wf₁ hv₁) (movBases_ok ha.wf₂ hv₂) noLo⟩
  rcases Bool.or_eq_true_iff.mp hp with hp | hp
  · rw [ha.readSrc hp, hv₂] at hv₁; cases hv₁; rfl
  · cases src with
    | mem m =>
      simp only [readSrc, State.load64] at hv₁ hv₂
      split at hv₁ <;> [skip; cases hv₁]
      split at hv₂ <;> [skip; cases hv₂]
      cases hv₁; cases hv₂
      exact ha.readW (w := 64) hok hp
    | _ => simp [loadPub] at hp

theorem step_sound_mov32 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : Reg} {src : Src}
    (ha : Agree τ s₁ s₂) (hs : step τ (.mov32 d src) = some τ')
    (e₁ : exec (.mov32 d src) s₁ = some s₁') (e₂ : exec (.mov32 d src) s₂ = some s₂') :
    addrs (.mov32 d src) s₁ = addrs (.mov32 d src) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  refine ⟨ha.srcAddrs hok, ha.write rfl e₁ e₂ ⟨?_, ?_⟩ rfl rfl (fun _ h => h) rfl⟩
  · simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
    refine regs_set ha.rf.1 fun hp => ?_
    rcases Bool.or_eq_true_iff.mp hp with hp | hp
    swap
    · cases src with
      | reg r =>
        simp only [readSrc32, Option.some.injEq] at hv₁ hv₂
        subst hv₁ hv₂
        rw [ha.lo r hp]
      | _ => simp [loPub] at hp
    rcases Bool.or_eq_true_iff.mp hp with hp | hp
    · rw [ha.readSrc32 hp, hv₂] at hv₁; cases hv₁; rfl
    · cases src with
      | mem m =>
        simp only [readSrc32, State.load32] at hv₁ hv₂
        split at hv₁ <;> [skip; cases hv₁]
        split at hv₂ <;> [skip; cases hv₂]
        cases hv₁; cases hv₂
        rw [ha.readW (w := 32) hok hp]
      | _ => simp [loadPub] at hp
  · simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, hv₁, rfl⟩ := e₁; obtain ⟨v₂, hv₂, rfl⟩ := e₂
    exact ha.rf.2

theorem step_sound_store {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {m : MemOp} {r : Reg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.store m r) = some τ')
    (e₁ : exec (.store m r) s₁ = some s₁') (e₂ : exec (.store m r) s₂ = some s₂') :
    addrs (.store m r) s₁ = addrs (.store m r) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, storeStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, State.store64] at e₁ e₂
  split at e₁ <;> [cases e₁; cases e₁]
  split at e₂ <;> [cases e₂; cases e₂]
  exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 8) hok (by decide) fun hp => by rw [ha.reg hp]⟩

theorem step_sound_store32 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {m : MemOp} {r : Reg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.store32 m r) = some τ')
    (e₁ : exec (.store32 m r) s₁ = some s₁') (e₂ : exec (.store32 m r) s₂ = some s₂') :
    addrs (.store32 m r) s₁ = addrs (.store32 m r) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, storeStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, State.store32] at e₁ e₂
  split at e₁ <;> [cases e₁; cases e₁]
  split at e₂ <;> [cases e₂; cases e₂]
  exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 4) hok (by decide) fun hp => by rw [ha.reg hp]⟩

theorem step_sound_store8 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {m : MemOp} {r : Reg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.store8 m r) = some τ')
    (e₁ : exec (.store8 m r) s₁ = some s₁') (e₂ : exec (.store8 m r) s₂ = some s₂') :
    addrs (.store8 m r) s₁ = addrs (.store8 m r) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, storeStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, State.store8] at e₁ e₂
  split at e₁ <;> [cases e₁; cases e₁]
  split at e₂ <;> [cases e₂; cases e₂]
  exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 1) hok (by decide) fun hp => by rw [ha.reg hp]⟩

theorem step_sound_alu {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {op : AluOp} {d : Reg} {src : Src}
    (ha : Agree τ s₁ s₂) (hs : step τ (.alu op d src) = some τ')
    (e₁ : exec (.alu op d src) s₁ = some s₁') (e₂ : exec (.alu op d src) s₂ = some s₂') :
    addrs (.alu op d src) s₁ = addrs (.alu op d src) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, aluStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  obtain ⟨-, hw₁, hm₁, -⟩ := exec_nonstore (d := d) rfl e₁
  obtain ⟨-, hw₂, hm₂, -⟩ := exec_nonstore (d := d) rfl e₂
  refine ⟨ha.srcAddrs hok, ha.keep ?_ rfl rfl hw₁ hw₂ hm₁ hm₂ (aluBases_ok ha.wf₁ e₁) (aluBases_ok ha.wf₂ e₂)
    noLo⟩
  simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
  exact alu_sound ha (fun s => s.gpr d) (fun s x => s.setReg d x) id
    (setReg_gpr_eq · d) (by simp [State.setReg]) (by simp)
    (fun hp => by rw [ha.readSrc hp, hb₂] at hb₁; cases hb₁; rfl) ho₁ ho₂

theorem step_sound_alu32 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {op : AluOp} {d : Reg} {src : Src}
    (ha : Agree τ s₁ s₂) (hs : step τ (.alu32 op d src) = some τ')
    (e₁ : exec (.alu32 op d src) s₁ = some s₁') (e₂ : exec (.alu32 op d src) s₂ = some s₂') :
    addrs (.alu32 op d src) s₁ = addrs (.alu32 op d src) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, aluStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  refine ⟨ha.srcAddrs hok, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => by rwa [aluBases_narrow] at h) rfl⟩
  simp only [exec, execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨b₁, hb₁, out₁, ho₁, rfl⟩ := e₁; obtain ⟨b₂, hb₂, out₂, ho₂, rfl⟩ := e₂
  exact alu_sound ha (fun s => (s.gpr d).setWidth 32) (fun s x => s.setReg32 d x)
    (fun h => by simp only [h]) (fun s x => setReg_gpr_eq s d _) (by simp [State.setReg32, State.setReg])
    (by simp [State.setReg32])
    (fun hp => by rw [ha.readSrc32 hp, hb₂] at hb₁; cases hb₁; rfl) ho₁ ho₂

theorem step_sound_shift32 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {op : ShiftOp} {d : Reg} {n : Nat}
    (ha : Agree τ s₁ s₂) (hs : step τ (.shift32 op d n) = some τ')
    (e₁ : exec (.shift32 op d n) s₁ = some s₁') (e₂ : exec (.shift32 op d n) s₂ = some s₂') :
    addrs (.shift32 op d n) s₁ = addrs (.shift32 op d n) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
  by_cases hn : 1 ≤ n ∧ n ≤ 31
  swap; · simp [exec, execShift32, hn] at e₁
  simp only [exec, execShift32, hn, and_self, ite_true] at e₁ e₂
  refine ⟨fun r hr => ?_, fun hf => ?_⟩
  · by_cases hrd : r = d
    · subst hrd
      have := ha.rf.1 r hr
      cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg32, State.setReg, this]
    · cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg32, State.setReg, State.setFlags, hrd, ha.rf.1 r hr]
  · simp only [Bool.and_eq_true] at hf
    have hd := ha.reg hf.2
    have hfl := ha.rf.2 hf.1
    cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
      simp [State.setReg32, State.setFlags, hd, hfl]

theorem step_sound_bswap32 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : Reg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.bswap32 d) = some τ')
    (e₁ : exec (.bswap32 d) s₁ = some s₁') (e₂ : exec (.bswap32 d) s₂ = some s₂') :
    addrs (.bswap32 d) s₁ = addrs (.bswap32 d) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  refine ⟨fun r hr => ?_, fun hf => by simpa [State.setReg32] using ha.rf.2 hf⟩
  by_cases hrd : r = d
  · subst hrd; simp [State.setReg32, State.setReg, ha.rf.1 r hr]
  · simp [State.setReg32, State.setReg, hrd, ha.rf.1 r hr]

theorem step_sound_movzx8 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : Reg} {m : MemOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.movzx8 d m) = some τ')
    (e₁ : exec (.movzx8 d m) s₁ = some s₁') (e₂ : exec (.movzx8 d m) s₂ = some s₂') :
    addrs (.movzx8 d m) s₁ = addrs (.movzx8 d m) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  refine ⟨by simp [addrs, ha.ea hok], ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
  simp only [exec, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
  exact ⟨regs_set (p := false) ha.rf.1 (fun h => by cases h), ha.rf.2⟩

theorem step_sound_bswap {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : Reg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.bswap d) = some τ')
    (e₁ : exec (.bswap d) s₁ = some s₁') (e₂ : exec (.bswap d) s₂ = some s₂') :
    addrs (.bswap d) s₁ = addrs (.bswap d) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  refine ⟨fun r hr => ?_, fun hf => by simpa using ha.rf.2 hf⟩
  by_cases hrd : r = d
  · subst hrd; simp [State.setReg, ha.rf.1 r hr]
  · simp [State.setReg, hrd, ha.rf.1 r hr]

theorem step_sound_shift {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {op : ShiftOp} {d : Reg} {n : Nat}
    (ha : Agree τ s₁ s₂) (hs : step τ (.shift op d n) = some τ')
    (e₁ : exec (.shift op d n) s₁ = some s₁') (e₂ : exec (.shift op d n) s₂ = some s₂') :
    addrs (.shift op d n) s₁ = addrs (.shift op d n) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
  by_cases hn : 1 ≤ n ∧ n ≤ 63
  swap; · simp [exec, execShift, hn] at e₁
  simp only [exec, execShift, hn, and_self, ite_true] at e₁ e₂
  refine ⟨fun r hr => ?_, fun hf => ?_⟩
  · by_cases hrd : r = d
    · subst hrd
      have := ha.rf.1 r hr
      cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg, this]
    · cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
        simp [State.setReg, State.setFlags, hrd, ha.rf.1 r hr]
  · simp only [Bool.and_eq_true] at hf
    have hd := ha.reg hf.2
    have hfl := ha.rf.2 hf.1
    cases op <;> simp only [Option.some.injEq] at e₁ e₂ <;> subst e₁ e₂ <;>
      simp [State.setReg, State.setFlags, hd, hfl]

theorem step_sound_movImm64 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : Reg} {v : BitVec 64}
    (ha : Agree τ s₁ s₂) (hs : step τ (.movImm64 d v) = some τ')
    (e₁ : exec (.movImm64 d v) s₁ = some s₁') (e₂ : exec (.movImm64 d v) s₂ = some s₂') :
    addrs (.movImm64 d v) s₁ = addrs (.movImm64 d v) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  refine ⟨rfl, ha.write rfl e₁ e₂ ?_ rfl rfl (fun _ h => h) rfl⟩
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  exact ⟨regs_set (p := true) ha.rf.1 fun _ => rfl, by simpa using ha.rf.2⟩

theorem step_sound_mul {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {r : Reg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.mul r) = some τ')
    (e₁ : exec (.mul r) s₁ = some s₁') (e₂ : exec (.mul r) s₂ = some s₂') :
    addrs (.mul r) s₁ = addrs (.mul r) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  exact ⟨rfl, ha.mul⟩

end VG.X86_64.Taint
