import VerifiedGarbage.Proof.MlKem.X86.Common

/-!
# ML-DSA on x86 (32-bit): running blocks symbolically

Untrusted: everything here is checked by Lean.

A block is run with `xrun`, a `simp only` that steps it one instruction at
a time (`runBlock_cons`, `runStep_some`) and keeps the state a chain of
`State.setReg`, `State.setFlags` and memory updates, whose projections the
lemmas here evaluate: so the state stays small, and a register of the
result is the value last written to it. Memory operands are `at_ b d`,
whose address is `addr (s.gpr b) d` (`ea_at`); a block lemma takes the
accesses it makes as hypotheses on the registers of the state it starts
from. (As ML-KEM's `xrun` on x86-64, for the 32-bit model.)

`Keep rs s s'` says that `s'` differs from `s` only in the registers `rs`
(and the flags and memory), and `WP.keep` proves it of code none of whose
instructions writes another register.
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86

/-! ## Projections of the state updates -/

section
variable (s : State) (d r : Reg) (v : BitVec 32) (cf o zf sf : Option Bool)

theorem setReg_gpr : (s.setReg d v).gpr r = if r = d then v else s.gpr r := rfl
theorem setReg_mem : (s.setReg d v).mem = s.mem := rfl
theorem setReg_rd : (s.setReg d v).rd = s.rd := rfl
theorem setReg_wr : (s.setReg d v).wr = s.wr := rfl
theorem setReg_cf : (s.setReg d v).cf = s.cf := rfl
theorem setReg_zf : (s.setReg d v).zf = s.zf := rfl
theorem setFlags_gpr : (s.setFlags cf o zf sf).gpr = s.gpr := rfl
theorem setFlags_mem : (s.setFlags cf o zf sf).mem = s.mem := rfl
theorem setFlags_rd : (s.setFlags cf o zf sf).rd = s.rd := rfl
theorem setFlags_wr : (s.setFlags cf o zf sf).wr = s.wr := rfl
theorem setFlags_cf : (s.setFlags cf o zf sf).cf = cf := rfl
theorem setFlags_zf : (s.setFlags cf o zf sf).zf = zf := rfl
theorem arithFlags_eq (x : BitVec 32) (c o : Bool) :
    arithFlags s x c o = s.setFlags (some c) (some o) (some (x == 0)) (some x.msb) := rfl

end

/-! ## Running a block -/

/-- Steps a block from a state whose accesses the hypotheses `ls` permit. -/
syntax "xrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| xrun) => `(tactic| xrun [])
  | `(tactic| xrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, execShift, arithFlags_eq, Proof.MlKem.X86.ea_at, State.load32, State.load8, State.store32,
        State.store8, Reg8.reg, setReg_gpr, setReg_mem, setReg_rd, setReg_wr, setReg_cf, setReg_zf,
        setFlags_gpr, setFlags_mem, setFlags_rd, setFlags_wr, setFlags_cf, setFlags_zf,
        Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
        ite_false, reduceCtorEq, BitVec.sub_self, true_and, and_true, $ls,*]))

/-! ## What a block keeps -/

/-- `s'` differs from `s` only in the registers `rs` (flags and memory
aside), with the same permissions. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs' s₂ s₃) :
    Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

/-- Every register. -/
def allRegs : List Reg := [.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

/-- Whether no instruction of `c` writes a register outside `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => allRegs.all fun r => rs.contains r || !Taint.clobbers i r

/-- A register that no instruction writes keeps its value. -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) : WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he, (Exec.rdwr he).1, (Exec.rdwr he).2⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := List.all_eq_true.mp (hc i (instrs_eq_instrs c ▸ hi)) r (mem_allRegs r)
  simp only [Bool.or_eq_true, List.contains_iff_mem, hr, false_or, Bool.not_eq_true'] at this
  exact this

/-! ## Values -/

/-- The byte a `store8` stores. -/
theorem b8_eq (x : BitVec 32) : BitVec.setWidth 8 x = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte, zero-extended. -/
theorem toNat_setWidth32_8 (x : BitVec 8) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

/-- A 32-bit pointer plus `d`, where nothing wraps around, as an address. -/
theorem addr_of_fit {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    addr x d = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-- A pointer advanced by `c` bytes. -/
theorem ptr_step (p : BitVec 32) (i c : Nat) :
    p + BitVec.ofNat 32 (c * i) + BitVec.ofNat 32 c = p + BitVec.ofNat 32 (c * (i + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add]

end VG.Proof.MlDsa.X86.Pack
