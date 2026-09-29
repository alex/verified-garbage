import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Impl.MlKem.X86_64.Common

/-!
# ML-KEM on x86-64: running blocks symbolically

Untrusted: everything here is checked by Lean.

A block is run with `xrun`, a `simp only` that steps it one instruction at
a time (`runBlock_cons`, `runStep_some`) and keeps the state a chain of
`State.setReg`, `State.setFlags` and memory updates, whose projections the
lemmas here evaluate: so the state stays small, and a register of the
result is the value last written to it. Memory operands are `at_ b d`,
whose address is `b + d` (`ea_at`); a block lemma takes the accesses it
makes as hypotheses on the registers of the state it starts from.

`Keep rs s s'` says that `s'` differs from `s` only in the registers `rs`
(and the flags and memory).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Impl.MlKem.X86_64 (at_ qImm)

/-! ## Projections of the state updates -/

section
variable (s : State) (d r : Reg) (v : BitVec 64) (cf o zf sf : Option Bool) (m : Mem)

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
theorem arithFlags_eq {w : Nat} (x : BitVec w) (c o : Bool) :
    arithFlags s x c o = s.setFlags (some c) (some o) (some (x == 0)) (some x.msb) := rfl

end

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

/-- A pointer advanced by `c` bytes, `c < 2³¹` (an immediate). -/
theorem ptr_step (p : Addr) (i c : Nat) :
    p + BitVec.ofNat 64 (c * i) + BitVec.ofNat 64 c = p + BitVec.ofNat 64 (c * (i + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add]

/-! ## Immediates, sign-extended -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem sx2 : BitVec.signExtend 64 (2 : BitVec 32) = 2 := by decide
theorem sx3 : BitVec.signExtend 64 (3 : BitVec 32) = 3 := by decide
theorem sx4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
theorem sx5 : BitVec.signExtend 64 (5 : BitVec 32) = 5 := by decide
theorem sx8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
theorem sx16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
theorem sx32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
theorem sxQ : BitVec.signExtend 64 qImm = 3329 := by decide

/-! ## Memory accesses -/

section
variable {s : State} {a : Addr}

theorem load64_eq (h : InRegions (s.rd ++ s.wr) a 8) : s.load64 a = some (s.mem.readW a 64) := by
  simp [State.load64, h]
theorem load32_eq (h : InRegions (s.rd ++ s.wr) a 4) : s.load32 a = some (s.mem.readW a 32) := by
  simp [State.load32, h]
theorem load8_eq (h : InRegions (s.rd ++ s.wr) a 1) : s.load8 a = some (s.mem a) := by
  simp [State.load8, h]
theorem store64_eq (h : InRegions s.wr a 8) (v : BitVec 64) :
    s.store64 a v = some { s with mem := s.mem.writeW a v } := by simp [State.store64, h]
theorem store32_eq (h : InRegions s.wr a 4) (v : BitVec 32) :
    s.store32 a v = some { s with mem := s.mem.writeW a v } := by simp [State.store32, h]
theorem store8_eq (h : InRegions s.wr a 1) (v : Byte) :
    s.store8 a v = some { s with mem := s.mem.writeW a v } := by simp [State.store8, h]

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
        readSrc32, execAlu, execAlu32, execShift, execShift32, execMul, State.setReg32, arithFlags_eq,
        ea_at, add_ofNat_zero, State.load64, State.load32, State.load8, State.store64, State.store32,
        State.store8, setReg_gpr, setReg_mem, setReg_rd, setReg_wr, setReg_cf, setReg_zf,
        setFlags_gpr, setFlags_mem, setFlags_rd, setFlags_wr, setFlags_cf, setFlags_zf,
        Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
        ite_false, reduceCtorEq, BitVec.setWidth_32_64_32, BitVec.sub_self, sx1, sx2, sx3, sx4, sx5, sx8,
        sx16, sx32, sxQ, $ls,*]))

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
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

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
  have := List.all_eq_true.mp (hc i hi) r (mem_allRegs r)
  simp only [Bool.or_eq_true, List.contains_iff_mem, hr, false_or, Bool.not_eq_true'] at this
  exact this

/-- The calling-convention obligations of code that writes only the
registers `rs`, none callee-saved, and memory only within regions `ws`
disjoint from the return address. -/
theorem gprPreserved_of {s s' : State} {rs : List Reg} (hk : Keep rs s s')
    (hcs : ∀ r ∈ calleeSaved, r ∉ rs) {ws : List Region} (hf : Frame ws s.mem s'.mem)
    (hret : ∀ r ∈ ws, Region.Disjoint ⟨s.gpr .rsp, 8⟩ r) : gprPreserved s s' :=
  ⟨fun r hr => hk.gpr (hcs r hr), hf.readW (Region.contains_self _ _) hret (by decide)⟩

/-! ## Arithmetic modulo `q` -/

theorem qImm_toNat : qImm.toNat = 3329 := rfl

/-- The value `csubQ` leaves: `v - q`, plus `q` masked by the borrow. -/
theorem csub_val {v : BitVec 32} (hv : v.toNat < 2 * 3329) (m : BitVec 32) :
    (v - qImm + (m - m - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < qImm.toNat))) &&& qImm)).toNat
      = if 3329 ≤ v.toNat then v.toNat - 3329 else v.toNat := by
  rw [BitVec.sub_self, qImm_toNat]
  split
  · rename_i h
    have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < 3329))) &&& qImm) = 0 := by
      rw [decide_eq_false (by omega)]; decide
    rw [e]
    unfold qImm
    bv_omega
  · rename_i h
    have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (v.toNat < 3329))) &&& qImm) = qImm := by
      rw [decide_eq_true (by omega)]; decide
    rw [e]
    unfold qImm
    bv_omega

/-! ## Counted loops -/

theorem ofNat64_pred {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (1 : BitVec 64).toNat = 1 := rfl
  rw [this]
  omega

theorem ofNat64_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- A loop whose body counts `cnt` down by one (setting ZF, as its last
instruction `sub cnt, 1` does), from `N`: the body runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop) {Q : State → Prop}
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - 1 ∧
        s'.zf = some (s.gpr cnt - 1 == 0))
    (hQ : ∀ s, Inv N s → Q s) {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = N - i ∧ i < N ∧ Inv i s ∧
    s.gpr cnt = BitVec.ofNat 64 (N - i)) ?_ N s ⟨0, rfl, hN0, h0, by rw [Nat.sub_zero]; exact hc⟩
  rintro n s ⟨i, rfl, hi, hI, hcnt⟩
  refine WP.mono (hbody i hi s hI hcnt) fun s' ⟨hI', hc', hz'⟩ => ?_
  rw [hcnt, ofNat64_pred (by omega) (by omega)] at hc' hz'
  have hev : isa.eval .ne s' = some (!decide (N - i - 1 = 0)) := by
    simp only [eval, hz', ofNat64_beq_zero (show N - i - 1 < 2 ^ 64 by omega), Option.map_some]
  by_cases he : i + 1 = N
  · subst he
    exact .inl ⟨by rw [hev]; simp, hQ s' hI'⟩
  · exact .inr ⟨by rw [hev]; simp; omega, N - (i + 1), by omega, i + 1, rfl, by omega, hI',
      by rw [hc']; congr 1⟩

end VG.Proof.MlKem.X86_64
