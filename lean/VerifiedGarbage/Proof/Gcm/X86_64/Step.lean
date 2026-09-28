import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# GHASH on x86-64: one step of Algorithm 1

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm
open VG.Spec.Gcm (Block)

theorem msb_shiftLeft (x : Block) (k : Nat) : (x <<< k).msb = x.getMsbD k := by
  rw [BitVec.msb_eq_getMsbD_zero, BitVec.getMsbD_shiftLeft, Nat.zero_add]

/-- The registers a step does not write. -/
def stepKeep : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp, .r14, .r15]

set_option simprocs false in
theorem step_ok (x : Block) (zv : Block × Block) (k : Nat) (s : State)
    (hx : s.gpr XH ++ s.gpr XL = x <<< k)
    (hzv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = zv)
    (hr : s.gpr RH = rHigh) :
    WP isa (.block step) s fun s' =>
      s'.gpr XH ++ s'.gpr XL = x <<< (k + 1) ∧
      (s'.gpr ZH ++ s'.gpr ZL, s'.gpr VH ++ s'.gpr VL) = mulStep x zv k ∧
      (∀ r ∈ stepKeep, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hzv
  simp only [XH, XL, ZH, ZL, VH, VL, RH] at hx hr ⊢
  apply WP.of_runBlock
  simp only [step, XH, XL, ZH, ZL, VH, VL, M, T, RH]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execShift, readSrc,
    isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · rw [shl1, hx, BitVec.shiftLeft_add]
  · rw [sbb_self, shl1_cf, hx, msb_shiftLeft, mask_z, hr, update_v]
    rfl
  · intro r hr
    simp only [stepKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_false]
  all_goals trivial

/-! ## The 128 steps -/

/-- The registers the multiplication does not write. -/
def keepRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

theorem keep_sub {r : Reg} (h : r ∈ keepRegs) : r ∈ stepKeep := by
  simp only [keepRegs, stepKeep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- After `k` steps of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (sB : State) (k : Nat) (s : State) : Prop where
  xr : s.gpr XH ++ s.gpr XL = x <<< k
  zv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = mulSteps x h k
  rh : s.gpr RH = rHigh
  keep : ∀ r ∈ keepRegs, s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem inner_step {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s) :
    WP isa (.block step) s fun s' => Inner x h sB (k + 1) s' ∧ s'.gpr CNT = s.gpr CNT := by
  refine WP.mono (step_ok x _ k s hs.xr hs.zv hs.rh) fun s' ⟨hx, hzv, hk, hm, hrd, hwr⟩ => ?_
  refine ⟨⟨hx, by rw [hzv, mulSteps_succ], by rw [hk _ (by simp [stepKeep, RH]), hs.rh],
    fun r hr => by rw [hk r (keep_sub hr), hs.keep r hr], by rw [hm, hs.mem], by rw [hrd, hs.rd],
    by rw [hwr, hs.wr]⟩, hk _ (by simp [stepKeep, CNT])⟩

theorem Inner.of_gpr {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s)
    {s' : State} (hg : ∀ r, r ≠ CNT → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inner x h sB k s' where
  xr := by rw [hg XH (by decide), hg XL (by decide)]; exact hs.xr
  zv := by rw [hg ZH (by decide), hg ZL (by decide), hg VH (by decide), hg VL (by decide)]; exact hs.zv
  rh := by rw [hg RH (by decide)]; exact hs.rh
  keep r hr := by
    have : r ≠ CNT := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hg r this]; exact hs.keep r hr
  mem := hm.trans hs.mem
  rd := hrd.trans hs.rd
  wr := hwr.trans hs.wr

set_option simprocs false in
theorem steps_ok {x h : Block} {sB : State} {j : Nat} (hj : j < 128 / unroll) {s : State}
    (hs : Inner x h sB (unroll * j) s) (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)) :
    WP isa (.block steps) s fun s' => Inner x h sB (unroll * (j + 1)) s' ∧
      s'.gpr CNT = BitVec.ofNat 64 (128 / unroll - (j + 1)) ∧
      s'.zf = some (BitVec.ofNat 64 (128 / unroll - (j + 1)) == 0) := by
  rw [steps, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := unroll)
    (fun k s' => Inner x h sB (unroll * j + k) s' ∧ s'.gpr CNT = s.gpr CNT)
    (fun k s' _ ⟨hs', hc'⟩ => WP.mono (inner_step hs') fun s'' ⟨h₁, h₂⟩ => ⟨h₁, h₂.trans hc'⟩)
    unroll le_rfl s ⟨hs, rfl⟩) fun s₁ ⟨hs₁, hc₁⟩ => ?_
  have e : 128 / unroll - j = (128 / unroll - (j + 1)) + 1 := by
    simp only [unroll] at hj ⊢; omega
  rw [e] at hc
  apply WP.of_runBlock
  simp only [CNT] at hc hc₁ ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, State.setReg, arithFlags, State.setFlags,
    ite_true, hc₁, hc, Option.bind_some, Option.some.injEq, exists_eq_left']
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hlt : 128 / unroll - (j + 1) < 2 ^ 64 := by simp only [unroll]; omega
  generalize 128 / unroll - (j + 1) = c at hlt ⊢
  have e2 : BitVec.ofNat 64 (c + 1) - 1 = BitVec.ofNat 64 c := by bv_omega
  rw [e1, e2]
  refine ⟨?_, rfl, rfl⟩
  rw [Nat.mul_succ]
  exact hs₁.of_gpr (fun r hr => ite_eq_right hr) rfl rfl rfl

/-- The loop of `128 / unroll` iterations: all 128 steps. -/
theorem mul_ok {x h : Block} {sB s : State} (hs : Inner x h sB 0 s)
    (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll)) :
    WP isa (.loop (.block steps) .ne) s (Inner x h sB 128) := by
  let Inv : Nat → State → Prop := fun m s =>
    ∃ j, m = 128 / unroll - j ∧ j < 128 / unroll ∧ Inner x h sB (unroll * j) s ∧
      s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)
  refine WP.loop (M := isa) Inv (fun m s ⟨j, hm, hj, hs, hc⟩ => ?_) _ s
    ⟨0, rfl, by decide, hs, hc⟩
  subst hm
  refine WP.mono (steps_ok hj hs hc) fun s' ⟨hs', hc', hz'⟩ => ?_
  have hev : isa.eval .ne s' = some (!(BitVec.ofNat 64 (128 / unroll - (j + 1)) == 0)) := by
    show eval .ne s' = _
    simp only [eval, hz', Option.map_some]
  by_cases hlast : j + 1 = 128 / unroll
  · left
    rw [hlast, Nat.sub_self] at hev
    refine ⟨by rw [hev]; decide, ?_⟩
    rw [hlast] at hs'
    exact hs'
  · right
    have hne : BitVec.ofNat 64 (128 / unroll - (j + 1)) ≠ 0 := by
      simp only [unroll] at hlast hj ⊢
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine ⟨by rw [hev]; simpa using hne, _, by omega, j + 1, rfl, by omega, hs', hc'⟩

end VG.Proof.Gcm.X86_64
