import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA on x86-64: the loop over the coefficients

`mapLoop body` runs `body` for `rcx` = 256 down to 1, and iteration `i` (from 0)
handles coefficient `255 - i` at `[p + 4·rcx - 4]` (`cfAddr`) of each
polynomial `p`. `loop_ok` proves it once for every function: from a body that
writes, to coefficient `255 - i` of each output polynomial (in a register of
`outs`), the value `V o (255 - i)` and keeps an invariant `J` of its other
registers, the loop writes every coefficient of each output. The inputs
(registers `ins`) are never written, so the body reads the coefficients of the
initial memory (`Inv.read`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep wp_countdown setReg_gpr setReg_mem ofNat64_pred)

/-! ## Addresses -/

/-- `p + 4c - 4`, the address of `cf p` when `rcx = c`. -/
def cfAddr (p c : Addr) : Addr := p + c * BitVec.ofNat 64 4 + BitVec.ofInt 64 (-4)

theorem ea_cf (s : State) (p : Reg) : s.ea (cf p) = cfAddr (s.gpr p) (s.gpr .rcx) := rfl

theorem cfAddr_eq (p : Addr) (j : Nat) :
    cfAddr p (BitVec.ofNat 64 (j + 1)) = coeffAddr p j := by
  unfold cfAddr coeffAddr
  rw [BitVec.add_assoc]
  refine congrArg (p + ·) ?_
  have e : BitVec.ofInt 64 (-4) = -BitVec.ofNat 64 4 := by decide
  rw [e, ← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## The writes of an iteration -/

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    writes m (p :: ps) = writes (m.writeW p.1 p.2) ps := rfl

section
variable (P : Reg → Addr)

/-- Writes to coefficient `j` of polynomials disjoint from that at `p` leave it unchanged. -/
theorem coeffAt_writes_disjoint (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    {p : Addr} (hd : ∀ o ∈ outs, (pR p).Disjoint (pR (P o))) {k : Nat} (hk : k < 256) :
    coeffAt (writes m (outs.map fun o => (coeffAddr (P o) j, V o))) p k = coeffAt m p k := by
  induction outs generalizing m with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, writes_cons]
    rw [ih _ fun o' h => hd o' (List.mem_cons_of_mem _ h),
      coeffAt_writeW_disjoint m (hd o List.mem_cons_self) (coeff_contains _ hj) hk]

theorem coeffAt_writes (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    (hpw : outs.Pairwise fun a b => (pR (P a)).Disjoint (pR (P b))) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) :
    coeffAt (writes m (outs.map fun o => (coeffAddr (P o) j, V o))) (P o) k =
      if j = k then V o else coeffAt m (P o) k := by
  induction outs generalizing m with
  | nil => cases ho
  | cons o' os ih =>
    rw [List.map_cons, writes_cons]
    rw [List.pairwise_cons] at hpw
    by_cases hr : o ∈ os
    · rw [ih _ hpw.2 hr]
      have hd : (pR (P o)).Disjoint (pR (P o')) := (hpw.1 o hr).symm
      rw [coeffAt_writeW_disjoint m hd (coeff_contains _ hj) hk]
    · obtain rfl : o = o' := by simpa [hr] using ho
      rw [coeffAt_writes_disjoint P _ os j hj V (fun o' h => hpw.1 o' h) hk, coeffAt_writeW m _ hk hj]

theorem frame_writes {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m) (outs : List Reg) (j : Nat)
    (hj : j < 256) (V : Reg → BitVec 32) (hin : ∀ o ∈ outs, pR (P o) ∈ rs) :
    Frame rs m₀ (writes m (outs.map fun o => (coeffAddr (P o) j, V o))) := by
  induction outs generalizing m with
  | nil => exact hf
  | cons o os ih =>
    rw [List.map_cons, writes_cons]
    exact ih (hf.writeW (hin o List.mem_cons_self) _ (coeff_contains _ hj)) fun o' h =>
      hin o' (List.mem_cons_of_mem _ h)

end

/-! ## The loop -/

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (s₀.gpr o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr o))
  pw : outs.Pairwise fun a b => (pR (s₀.gpr a)).Disjoint (pR (s₀.gpr b))

/-- After `i` iterations: the registers `fixed` are unchanged, the outputs
hold their values from coefficient `256 - i` on, and `J i`. -/
structure Inv (s₀ : State) (fixed outs : List Reg) (V : Reg → Nat → BitVec 32) (J : Nat → State → Prop)
    (i : Nat) (s : State) : Prop where
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (outs.map fun o => pR (s₀.gpr o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k, 256 - i ≤ k → k < 256 → coeffAt s.mem (s₀.gpr o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs fixed : List Reg} {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop}
  {i : Nat} {s : State}

/-- The address of the coefficient that iteration `i` handles. -/
theorem Inv.addr (hI : Inv s₀ fixed outs V J i s) (hc : s.gpr .rcx = BitVec.ofNat 64 (256 - i)) (hi : i < 256)
    {p : Reg} (hp : p ∈ fixed) : cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₀.gpr p) (255 - i) := by
  rw [hI.fixed p hp, hc, show 256 - i = 255 - i + 1 by omega]
  exact cfAddr_eq _ _

theorem Inv.inR (hL : Layout s₀ ins outs) (hI : Inv s₀ fixed outs V J i s) {p : Reg} (hp : p ∈ ins) {k : Nat}
    (hk : k < 256) : InRegions (s.rd ++ s.wr) (coeffAddr (s₀.gpr p) k) 4 := by
  rw [hI.rd, hI.wr]
  exact ⟨_, hL.rd p hp, coeff_contains _ hk⟩

theorem Inv.inW (hL : Layout s₀ ins outs) (hI : Inv s₀ fixed outs V J i s) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) : InRegions s.wr (coeffAddr (s₀.gpr o) k) 4 := by
  rw [hI.wr]
  exact ⟨_, hL.wr o ho, coeff_contains _ hk⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : Layout s₀ ins outs) (hI : Inv s₀ fixed outs V J i s) {p : Reg} (hp : p ∈ ins) {k : Nat}
    (hk : k < 256) : s.mem.readW (coeffAddr (s₀.gpr p) k) 32 = coeffAt s₀.mem (s₀.gpr p) k :=
  coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hp o ho) hk

end

/-- The loop, from a body that writes `V o (255 - i)` to coefficient `255 - i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs fixed clob : List Reg} {body : List Instr} {V : Reg → Nat → BitVec 32}
    {J : Nat → State → Prop} (hL : Layout s₀ ins outs) (hfix : ∀ r ∈ fixed, r ∉ clob) (hcx : .rcx ∈ clob)
    (hJ : ∀ s, s.gpr .rcx = BitVec.ofNat 64 256 → s.mem = s₀.mem → Keep [.rcx] s₀ s → J 0 s)
    (hbody : ∀ i < 256, ∀ s, Inv s₀ fixed outs V J i s → s.gpr .rcx = BitVec.ofNat 64 (256 - i) →
      WP isa (.block (body ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = writes s.mem (outs.map fun o => (coeffAddr (s₀.gpr o) (255 - i), V o (255 - i))) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ J (i + 1) s') ∧
        Keep clob s s') :
    WP isa (mapLoop body) s₀ (Inv s₀ fixed outs V J 256) := by
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s => s.mem = s₀.mem ∧ s.gpr .rcx = BitVec.ofNat 64 256)
    (by apply WP.of_runBlock; simp [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      setReg_gpr, setReg_mem]) (by decide)) fun s₁ ⟨⟨hm, hc⟩, hk⟩ => ?_)
  have h0 : Inv s₀ fixed outs V J 0 s₁ := by
    refine ⟨fun r hr => hk.gpr fun h => ?_, hk.2.1, hk.2.2, ?_, fun _ _ k h₁ h₂ => absurd h₂ (by omega),
      hJ s₁ hc hm hk⟩
    · simp only [List.mem_singleton] at h
      subst h
      exact hfix _ hr hcx
    · rw [hm]; exact Frame.refl _ _
  refine wp_countdown (cnt := .rcx) (N := 256) (by decide) (by decide) (Inv s₀ fixed outs V J)
    (fun i hi s hI hc => ?_) (fun _ h => h) h0 hc
  · refine WP.mono (hbody i hi s hI hc) fun s' ⟨⟨hm', hc', hz', hJ'⟩, hk'⟩ => ⟨?_, hc', hz'⟩
    refine ⟨fun r hr => (hk'.gpr (hfix r hr)).trans (hI.fixed r hr), hk'.2.1.trans hI.rd, hk'.2.2.trans hI.wr,
      ?_, fun o ho k h₁ h₂ => ?_, hJ'⟩
    · rw [hm']
      exact frame_writes _ hI.frame outs _ (by omega) _ fun o ho => List.mem_map_of_mem ho
    · rw [hm', coeffAt_writes _ _ outs _ (by omega) _ hL.pw ho h₂]
      split
      · subst k; rfl
      · exact hI.done o ho k (by omega) h₂

end VG.Proof.MlDsa.X86_64.Round
