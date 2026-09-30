import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA on 32-bit ARM: the loop over the coefficients

Untrusted: everything here is checked by Lean. `mapLoop cnt body` runs
`body` 256 times, `cnt` counting down, and iteration `i` handles coefficient
`i` of each polynomial, whose pointer (a register of `ptrs`) the body
advances by 4 bytes. `loop_ok` proves it once for every function: from a
body that writes, to coefficient `i` of each output polynomial (in a
register of `outs`), the value `V o i` and keeps an invariant `J` of its
other registers, the loop writes every coefficient of each output. The
inputs (registers `ins`) are never written, so the body reads the
coefficients of the initial memory (`Inv.read`).
-/

namespace VG.Proof.MlDsa.Arm.Round

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (coeffAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)

/-- The address of the polynomial whose pointer is `r` in `s`. -/
abbrev P (s : State) (r : Reg) : Addr := State.addr (s.gpr r)

/-- A reduced word is the element of `ℤ_q` it represents. -/
theorem word_of_reduced {v : BitVec 32} (h : v.toNat < VG.Spec.MlDsa.q) :
    BitVec.ofNat 32 (Fin.ofNat VG.Spec.MlDsa.q v.toNat).val = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt v.isLt]

/-! ## The writes of an iteration -/

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    writes m (p :: ps) = writes (m.writeW p.1 p.2) ps := rfl

theorem writes_nil (m : Mem) : writes m [] = m := rfl

section
variable (Pa : Reg → Addr)

theorem coeffAt_writes_disjoint (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    {p : Addr} (hd : ∀ o ∈ outs, (pR p).Disjoint (pR (Pa o))) {k : Nat} (hk : k < 256) :
    coeffAt (writes m (outs.map fun o => (coeffAddr (Pa o) j, V o))) p k = coeffAt m p k := by
  induction outs generalizing m with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, writes_cons]
    rw [ih _ fun o' h => hd o' (List.mem_cons_of_mem _ h),
      coeffAt_writeW_disjoint m (hd o List.mem_cons_self) (coeff_contains _ hj) hk]

theorem coeffAt_writes (m : Mem) (outs : List Reg) (j : Nat) (hj : j < 256) (V : Reg → BitVec 32)
    (hpw : outs.Pairwise fun a b => (pR (Pa a)).Disjoint (pR (Pa b))) {o : Reg} (ho : o ∈ outs) {k : Nat}
    (hk : k < 256) :
    coeffAt (writes m (outs.map fun o => (coeffAddr (Pa o) j, V o))) (Pa o) k =
      if j = k then V o else coeffAt m (Pa o) k := by
  induction outs generalizing m with
  | nil => cases ho
  | cons o' os ih =>
    rw [List.map_cons, writes_cons]
    rw [List.pairwise_cons] at hpw
    by_cases hr : o ∈ os
    · rw [ih _ hpw.2 hr]
      have hd : (pR (Pa o)).Disjoint (pR (Pa o')) := (hpw.1 o hr).symm
      rw [coeffAt_writeW_disjoint m hd (coeff_contains _ hj) hk]
    · obtain rfl : o = o' := by simpa [hr] using ho
      rw [coeffAt_writes_disjoint Pa _ os j hj V (fun o' h => hpw.1 o' h) hk, coeffAt_writeW m _ hk hj]

theorem frame_writes {rs : List Region} {m₀ m : Mem} (hf : Frame rs m₀ m) (outs : List Reg) (j : Nat)
    (hj : j < 256) (V : Reg → BitVec 32) (hin : ∀ o ∈ outs, pR (Pa o) ∈ rs) :
    Frame rs m₀ (writes m (outs.map fun o => (coeffAddr (Pa o) j, V o))) := by
  induction outs generalizing m with
  | nil => exact hf
  | cons o os ih =>
    rw [List.map_cons, writes_cons]
    exact ih (hf.writeW (hin o List.mem_cons_self) _ (coeff_contains _ hj)) fun o' h =>
      hin o' (List.mem_cons_of_mem _ h)

end

/-! ## The loop -/

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs, none wrapping
around. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (P s₀ p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (P s₀ o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (P s₀ p)).Disjoint (pR (P s₀ o))
  pw : outs.Pairwise fun a b => (pR (P s₀ a)).Disjoint (pR (P s₀ b))
  fit : ∀ p ∈ ins ++ outs, (s₀.gpr p).toNat + 1024 ≤ 2 ^ 32

/-- After `i` iterations: the pointers `ptrs` at coefficient `i`, `cnt` at
`256 - i`, the registers `fixed` unchanged, the outputs holding their values
below coefficient `i`, and `J i`. -/
structure Inv (s₀ : State) (ptrs fixed outs : List Reg) (cnt : Reg) (V : Reg → Nat → BitVec 32)
    (J : Nat → State → Prop) (i : Nat) (s : State) : Prop where
  ptr : ∀ p ∈ ptrs, s.gpr p = s₀.gpr p + BitVec.ofNat 32 (4 * i)
  cnt : s.gpr cnt = BitVec.ofNat 32 (1 * (256 - i))
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (outs.map fun o => pR (P s₀ o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k < i, coeffAt s.mem (P s₀ o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs ptrs fixed : List Reg} {cnt : Reg} {V : Reg → Nat → BitVec 32}
  {J : Nat → State → Prop} {i : Nat} {s : State}

/-- The address a pointer `p` of the loop points at in iteration `i`. -/
theorem Inv.addr (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {p : Reg}
    (hp : p ∈ ptrs) (hio : p ∈ ins ++ outs) :
    State.addr (s.gpr p + BitVec.ofNat 32 0) = coeffAddr (P s₀ p) i := by
  have := hL.fit p hio
  rw [hI.ptr p hp, addr_ptr _ _ _ (by omega), Nat.add_zero]

theorem Inv.inR (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {p : Reg}
    (hp : p ∈ ptrs) (hin : p ∈ ins) : InRegions (s.rd ++ s.wr) (State.addr (s.gpr p + BitVec.ofNat 32 0)) 4 := by
  rw [hI.addr hL hi hp (List.mem_append_left _ hin), hI.rd, hI.wr]
  exact ⟨_, hL.rd p hin, coeff_contains _ (by rw [n_eq]; exact hi)⟩

theorem Inv.inW (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {o : Reg}
    (hp : o ∈ ptrs) (ho : o ∈ outs) : InRegions s.wr (State.addr (s.gpr o + BitVec.ofNat 32 0)) 4 := by
  rw [hI.addr hL hi hp (List.mem_append_right _ ho), hI.wr]
  exact ⟨_, hL.wr o ho, coeff_contains _ (by rw [n_eq]; exact hi)⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs cnt V J i s) (hi : i < 256) {p : Reg}
    (hp : p ∈ ptrs) (hin : p ∈ ins) :
    s.mem.readW (State.addr (s.gpr p + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (P s₀ p) i := by
  rw [hI.addr hL hi hp (List.mem_append_left _ hin), ← coeffAt_eq]
  exact coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hin o ho) (by rw [n_eq]; exact hi)

end

/-- What an iteration does: it writes `V o i` to coefficient `i` of each
output, advances the pointers, counts down, keeps the registers `fixed`,
and establishes `J (i + 1)`. -/
def Step (s₀ : State) (ptrs fixed outs : List Reg) (cnt : Reg) (V : Reg → Nat → BitVec 32)
    (J : Nat → State → Prop) (i : Nat) (s s' : State) : Prop :=
  s'.mem = writes s.mem (outs.map fun o => (coeffAddr (P s₀ o) i, V o i)) ∧
    (∀ p ∈ ptrs, s'.gpr p = s.gpr p + 4) ∧ s'.gpr cnt = s.gpr cnt - 1 ∧ s'.z = (s.gpr cnt - 1 == 0) ∧
    (∀ r ∈ fixed, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ J (i + 1) s'

/-- The loop, from a body that writes `V o i` to coefficient `i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs ptrs fixed : List Reg} {cnt : Reg} {body : List Instr}
    {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop} (hL : Layout s₀ ins outs)
    (hcf : cnt ∉ fixed) (hcp : cnt ∉ ptrs)
    (hJ : ∀ s, s.gpr = (fun r => if r = cnt then BitVec.ofNat 32 256 else s₀.gpr r) → s.mem = s₀.mem →
      J 0 s)
    (hbody : ∀ i < 256, ∀ s, Inv s₀ ptrs fixed outs cnt V J i s →
      WP isa (.block body) s (Step s₀ ptrs fixed outs cnt V J i s)) :
    WP isa (mapLoop cnt body) s₀ (Inv s₀ ptrs fixed outs cnt V J 256) := by
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine wp_loop_ne (Inv s₀ ptrs fixed outs cnt V J) (N := 256) (by decide)
    (fun i hi s hI => WP.mono (hbody i hi s hI) fun s' ⟨hm, hp, hc, hz, hf, rd, wr, sp, hJ'⟩ => ?_)
    (fun _ h => h) ?_
  · refine ⟨⟨fun p hp' => ?_, ?_, fun r hr => (hf r hr).trans (hI.fixed r hr), rd.trans hI.rd, wr.trans hI.wr,
      sp.trans hI.sp, ?_, fun o ho k hk => ?_, hJ'⟩, ?_⟩
    · rw [hp p hp', hI.ptr p hp', BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        ← BitVec.ofNat_add, Nat.mul_succ]
    · rw [hc, hI.cnt]; exact count_sub (k := 1) hi
    · rw [hm]
      exact frame_writes _ hI.frame outs _ hi _ fun o ho => List.mem_map_of_mem ho
    · rw [hm, coeffAt_writes _ _ outs _ hi _ hL.pw ho (by omega)]
      split
      · subst k; rfl
      · exact hI.done o ho k (by omega)
    · rw [hz, hI.cnt]; exact count_z (k := 1) hi (by decide) (by decide)
  · refine ⟨fun p hp => ?_, by simp [State.setReg], fun r hr => ?_, rfl, rfl, rfl, Frame.refl _ _,
      fun _ _ k hk => absurd hk (Nat.not_lt_zero k), hJ _ ?_ rfl⟩
    · have : p ≠ cnt := fun e => hcp (e ▸ hp)
      simp [State.setReg, this]
    · have : r ≠ cnt := fun e => hcf (e ▸ hr)
      simp [State.setReg, this]
    · funext r; rfl

end VG.Proof.MlDsa.Arm.Round
