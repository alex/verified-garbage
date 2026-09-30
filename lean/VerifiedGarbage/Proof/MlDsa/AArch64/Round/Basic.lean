import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-!
# ML-DSA on AArch64: what the rounding proofs share

Untrusted: everything here is checked by Lean.

* For each function, a contract with the facts of its shared contract
  (`Spec/MlDsa/Poly.lean`) spelled out for AArch64: the arguments in their
  registers, the permitted regions, their disjointness, and the
  postcondition. `Verified.of_correct` moves a proof to the shared
  contract, which implies it (`mldsa_implies`).
* `mapLoop ptrs cnt body` runs `body` for coefficients `0, …, 255`, with the
  pointers `ptrs` at coefficient `i` of their polynomials. `loop_ok` proves
  it once for every function: from a body that writes, to coefficient `i`
  of each output polynomial (the registers `outs`), the value `V o i`, and
  keeps an invariant `J` of its other registers, the loop writes every
  coefficient of each output. The inputs (registers `ins`) are never
  written, so the body reads the coefficients of the initial memory
  (`Inv.read`).
* The functions with `γ₂` first zero-extend it (`zext`): `zext_ok` runs it,
  and `zext_ct` proves constant time from the taint of the rest, where the
  whole register is public. `onGamma_ok` runs the branch on `γ₂`.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (writesOnly movW_ok wp_countdown Qv)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (coeffAt polyAt Reduced PolyIs NatPolyIs HintIs hintAt gamma2s power2Round highBits
  lowBits normRq makeHint useHint hintOnes ofInt n)

/-! ## The contracts -/

/-- A `u32` argument in `r`. -/
abbrev arg32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_power2round(t = x0, t1 = x1, t0 = x2)`. -/
def power2RoundK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x0)] ∧ s.wr = [pR (s.gpr .x1), pR (s.gpr .x2)] ∧
    (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)) ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)) ∧
    (pR (s.gpr .x1)).Disjoint (pR (s.gpr .x2)) ∧ Reduced s.mem (s.gpr .x0)
  post s s' :=
    NatPolyIs s'.mem (s.gpr .x1) ((polyAt s.mem (s.gpr .x0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (s.gpr .x2) ((polyAt s.mem (s.gpr .x0)).map fun c => ofInt (power2Round c).2)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- `r = x0, gamma2 = w1, out = x2`, with the postcondition `post`. -/
def bitsK (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x0)] ∧ s.wr = [pR (s.gpr .x2)] ∧ (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)) ∧
    arg32 s .x1 ∈ gamma2s ∧ Reduced s.mem (s.gpr .x0)
  post := post
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_high_bits(r = x0, gamma2 = w1, out = x2)`. -/
def highBitsK : Contract isa := bitsK fun s s' =>
  NatPolyIs s'.mem (s.gpr .x2) ((polyAt s.mem (s.gpr .x0)).map fun c => (highBits (arg32 s .x1) c).toNat)

/-- `vg_mldsa_low_bits(r = x0, gamma2 = w1, out = x2)`. -/
def lowBitsK : Contract isa := bitsK fun s s' =>
  PolyIs s'.mem (s.gpr .x2) ((polyAt s.mem (s.gpr .x0)).map fun c => ofInt (lowBits (arg32 s .x1) c))

/-- `vg_mldsa_norm_lt(f = x0, bound = w1)`. -/
def normLtK : Contract isa where
  pre s := s.rd = [pR (s.gpr .x0)] ∧ s.wr = [] ∧ Reduced s.mem (s.gpr .x0)
  post s s' := (s'.gpr .x0).setWidth 32 = if normRq [polyAt s.mem (s.gpr .x0)] < arg32 s .x1 then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.sp = s₂.sp

/-- `a = x0, b = x1, gamma2 = w2, out = x3`, with the precondition `pre'` on
the memory and the postcondition `post`. -/
def hintK (pre' : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .x0), pR (s.gpr .x1)] ∧ s.wr = [pR (s.gpr .x3)] ∧
    (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x3)) ∧ (pR (s.gpr .x1)).Disjoint (pR (s.gpr .x3)) ∧
    arg32 s .x2 ∈ gamma2s ∧ pre' s
  post := post
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_make_hint(z = x0, r = x1, gamma2 = w2, h = x3)`. -/
def makeHintK : Contract isa :=
  hintK (fun s => Reduced s.mem (s.gpr .x0) ∧ Reduced s.mem (s.gpr .x1)) fun s s' =>
    let hint := Vector.zipWith (makeHint (arg32 s .x2)) (polyAt s.mem (s.gpr .x0)) (polyAt s.mem (s.gpr .x1))
    HintIs s'.mem (s.gpr .x3) 1 [hint] ∧ ((s'.gpr .x0).setWidth 32).toNat = hintOnes [hint]

/-- `vg_mldsa_use_hint(h = x0, r = x1, gamma2 = w2, out = x3)`. -/
def useHintK : Contract isa :=
  hintK (fun s => Reduced s.mem (s.gpr .x1)) fun s s' =>
    NatPolyIs s'.mem (s.gpr .x3) (Vector.zipWith (fun hj rj => (useHint (arg32 s .x2) hj rj).toNat)
      ((hintAt s.mem (s.gpr .x0) 1).headD (Vector.replicate n false)) (polyAt s.mem (s.gpr .x1)))

/-! ## Zero-extending `γ₂` -/

/-- The state after `zext gr`'s first instruction, which zero-extends `gr`. -/
def zextS (gr : Reg) (s : State) : State := s.write .w gr (s.read .w gr + BitVec.ofNat 32 0)

theorem zextS_exec (gr : Reg) (s : State) : Exec isa (.block [.addImm .w gr gr 0]) s [] (zextS gr s) :=
  .block rfl

theorem zextS_gpr (gr : Reg) (s : State) (r : Reg) :
    (zextS gr s).gpr r = if r = gr then ((s.gpr gr).setWidth 32).setWidth 64 else s.gpr r := by
  simp [zextS, State.write, State.read]

theorem zextS_other {gr : Reg} (s : State) {r : Reg} (h : r ≠ gr) : (zextS gr s).gpr r = s.gpr r := by
  rw [zextS_gpr, ite_eq_right h]

theorem zextS_self (gr : Reg) (s : State) : (zextS gr s).gpr gr = ((s.gpr gr).setWidth 32).setWidth 64 := by
  rw [zextS_gpr, ite_eq_left rfl]

theorem zextS_toNat (gr : Reg) (s : State) : ((zextS gr s).gpr gr).toNat = arg32 s gr := by
  rw [zextS_self, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ((s.gpr gr).setWidth 32).isLt; omega)]

/-- Running `zext gr main`: `main` from the state with `gr` zero-extended. -/
theorem zext_ok {gr : Reg} {main : Prog isa} {s : State} {Q : State → Prop} (h : WP isa main (zextS gr s) Q) :
    WP isa (zext gr main) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨[] ++ t, s', .seq (zextS_exec gr s) he, hq⟩

/-- The registers of the initial state that `zext gr` keeps. -/
theorem zextS_keep (gr : Reg) (s : State) : Keep [gr] s (zextS gr s) :=
  ⟨fun r hr => zextS_other s (by simpa using hr), rfl, rfl, rfl⟩

theorem zextS_mem (gr : Reg) (s : State) : (zextS gr s).mem = s.mem := rfl

/-- Constant time of `zext gr main` from the taint of `main`, from states
that agree on what is public once `gr` is zero-extended. -/
theorem zext_ct {gr : Reg} {main : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    {τ : VG.AArch64.Taint.T}
    (hτ : ∀ s₁ s₂, Pub s₁ s₂ → VG.AArch64.Taint.Agree τ (zextS gr s₁) (zextS gr s₂))
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ main hc).isSome = true) :
    ConstantTime isa Pre Pub (zext gr main) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  obtain ⟨τ', hc'⟩ := Option.isSome_iff_exists.mp h
  unfold zext at e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, rfl⟩ := Exec.det a₁ (zextS_exec gr s₁)
      obtain ⟨rfl, rfl⟩ := Exec.det a₂ (zextS_exec gr s₂)
      rw [(VG.Taint.check_sound (A := taint) hc' (hτ _ _ hp) b₁ b₂).1]

/-- The registers `rs` are public, and `gr` once zero-extended. -/
theorem agree_zext {gr : Reg} {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (hg : (s₁.gpr gr).setWidth 32 = (s₂.gpr gr).setWidth 32) (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs (gr :: rs)) (zextS gr s₁) (zextS gr s₂) := by
  refine ⟨hsp, fun r hr => ?_⟩
  rw [zextS_gpr, zextS_gpr]
  split
  · rw [hg]
  · simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons] at hr
    exact h r (hr.resolve_left ‹_›)

/-! ## The branch on `γ₂` -/

theorem g32_setWidth : (BitVec.ofNat 32 g32).setWidth 64 = BitVec.ofNat 64 261888 := by decide

/-- `onGamma gr t arm` runs `arm γ₂`, if `γ₂` is in `gr`. -/
theorem onGamma_ok {gr t : Reg} (ht : t ≠ gr) {arm : Nat → Prog isa} {s : State} {Q : State → Prop}
    (hg : (s.gpr gr).toNat = g32 ∨ (s.gpr gr).toNat = g88)
    (h : ∀ g, (s.gpr gr).toNat = g → ∀ s', Keep [t] s s' → s'.mem = s.mem → WP isa (arm g) s' Q) :
    WP isa (onGamma gr t arm) s Q := by
  unfold onGamma
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok t _ s) fun s₁ ⟨⟨h1, hm₁⟩, k₁⟩ => ?_
  have hgr : s₁.gpr gr = s.gpr gr := k₁.get gr (by simpa using ht.symm)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [t] (Q := fun s' => s'.gpr t = s₁.gpr gr - s₁.gpr t ∧ s'.mem = s₁.mem)
    (by arun) (by simp [writesOnly, Code.allInstrs, dstOf])) fun s₂ ⟨⟨h2, hm₂⟩, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hk : Keep [t] s s₂ := k.mono (by simp)
  have hm : s₂.mem = s.mem := by rw [hm₂, hm₁]
  have e : s₂.gpr t = s.gpr gr - BitVec.ofNat 64 261888 := by rw [h2, hgr, h1, g32_setWidth]
  have hz : isa.eval (.zero .x t) s₂ = some (decide ((s.gpr gr).toNat = g32)) := by
    rw [VG.Proof.MlKem.AArch64.eval_zero, e, VG.Proof.MlKem.AArch64.eq_zero_iff]
    refine congrArg some (decide_eq_decide.mpr ?_)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr gr).isLt
    simp only [g32]
    omega
  refine WP.ite _ hz (fun hb => h _ (of_decide_eq_true hb) s₂ hk hm) fun hb => h _ ?_ s₂ hk hm
  have := of_decide_eq_false hb
  omega

/-! ## The loop over the coefficients -/

theorem coeffAddr_next (p : Addr) (j : Nat) : coeffAddr p j + BitVec.ofNat 64 4 = coeffAddr p (j + 1) := by
  rw [coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- Stores of `v` at `a` for each `(a, v)`, in order. -/
def writes (m : Mem) (ps : List (Addr × BitVec 32)) : Mem := ps.foldl (fun m p => m.writeW p.1 p.2) m

theorem writes_cons (m : Mem) (p : Addr × BitVec 32) (ps : List (Addr × BitVec 32)) :
    writes m (p :: ps) = writes (m.writeW p.1 p.2) ps := rfl

theorem writes_nil (m : Mem) : writes m [] = m := rfl

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

/-- Where the loop's polynomials are: inputs readable, outputs writable,
the outputs pairwise disjoint and disjoint from the inputs. -/
structure Layout (s₀ : State) (ins outs : List Reg) : Prop where
  rd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd ++ s₀.wr
  wr : ∀ o ∈ outs, pR (s₀.gpr o) ∈ s₀.wr
  dis : ∀ p ∈ ins, ∀ o ∈ outs, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr o))
  pw : outs.Pairwise fun a b => (pR (s₀.gpr a)).Disjoint (pR (s₀.gpr b))

/-- The layout, in a state with the same pointers and permissions. -/
theorem Layout.congr {s₀ s : State} {ins outs : List Reg} (h : Layout s₀ ins outs)
    (e : ∀ r ∈ ins ++ outs, s.gpr r = s₀.gpr r) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Layout s ins outs where
  rd p hp := by rw [e p (List.mem_append_left _ hp), hrd, hwr]; exact h.rd p hp
  wr o ho := by rw [e o (List.mem_append_right _ ho), hwr]; exact h.wr o ho
  dis p hp o ho := by
    rw [e p (List.mem_append_left _ hp), e o (List.mem_append_right _ ho)]; exact h.dis p hp o ho
  pw := h.pw.imp_of_mem fun ha hb hd => by
    rw [e _ (List.mem_append_right _ ha), e _ (List.mem_append_right _ hb)]; exact hd

/-- After `i` iterations: the pointers `ptrs` at coefficient `i`, the
registers `fixed` unchanged, the outputs hold their values below
coefficient `i`, and `J i`. -/
structure Inv (s₀ : State) (ptrs fixed outs : List Reg) (V : Reg → Nat → BitVec 32) (J : Nat → State → Prop)
    (i : Nat) (s : State) : Prop where
  ptr : ∀ p ∈ ptrs, s.gpr p = coeffAddr (s₀.gpr p) i
  fixed : ∀ r ∈ fixed, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (outs.map fun o => pR (s₀.gpr o)) s₀.mem s.mem
  done : ∀ o ∈ outs, ∀ k < i, coeffAt s.mem (s₀.gpr o) k = V o k
  j : J i s

section
variable {s₀ : State} {ins outs ptrs fixed : List Reg} {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop}
  {i : Nat} {s : State}

theorem Inv.inR (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs V J i s) {p : Reg} (hp : p ∈ ins)
    (hpp : p ∈ ptrs) (hi : i < 256) : InRegions (s.rd ++ s.wr) (s.gpr p) 4 := by
  rw [hI.rd, hI.wr, hI.ptr p hpp]
  exact ⟨_, hL.rd p hp, coeff_contains _ hi⟩

theorem Inv.inW (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs V J i s) {o : Reg} (ho : o ∈ outs)
    (hpo : o ∈ ptrs) (hi : i < 256) : InRegions s.wr (s.gpr o) 4 := by
  rw [hI.wr, hI.ptr o hpo]
  exact ⟨_, hL.wr o ho, coeff_contains _ hi⟩

/-- The inputs are those of the initial memory. -/
theorem Inv.read (hL : Layout s₀ ins outs) (hI : Inv s₀ ptrs fixed outs V J i s) {p : Reg} (hp : p ∈ ins)
    (hpp : p ∈ ptrs) (hi : i < 256) : s.mem.readW (s.gpr p) 32 = coeffAt s₀.mem (s₀.gpr p) i := by
  rw [hI.ptr p hpp, ← coeffAt_eq]
  exact coeffAt_frame hI.frame (fun _ hr => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hL.dis p hp o ho) hi

end

/-- The loop, from a body that writes `V o i` to coefficient `i` of each output. -/
theorem loop_ok {s₀ : State} {ins outs ptrs fixed clob : List Reg} {cnt : Reg} {body : List Instr}
    {V : Reg → Nat → BitVec 32} {J : Nat → State → Prop} (hL : Layout s₀ ins outs)
    (hout : ∀ o ∈ outs, o ∈ ptrs) (hfix : ∀ r ∈ fixed, r ∉ clob) (hpc : ∀ p ∈ ptrs, p ≠ cnt)
    (hfc : cnt ∉ fixed)
    (hJ : ∀ s, s.mem = s₀.mem → Keep [cnt] s₀ s → J 0 s)
    (hbody : ∀ i < 256, ∀ s, Inv s₀ ptrs fixed outs V J i s →
      WP isa (.block (body ++ ptrs.map (fun p => .addImm .x p p 4) ++ [.subImm .x cnt cnt 1])) s fun s' =>
        (s'.mem = writes s.mem (outs.map fun o => (s.gpr o, V o i)) ∧
          (∀ p ∈ ptrs, s'.gpr p = s.gpr p + BitVec.ofNat 64 4) ∧
          s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1 ∧ J (i + 1) s') ∧
        Keep clob s s') :
    WP isa (mapLoop ptrs cnt body) s₀ (Inv s₀ ptrs fixed outs V J 256) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [cnt] (Q := fun s => s.mem = s₀.mem ∧ s.gpr cnt = BitVec.ofNat 64 256)
    (by arun) (by simp [writesOnly, Code.allInstrs, dstOf]))
    fun s₁ ⟨⟨hm, hc⟩, hk⟩ => ?_)
  have h0 : Inv s₀ ptrs fixed outs V J 0 s₁ := by
    refine ⟨fun p hp => ?_, fun r hr => hk.get r (by simp only [List.mem_singleton]; rintro rfl; exact hfc hr), hk.rd, hk.wr, ?_,
      fun _ _ k h => absurd h (Nat.not_lt_zero _), hJ s₁ hm hk⟩
    · rw [hk.get p (by simpa using hpc p hp), coeffAddr, Nat.mul_zero, BitVec.add_zero]
    · rw [hm]; exact Frame.refl _ _
  refine wp_countdown (cnt := cnt) (N := 256) (by decide) (by decide) (Inv s₀ ptrs fixed outs V J)
    (fun i hi s hI _ => ?_) h0 hc
  refine WP.mono (hbody i hi s hI) fun s' ⟨⟨hm', hp', hc', hJ'⟩, hk'⟩ => ⟨?_, hc'⟩
  have hw : s'.mem = writes s.mem (outs.map fun o => (coeffAddr (s₀.gpr o) i, V o i)) := by
    rw [hm']
    exact congrArg (writes s.mem) (List.map_congr_left fun o ho => by rw [hI.ptr o (hout o ho)])
  refine ⟨fun p hp => by rw [hp' p hp, hI.ptr p hp, coeffAddr_next],
    fun r hr => (hk'.get r (hfix r hr)).trans (hI.fixed r hr), hk'.rd.trans hI.rd, hk'.wr.trans hI.wr,
    ?_, fun o ho k hk => ?_, hJ'⟩
  · rw [hw]
    exact frame_writes _ hI.frame outs _ hi _ fun o ho => List.mem_map_of_mem ho
  · rw [hw, coeffAt_writes _ _ outs _ hi _ hL.pw ho (by omega)]
    split
    · subst k; rfl
    · exact hI.done o ho k (by omega)

end VG.Proof.MlDsa.AArch64.Round
