import VerifiedGarbage.Proof.MlDsa.X86.Round.HintCore

/-!
# ML-DSA on x86 (32-bit): the loops of `vg_mldsa_make_hint` and `vg_mldsa_use_hint`

Untrusted: everything here is checked by Lean. Both store the end of their
output, `out + 1024`, in the argument slot of `γ₂`, compare `γ₂` with
`(q - 1)/32` (`hintInit`), and run, for the value they found, a loop of a
core (`Core2`, `HintCore.lean`) and `endTail`, which stores `eax` to the
output at `ebp` and compares the advanced `ebp` with the end (`hint_step`).
The loop is proven once for both (`hint_piece`); `makeHint` also counts the
values in `ecx` (`cnt`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame coeffAt_writeW coeffAt_writeW_disjoint
  n_eq q_eq)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_esp P0_wr frameR retR LeafPost LeafEnd Piece toNat_ofNat32
  eq_ofNat_of_toNat ptr_next sub_beq_zero)

/-- The precondition of both, with `reqA` if the first polynomial is reduced (`makeHint`'s `z`). -/
structure HPre (reqA : Bool) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [pR (pA s₀ 0), pR (pA s₀ 1)]
  wr : s₀.wr = [pR (pA s₀ 3), aR s₀ 4]
  a_o : (pR (pA s₀ 0)).Disjoint (pR (pA s₀ 3))
  a_a : (pR (pA s₀ 0)).Disjoint (aR s₀ 4)
  b_o : (pR (pA s₀ 1)).Disjoint (pR (pA s₀ 3))
  b_a : (pR (pA s₀ 1)).Disjoint (aR s₀ 4)
  o_a : (pR (pA s₀ 3)).Disjoint (aR s₀ 4)
  ret_a' : (retR s₀).Disjoint (pR (pA s₀ 0))
  ret_b : (retR s₀).Disjoint (pR (pA s₀ 1))
  ret_o : (retR s₀).Disjoint (pR (pA s₀ 3))
  ret_a : (retR s₀).Disjoint (aR s₀ 4)
  stk_a' : (stkR s₀).Disjoint (pR (pA s₀ 0))
  stk_b : (stkR s₀).Disjoint (pR (pA s₀ 1))
  stk_o : (stkR s₀).Disjoint (pR (pA s₀ 3))
  stk_a : (stkR s₀).Disjoint (aR s₀ 4)
  a_fit : (arg s₀ 0).toNat + 1024 ≤ 2 ^ 32
  b_fit : (arg s₀ 1).toNat + 1024 ≤ 2 ^ 32
  o_fit : (arg s₀ 3).toNat + 1024 ≤ 2 ^ 32
  g2 : (arg s₀ 2).toNat ∈ gamma2s
  a_red : reqA = true → Reduced s₀.mem (pA s₀ 0)
  b_red : Reduced s₀.mem (pA s₀ 1)

/-- The public data: the stack pointer, the pointers and `γ₂`. -/
def HPub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

/-! ## The prologue -/

/-- After `hintInit`. -/
structure HS1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [aR s₀ 4] (P0 s₀).mem s.mem
  slot : s.mem.readW (argAddr s₀ 2) 32 = arg s₀ 3 + 1024
  esi : s.gpr .esi = arg s₀ 0
  edi : s.gpr .edi = arg s₀ 1
  ebp : s.gpr .ebp = arg s₀ 3
  ecx : s.gpr .ecx = 0
  zf : s.zf = some (arg s₀ 2 == BitVec.ofNat 32 g32)

theorem hintInit_piece (reqA : Bool) : Piece (HPre reqA) HPub (fun s₀ s => s = P0 s₀) HS1 (.block hintInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have hin : aR s₀ 4 ∈ s₀.rd ++ s₀.wr := by simp [hp.wr]
    obtain ⟨a₀, i₀, v₀⟩ := arg_P0 (i := 0) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₁, i₁, v₁⟩ := arg_P0 (i := 1) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₂, i₂, v₂⟩ := arg_P0 (i := 2) (by omega) hp.sp hp.sp' hin hp.stk_a
    obtain ⟨a₃, i₃, v₃⟩ := arg_P0 (i := 3) (by omega) hp.sp hp.sp' hin hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂ a₃
    have w₂ : InRegions (P0 s₀).wr (argAddr s₀ 2) 4 :=
      ⟨aR s₀ 4, by rw [P0_wr, hp.wr]; simp, arg_contains (by omega) hp.sp'⟩
    have s02 : Mem.Sep (argAddr s₀ 2) 4 (argAddr s₀ 0) 4 := by
      have := hp.sp'; intro x h₁ h₂; simp only [argAddr, E0] at this h₁ h₂; bv_omega
    have s12 : Mem.Sep (argAddr s₀ 2) 4 (argAddr s₀ 1) 4 := by
      have := hp.sp'; intro x h₁ h₂; simp only [argAddr, E0] at this h₁ h₂; bv_omega
    have s32 : Mem.Sep (argAddr s₀ 2) 4 (argAddr s₀ 3) 4 := by
      have := hp.sp'; intro x h₁ h₂; simp only [argAddr, E0] at this h₁ h₂; bv_omega
    apply WP.of_runBlock
    simp (config := {decide := true}) only [hintInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₁, a₂, a₃, i₀, i₁, i₂, i₃, v₀, v₁, v₂, v₃, w₂, ite_true,
      ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (arg_contains (by omega)
      hp.sp'), Mem.readW_writeW_self32 _ _ _, by simp, by simp, by simp, by simp, by rw [sub_beq_zero']⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-! ## The loop -/

/-- The first polynomial's coefficient `i`. -/
abbrev cA (s₀ : State) (i : Nat) : Nat := (coeffAt s₀.mem (pA s₀ 0) i).toNat

/-- The second polynomial's coefficient `i`. -/
abbrev cB (s₀ : State) (i : Nat) : Nat := (coeffAt s₀.mem (pA s₀ 1) i).toNat

/-- The sum of the first `k` values. -/
def sumV (V : Nat → Nat → Nat) (s₀ : State) : Nat → Nat
  | 0 => 0
  | k + 1 => sumV V s₀ k + V (cA s₀ k) (cB s₀ k)

/-- After `k` coefficients. -/
structure HInv (V : Nat → Nat → Nat) (cnt : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = arg s₀ 0 + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 (4 * k)
  ebp : s.gpr .ebp = arg s₀ 3 + BitVec.ofNat 32 (4 * k)
  frame : Frame [pR (pA s₀ 3), aR s₀ 4] (P0 s₀).mem s.mem
  slot : s.mem.readW (argAddr s₀ 2) 32 = arg s₀ 3 + 1024
  out : ∀ i < k, coeffAt s.mem (pA s₀ 3) i = BitVec.ofNat 32 (V (cA s₀ i) (cB s₀ i))
  ecx : cnt = true → s.gpr .ecx = BitVec.ofNat 32 (sumV V s₀ k)

/-- The output pointer compared with the end of the output. -/
theorem end_cmp' (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)

theorem hint_step {core : List Instr} {V : Nat → Nat → Nat} {reqA cnt : Bool} (hc : Core2 core V reqA cnt)
    {s₀ : State} (hp : HPre reqA s₀) {k : Nat} (hk : k < 256) {s : State}
    (h : HInv V cnt s₀ k s) :
    WP isa (.block (core ++ endTail)) s fun s' =>
      HInv V cnt s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < VG.Spec.MlDsa.n := by rw [n_eq]; exact hk
  have ina : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 := by
    rw [State.ea, at_, h.esi, ea_cf hp.a_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have inb : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 := by
    rw [State.ea, at_, h.edi, ea_cf hp.b_fit hk, h.rd, h.wr, pushed_rd, P0_wr, hp.rd]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  have va : (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = cA s₀ k := by
    rw [State.ea, at_, h.esi, ea_cf hp.a_fit hk, ← VG.Proof.MlDsa.Round.coeffAt_eq,
      in_keep hp.sp h.frame hp.stk_a' (by simp [hp.a_o, hp.a_a]) hk]
  have vb : (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = cB s₀ k := by
    rw [State.ea, at_, h.edi, ea_cf hp.b_fit hk, ← VG.Proof.MlDsa.Round.coeffAt_eq,
      in_keep hp.sp h.frame hp.stk_b (by simp [hp.b_o, hp.b_a]) hk]
  refine hc _ s _ _ _ (fun e => (hp.a_red e) k hk') (hp.b_red k hk') ina va inb vb fun s₁ o₁ v₁ c₁ => ?_
  have ebp₁ : s₁.gpr .ebp = arg s₀ 3 + BitVec.ofNat 32 (4 * k) := by rw [o₁.gpr _ (by decide), h.ebp]
  have out : InRegions s₁.wr (addr (arg s₀ 3 + BitVec.ofNat 32 (4 * k)) 0) 4 := by
    rw [addr_cf hp.o_fit hk, o₁.wr, h.wr, P0_wr, hp.wr]
    exact ⟨_, by simp, coeff_contains _ hk'⟩
  refine wp_stm ebp₁ out fun s₂ m₂ => wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_addi fun s₅ u₅ =>
    wp_cmpm (B := s₅.gpr .esp) (o := 28) rfl ?_ fun s₆ f₆ z₆ =>
    WP.block_nil_iff.mpr ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun e => ?_⟩, ?_⟩
  · have hsp : s₅.gpr .esp = (P0 s₀).gpr .esp := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide),
        h.esp]
    rw [show addr (s₅.gpr .esp) 28 = argAddr s₀ 2 by rw [hsp]; exact VG.Proof.MlKem.X86.P0_argAddr s₀ 2,
      u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, m₂.rd, m₂.wr, o₁.rd, o₁.wr, h.rd, h.wr, pushed_rd, P0_wr, hp.wr]
    exact ⟨aR s₀ 4, by simp, arg_contains (by omega) hp.sp'⟩
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr,
      o₁.gpr _ (by decide), h.esp]
  · rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, o₁.rd, h.rd]
  · rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, o₁.wr, h.wr]
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, o₁.gpr _ (by decide), h.esi]
    exact ptr_next _ _ 4
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide), h.edi]
    exact ptr_next _ _ 4
  · rw [f₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, ebp₁]
    exact ptr_next _ _ 4
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem]
    exact h.frame.writeW (by simp) _ (coeff_contains _ hk')
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      Mem.readW_writeW_sep (Region.Disjoint.sep hp.o_a.symm (arg_contains (by omega) hp.sp')
        (coeff_contains _ hk')) (by decide), h.slot]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      coeffAt_writeW _ _ (by rw [n_eq]; omega) hk']
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl]; exact eq_ofNat_of_toNat v₁
    · rw [ite_eq_right e]; exact h.out i (by omega)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, c₁ e,
      h.ecx e, eq_ofNat_of_toNat v₁, ← BitVec.ofNat_add]
    rfl
  · simp only [eval, z₆, Option.map_some]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, addr_cf hp.o_fit hk, o₁.mem,
      show addr (s₅.gpr .esp) 28 = argAddr s₀ 2 by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, o₁.gpr _ (by decide),
          h.esp]; exact VG.Proof.MlKem.X86.P0_argAddr s₀ 2,
      Mem.readW_writeW_sep (Region.Disjoint.sep hp.o_a.symm (arg_contains (by omega) hp.sp')
        (coeff_contains _ hk')) (by decide), h.slot, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      m₂.gpr, ebp₁, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlKem.X86.add_ofNat_add,
      end_cmp' _ (by omega)]
    by_cases e : k + 1 < 256
    · rw [decide_eq_false (by omega), decide_eq_true e]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false e]; rfl

theorem hint_loop {core : List Instr} {V : Nat → Nat → Nat} {reqA cnt : Bool} (hc : Core2 core V reqA cnt)
    (E : State → Prop) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp]) (.block (core ++ endTail)) hh).isSome = true) :
    Piece (HPre reqA) HPub (fun s₀ s => HS1 s₀ s ∧ E s₀) (fun s₀ s => HInv V cnt s₀ 256 s ∧ E s₀)
      (.loop (.block (core ++ endTail)) .ne) := by
  refine (Piece.loop (fun k s₀ s => HInv V cnt s₀ k s ∧ E s₀) (by decide) fun k hk =>
    Piece.taint [.esp, .esi, .edi, .ebp]
      (fun s₀ s hp ⟨h, he⟩ => (hint_step hc hp hk h).mono fun _ ⟨h', c'⟩ => ⟨⟨h', he⟩, c'⟩)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, hq.2.1]
        · rw [h.edi, h'.edi, hq.2.2.1]
        · rw [h.ebp, h'.ebp, hq.2.2.2.2]) ht).mono (fun s₀ s _ ⟨h, he⟩ => ⟨?_, he⟩) fun _ _ _ h => h
  exact ⟨h.esp, h.rd, h.wr, by rw [h.esi]; simp, by rw [h.edi]; simp, by rw [h.ebp]; simp,
    h.frame.mono (by simp), h.slot, fun i hi => absurd hi (by omega), fun _ => by rw [h.ecx]; rfl⟩

/-- `γ₂` is `(q - 1)/32`: the branch the code takes. -/
def hG32 (s₀ : State) : Bool := arg s₀ 2 == BitVec.ofNat 32 g32

/-- Both branches, for the core `core g` computing `Vf g`. -/
theorem hint_ite {core : Nat → List Instr} {Vf : Nat → Nat → Nat → Nat} {reqA cnt : Bool}
    (hc : ∀ g ∈ gamma2s, Core2 (core g) (Vf g) reqA cnt)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp]) (.block (core g32 ++ endTail)) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp]) (.block (core g88 ++ endTail)) h₂).isSome = true) :
    Piece (HPre reqA) HPub HS1 (fun s₀ s => HInv (Vf (arg s₀ 2).toNat) cnt s₀ 256 s)
      (.ite .e (.loop (.block (core g32 ++ endTail)) .ne) (.loop (.block (core g88 ++ endTail)) .ne)) := by
  refine Piece.ite hG32 (fun s₀ s _ h => h.zf) (fun s₀ s₀' _ _ hq => by simp only [hG32, hq.2.2.2.1]) ?_ ?_
  · refine (hint_loop (hc g32 g32_mem) (fun s₀ => hG32 s₀ = true) t₁).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases gamma_cases hp.g2 with ⟨_, e⟩ | ⟨e', _⟩
    · rw [e]; exact h
    · rw [hG32, e'] at he; exact absurd he (by decide)
  · refine (hint_loop (hc g88 g88_mem) (fun s₀ => hG32 s₀ = false) t₂).mono (fun _ _ _ h => h)
      fun s₀ s hp ⟨h, he⟩ => ?_
    rcases gamma_cases hp.g2 with ⟨e', _⟩ | ⟨_, e⟩
    · rw [hG32, e'] at he; exact absurd he (by decide)
    · rw [e]; exact h

theorem hW {reqA : Bool} {s₀ : State} (hp : HPre reqA s₀) :
    ∀ r ∈ [pR (pA s₀ 3), aR s₀ 4], (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_o, hp.ret_o⟩
  · exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_a, hp.ret_a⟩

end VG.Proof.MlDsa.X86.Round
