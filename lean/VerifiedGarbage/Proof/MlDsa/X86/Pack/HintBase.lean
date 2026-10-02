import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on x86 (32-bit): what the proofs of the hint encodings share

* Loops whose number of iterations depends on the leaked data
  (`loopC`, which ends when a condition that correctness determines from
  public data fails, and `loopN`, with a public number of iterations), for
  the `Piece` framework of ML-KEM on x86 (`Proof/MlKem/X86/Piece.lean`).
* The layout both functions' contracts give (`Lay`): arguments `(r, rlen,
  omega, w, wlen)` on the stack, `r` read-only, `w` and the arguments
  writable, and where a leaf's body finds its arguments.
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86
open VG.Proof.MlKem.X86
open VG.Impl.MlKem.X86 (saveRegs)
open VG.Spec.MlDsa

/-! ## Running blocks

A block is run with `hrun`, a `simp only` that steps it one instruction at
a time (`runBlock_cons`, `runStep_some`) with `State.setReg` and the flags
kept folded (`RegUpd`); `Keep rs s s'` says that `s'` differs from `s` only
in the registers `rs` (and the flags and memory), and `WP.keep` proves it of
code none of whose instructions writes another register. -/

theorem arithFlags_eq (s : State) (x : BitVec 32) (c o : Bool) :
    arithFlags s x c o = s.setFlags (some c) (some o) (some (x == 0)) (some x.msb) := rfl
theorem sub_zero' (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x
theorem setFlags_cf (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).cf = a := rfl
theorem setFlags_zf (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).zf = c := rfl

/-- Steps a block from a state whose accesses the hypotheses `ls` permit. -/
syntax "hrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| hrun) => `(tactic| hrun [])
  | `(tactic| hrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, arithFlags_eq, Proof.MlKem.X86.ea_at, State.load32, State.load8, State.store32,
        State.store8, Reg8.reg, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.cf_setReg, RegUpd.zf_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags,
        RegUpd.wr_setFlags, setFlags_cf, setFlags_zf,
        Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
        ite_false, reduceCtorEq, BitVec.sub_self, sub_zero', true_and, and_true, $ls,*]))

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

theorem Keep.drop {r : Reg} {rs : List Reg} {s s' : State} (k : Keep (r :: rs) s s') (h : s'.gpr r = s.gpr r) :
    Keep rs s s' :=
  ⟨fun r' hr' => by
    by_cases e : r' = r
    · subst e; exact h
    · exact k.gpr (by simp only [List.mem_cons, not_or]; exact ⟨e, hr'⟩), k.2⟩

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

/-- The byte a `store8` stores. -/
theorem b8_eq (x : BitVec 32) : BitVec.setWidth 8 x = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte, zero-extended. -/
theorem toNat_setWidth32_8 (x : BitVec 8) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem add_one' (x : BitVec 32) (t : Nat) : x + BitVec.ofNat 32 t + 1 = x + BitVec.ofNat 32 (t + 1) := by
  rw [BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

theorem add_four' (x : BitVec 32) (t : Nat) : x + BitVec.ofNat 32 t + 4 = x + BitVec.ofNat 32 (t + 4) := by
  rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ofNat_add_ofNat]

theorem add_1024' (x : BitVec 32) (t : Nat) : x + BitVec.ofNat 32 t + 1024 = x + BitVec.ofNat 32 (t + 1024) := by
  rw [BitVec.add_assoc, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, ofNat_add_ofNat]

theorem ofNat_add_one (t : Nat) : BitVec.ofNat 32 t + 1 = BitVec.ofNat 32 (t + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

theorem add_sub_one' (x : BitVec 32) {a : Nat} (h : 1 ≤ a) : x + BitVec.ofNat 32 a - 1 = x + BitVec.ofNat 32 (a - 1) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - 1) + 1 by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat, Nat.sub_add_cancel h],
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- A byte, zero-extended, as a number. -/
theorem byte32 (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth32_8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The loop condition after counting down. -/
theorem eval_ne_cnt {s : State} {N k : Nat} (hk : k < N) (hN : N < 2 ^ 32)
    (h : s.zf = some (BitVec.ofNat 32 (N - k) - 1 == 0)) : isa.eval .ne s = some (decide (k + 1 < N)) := by
  show s.zf.map (!·) = _
  rw [h]; exact cnt_ne hk hN

/-! ## Loops -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece whose postcondition also says something of `s₀` that its
precondition implies. -/
theorem addX {A B : State → State → Prop} {c : Prog isa} {X : State → Prop} (h : Piece Pre Pub A B c)
    (hx : ∀ s₀ s, Pre s₀ → A s₀ s → X s₀) : Piece Pre Pub A (fun s₀ s => B s₀ s ∧ X s₀) c where
  wp s₀ s h₀ ha := (h.wp s₀ s h₀ ha).mono fun _ hb => ⟨hb, hx _ _ h₀ ha⟩
  ct := h.ct

/-- A loop that goes on after iteration `k` while `cont k s₀`, which
correctness determines from public data, and has fewer than `M s₀`
iterations. -/
theorem loopC {body : Prog isa} {cnd : Cond} (Inv : Nat → State → State → Prop) (B : State → State → Prop)
    (M : State → Nat) (cont : Nat → State → Bool)
    (hM : ∀ k s₀, Pre s₀ → cont k s₀ = true → k + 1 < M s₀)
    (hc : ∀ k s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → cont k s₀ = cont k s₀')
    (hb : ∀ k, Piece Pre Pub (Inv k) (fun s₀ s => isa.eval cnd s = some (cont k s₀) ∧
      (cont k s₀ = true → Inv (k + 1) s₀ s) ∧ (cont k s₀ = false → B s₀ s)) body) :
    Piece Pre Pub (Inv 0) B (.loop body cnd) where
  wp s₀ s h₀ ha := by
    refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = M s₀ - k ∧ Inv k s₀ s)
      (fun n s ⟨k, hn, hi⟩ => ?_) (M s₀) s ⟨0, (Nat.sub_zero _).symm, ha⟩
    refine ((hb k).wp _ _ h₀ hi).mono fun s' ⟨he, ht, hf⟩ => ?_
    cases h : cont k s₀
    · exact .inl ⟨by rw [he, h], hf h⟩
    · have := hM k s₀ h₀ h
      exact .inr ⟨by rw [he, h], M s₀ - (k + 1), by omega, k + 1, rfl, ht h⟩
  ct s₀ s₀' h₀ h₀' hp := by
    have := RelCT.loop (M := isa) (body := body) (c := cnd) (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = M s₀ - k ∧ Inv k s₀ s ∧ Inv k s₀' s')
      (fun n => by
        refine RelCT.exists_ fun k => ?_
        by_cases hk : n = M s₀ - k
        · refine ((hb k).ct' h₀ h₀' hp).mono (fun s s' ⟨_, a, a'⟩ => ⟨a, a'⟩) ?_
          rintro s s' ⟨⟨e₁, t₁, -⟩, e₂, t₂, -⟩
          refine ⟨by rw [e₁, e₂, hc k _ _ h₀ h₀' hp], fun _ => trivial, fun h => ?_⟩
          rw [e₁, Option.some.injEq] at h
          have := hM k s₀ h₀ h
          exact ⟨M s₀ - (k + 1), by omega, k + 1, rfl, t₁ h, t₂ (by rw [← hc k _ _ h₀ h₀' hp]; exact h)⟩
        · exact RelCT.of_false fun s s' ⟨h1, _⟩ => hk h1) (M s₀)
    exact this.mono (fun s s' ⟨a, a'⟩ => ⟨0, (Nat.sub_zero _).symm, a, a'⟩) fun _ _ h => h

/-- A loop of `N s₀ ≥ 1` iterations, where `N` is public. -/
theorem loopN {body : Prog isa} {cnd : Cond} (Inv : Nat → State → State → Prop) (N : State → Nat)
    (hN : ∀ s₀, Pre s₀ → 0 < N s₀) (hNp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → N s₀ = N s₀')
    (hb : ∀ k, Piece Pre Pub (fun s₀ s => Inv k s₀ s ∧ k < N s₀)
      (fun s₀ s => Inv (k + 1) s₀ s ∧ isa.eval cnd s = some (decide (k + 1 < N s₀))) body) :
    Piece Pre Pub (Inv 0) (fun s₀ s => Inv (N s₀) s₀ s) (.loop body cnd) :=
  (loopC (fun k s₀ s => Inv k s₀ s ∧ k < N s₀) _ N (fun k s₀ => decide (k + 1 < N s₀))
    (fun _ _ _ h => of_decide_eq_true h) (fun k s₀ s₀' h₀ h₀' hp => by rw [hNp _ _ h₀ h₀' hp])
    fun k => (addX (X := fun s₀ => k < N s₀) (hb k) fun _ _ _ h => h.2).mono (fun _ _ _ h => h)
      fun s₀ s _ ⟨⟨hi, he⟩, hk⟩ => ⟨he, fun h => ⟨hi, of_decide_eq_true h⟩, fun h => by
        rw [show N s₀ = k + 1 by have := of_decide_eq_false h; omega]; exact hi⟩).mono
    (fun s₀ _ h₀ h => ⟨h, hN s₀ h₀⟩) fun _ _ _ h => h

/-- `loopN` over a block, which the taint analysis proves from `R`. -/
theorem countLoopN {body : List Instr} {cnd : Cond} (Inv : Nat → State → State → Prop) (N : State → Nat)
    (hN : ∀ s₀, Pre s₀ → 0 < N s₀) (hNp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → N s₀ = N s₀')
    (R : List Reg)
    (hstep : ∀ k s₀ s, Pre s₀ → Inv k s₀ s → k < N s₀ → WP isa (.block body) s fun s' =>
      Inv (k + 1) s₀ s' ∧ isa.eval cnd s' = some (decide (k + 1 < N s₀)))
    (hR : ∀ k s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → Inv k s₀ s → Inv k s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr R) (.block body) hc).isSome = true) :
    Piece Pre Pub (Inv 0) (fun s₀ s => Inv (N s₀) s₀ s) (.loop (.block body) cnd) :=
  loopN Inv N hN hNp fun k => Piece.taint R (fun s₀ s h₀ ⟨hi, hk⟩ => hstep k s₀ s h₀ hi hk)
    (fun s₀ s₀' s s' h₀ h₀' hp ⟨a, _⟩ ⟨a', _⟩ => hR k s₀ s₀' s s' h₀ h₀' hp a a') ht

/-- An empty block. -/
theorem nil_piece {A B : State → State → Prop} (h : ∀ s₀ s, Pre s₀ → A s₀ s → B s₀ s) :
    Piece Pre Pub A B (.block []) :=
  Piece.taint [] (fun s₀ s hp ha => WP.block_nil_iff.mpr (h s₀ s hp ha))
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

end

/-! ## The layout -/

section
variable (s₀ : State)
/-- The buffer read, `w` the one written. -/
abbrev rA : Addr := (arg s₀ 0).setWidth 64
abbrev wA : Addr := (arg s₀ 3).setWidth 64
/-- `ω`. -/
abbrev ω : Nat := (arg s₀ 2).toNat
/-- The arguments. -/
abbrev gR : Region := ⟨argAddr s₀ 0, 20⟩
/-- The leaf's frame, as the contract gives it. -/
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

/-- The facts of both contracts' layouts, for a buffer of `a` bytes read and
one of `b` written. -/
structure Lay (s₀ : State) (a b : Nat) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 20 ≤ 2 ^ 32
  rd : s₀.rd = [⟨rA s₀, a⟩]
  wr : s₀.wr = [⟨wA s₀, b⟩, gR s₀]
  r_w : (⟨rA s₀, a⟩ : Region).Disjoint ⟨wA s₀, b⟩
  r_g : (⟨rA s₀, a⟩ : Region).Disjoint (gR s₀)
  w_g : (⟨wA s₀, b⟩ : Region).Disjoint (gR s₀)
  ret_r : (retR s₀).Disjoint ⟨rA s₀, a⟩
  ret_w : (retR s₀).Disjoint ⟨wA s₀, b⟩
  ret_g : (retR s₀).Disjoint (gR s₀)
  stk_r : (stkR s₀).Disjoint ⟨rA s₀, a⟩
  stk_w : (stkR s₀).Disjoint ⟨wA s₀, b⟩
  stk_g : (stkR s₀).Disjoint (gR s₀)
  r_fit : (arg s₀ 0).toNat + a ≤ 2 ^ 32
  w_fit : (arg s₀ 3).toNat + b ≤ 2 ^ 32

namespace Lay
variable {s₀ : State} {a b : Nat} (hl : Lay s₀ a b)
include hl

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hl.sp]

/-- The push changes nothing but the frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hl.sp)
  rw [saveRegs_len] at hf
  exact hf

/-- The arguments, after the push. -/
theorem P0_argw {i : Nat} (hi : i < 5) : (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
  P0_arg hl.sp (n := 5) hi hl.sp' hl.stk_g

theorem argIn {s : State} (hrd : s.rd = (P0 s₀).rd) (hwr : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact P0_argIn hi hl.sp' (by simp [hl.wr])

theorem argOut {s : State} (hwr : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 5) : InRegions s.wr (argAddr s₀ i) 4 := by
  rw [hwr, P0_wr, hl.wr]
  exact ⟨gR s₀, by simp, arg_contains (n := 5) hi hl.sp'⟩

/-- The bytes read, as on entry. -/
theorem r_keep {s : State} {W : List Region} (hf : Frame W (P0 s₀).mem s.mem)
    (hW : ∀ r ∈ W, (⟨rA s₀, a⟩ : Region).Disjoint r) {t : Nat} (ht : t < a) :
    s.mem (rA s₀ + BitVec.ofNat 64 t) = s₀.mem (rA s₀ + BitVec.ofNat 64 t) := by
  have := hl.r_fit
  rw [hf.bytes (R := ⟨rA s₀, a⟩) hW (show a ≤ 2 ^ 64 by omega) ht,
    hl.P0_keep.bytes (R := ⟨rA s₀, a⟩) (by simpa [← hl.stk_eq] using hl.stk_r.symm) (show a ≤ 2 ^ 64 by omega) ht]

theorem wW : ∀ r ∈ [(⟨wA s₀, b⟩ : Region)], (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨by rw [← hl.stk_eq]; exact hl.stk_w, hl.ret_w⟩

end Lay

theorem argEa {s₀ s : State} (h : s.gpr .esp = (P0 s₀).gpr .esp) (i : Nat) :
    (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h]; exact P0_argAddr s₀ i

end VG.Proof.MlDsa.X86.Pack.Hint
