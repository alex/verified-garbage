import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# Inlining verified code (AArch64)

Untrusted: everything here is checked by Lean. As for x86-64: running code
from a state that permits more memory gives the same result (`Exec.widen`),
code never writes outside the regions its state permits (`Exec.regions`),
and `WP.inline` combines the two with the correctness part of the inlined
function's `Verified` proof.
-/

namespace VG.AArch64

/-- Every access that `rs` permits, `rs'` permits. -/
def Covers (rs rs' : List Region) : Prop := ∀ a n, InRegions rs a n → InRegions rs' a n

/-- `s`, permitted to read `rd` and write `wr` instead. -/
def State.withRegions (s : State) (rd wr : List Region) : State := { s with rd := rd, wr := wr }

@[simp] theorem State.withRegions_gpr (s : State) (rd wr) : (s.withRegions rd wr).gpr = s.gpr := rfl
@[simp] theorem State.withRegions_sp (s : State) (rd wr) : (s.withRegions rd wr).sp = s.sp := rfl
@[simp] theorem State.withRegions_mem (s : State) (rd wr) : (s.withRegions rd wr).mem = s.mem := rfl
@[simp] theorem State.withRegions_rd (s : State) (rd wr) : (s.withRegions rd wr).rd = rd := rfl
@[simp] theorem State.withRegions_wr (s : State) (rd wr) : (s.withRegions rd wr).wr = wr := rfl
@[simp] theorem State.withRegions_self (s : State) : s.withRegions s.rd s.wr = s := rfl
@[simp] theorem State.withRegions_withRegions (s : State) (rd wr rd' wr') :
    (s.withRegions rd wr).withRegions rd' wr' = s.withRegions rd' wr' := rfl

/-- Sub-regions: each region of `rs` lies at some offset within a region of `rs'`. -/
theorem Covers.of_sub {rs rs' : List Region}
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs rs' := by
  intro a n ⟨r, hr, hc⟩
  obtain ⟨r', hr', off, hb, hl⟩ := h r hr
  refine ⟨r', hr', ?_⟩
  unfold Region.Contains at *
  rw [hb] at hc
  have : (a - r'.base).toNat ≤ (a - (r'.base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - r'.base = (a - (r'.base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

/-- The register an instruction writes, if any. -/
def dstOf : Instr → Option Reg
  | .add _ d .. | .sub _ d .. | .addImm _ d .. | .subImm _ d .. | .logic _ _ d .. | .ror _ d ..
  | .lsr _ d .. | .rev32 d _ | .rev d _ | .movz _ d .. | .movk _ d .. | .ldr _ d .. | .ldrb d .. => some d
  | .str .. | .strb .. => none

section
variable {s s' : State} {rd wr : List Region}

theorem load_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : s.load a n = some v) : (s.withRegions rd wr).load a n = some v := by
  simp only [State.load] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store_widen (hc : Covers s.wr wr) {a : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : s.store a n v = some s') : (s.withRegions rd wr).store a n v = some (s'.withRegions rd wr) := by
  simp only [State.store] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem write_withRegions (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    (s.withRegions rd wr).write sz d v = (s.write sz d v).withRegions rd wr := rfl

theorem exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) {i : Instr}
    (h : exec i s = some s') : exec i (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases i with
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := h
    exact ⟨a, ha, v, load_widen hc hv, rfl⟩
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨a, ha, v, hv, rfl⟩ := h
    exact ⟨a, ha, v, load_widen hc hv, rfl⟩
  | str sz t n off =>
    simp only [exec, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨a, ha, hs⟩ := h
    exact ⟨a, ha, store_widen hw hs⟩
  | strb t n off =>
    simp only [exec, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨a, ha, hs⟩ := h
    exact ⟨a, ha, store_widen hw hs⟩
  | _ =>
    simp only [exec] at h ⊢
    first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (split at h <;> [skip; cases h]
       rename_i hh; simp only [hh, ite_true, Option.some.injEq] at h ⊢; subst h; rfl)

theorem addrs_withRegions (i : Instr) (s : State) (rd wr : List Region) :
    addrs i (s.withRegions rd wr) = addrs i s := by
  cases i <;> rfl

theorem exec_regions {i : Instr} (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  cases i with
  | str sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, rfl, (Frame.refl _ _).write hr _ hc⟩
  | strb t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, rfl, (Frame.refl _ _).write hr _ hc⟩
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩)

theorem exec_gpr {i : Instr} {r : Reg} (hi : dstOf i ≠ some r) (h : exec i s = some s') :
    s'.gpr r = s.gpr r := by
  have hw : ∀ (t : State) sz (d : Reg) (v : BitVec sz.bits), d ≠ r → (t.write sz d v).gpr r = t.gpr r :=
    fun t sz d v hd => by simp [State.write, Ne.symm hd]
  cases i with
  | str sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; rfl
  | strb t n off =>
    simp only [exec, Option.bind_eq_some_iff, State.store] at h
    obtain ⟨a, -, h⟩ := h
    split at h <;> cases h; rfl
  | ldr sz t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact hw _ _ _ _ fun e => hi (by simp [dstOf, e])
  | ldrb t n off =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, v, -, rfl⟩ := h
    exact hw _ _ _ _ fun e => hi (by simp [dstOf, e])
  | _ =>
    simp only [exec] at h
    first
    | (simp only [Option.some.injEq] at h; subst h
       exact hw _ _ _ _ fun e => hi (by simp [dstOf, e]))
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h
       exact hw _ _ _ _ fun e => hi (by simp [dstOf, e]))

theorem eval_withRegions (c : Cond) (s : State) (rd wr : List Region) :
    eval c (s.withRegions rd wr) = eval c s := by
  cases c <;> rfl

end

theorem execBlock_regions {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw, hsp, hf⟩ := exec_regions he
    obtain ⟨hr', hw', hsp', hf'⟩ := ih h2
    exact ⟨hr'.trans hr, hw'.trans hw, hsp'.trans hsp, hf.trans (hw ▸ hf')⟩

theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame s.wr s.mem s'.mem := by
  induction h with
  | block h => exact execBlock_regions h
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, p₁, f₁⟩ := ih₁; obtain ⟨r₂, w₂, p₂, f₂⟩ := ih₂
    exact ⟨r₂.trans r₁, w₂.trans w₁, p₂.trans p₁, f₁.trans (w₁ ▸ f₂)⟩
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, p₁, f₁⟩ := ih₁; obtain ⟨r₂, w₂, p₂, f₂⟩ := ih₂
    exact ⟨r₂.trans r₁, w₂.trans w₁, p₂.trans p₁, f₁.trans (w₁ ▸ f₂)⟩

theorem execBlock_widen {is : List Instr} {s s' : State} {t : List Leak} {rd wr : List Region}
    (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr)
    (h : execBlock isa is s = some (s', t)) :
    execBlock isa is (s.withRegions rd wr) = some (s'.withRegions rd wr, t) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw', -⟩ := exec_regions he
    have := ih (s := s₁) (by rwa [hr, hw']) (by rwa [hw']) h2
    simp only [execBlock]
    rw [exec_widen hc hw he]
    simp only [this, Option.map_some, addrs_withRegions]

/-- Running from a state that permits more memory. -/
theorem Exec.widen {c : Prog isa} {s s' : State} {t : List Leak} {rd wr : List Region}
    (h : Exec isa c s t s') (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    Exec isa c (s.withRegions rd wr) t (s'.withRegions rd wr) := by
  induction h with
  | block h => exact .block (execBlock_widen hc hw h)
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, -⟩ := Exec.regions h₁
    exact .seq (ih₁ hc hw) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | iteT hc' _ ih => exact .iteT ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | iteF hc' _ ih => exact .iteF ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | loopExit h₁ hc' ih => exact .loopExit (ih hc hw) ((eval_withRegions _ _ _ _).trans ‹_›)
  | loopNext h₁ hc' _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, -⟩ := Exec.regions h₁
    exact .loopNext (ih₁ hc hw) ((eval_withRegions _ _ _ _).trans ‹_›) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))

/-- The instructions of structured code. -/
def instrs {I C : Type} : Code I C → List I
  | .block is => is
  | .seq a b => instrs a ++ instrs b
  | .ite _ t e => instrs t ++ instrs e
  | .loop b _ => instrs b

theorem execBlock_gpr {is : List Instr} {r : Reg} (hc : ∀ i ∈ is, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.gpr r = s.gpr r := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2,
      exec_gpr (hc i (List.mem_cons_self ..)) he]

/-- A register that no instruction writes keeps its value. -/
theorem Exec.gpr {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, dstOf i ≠ some r)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.gpr r = s.gpr r := by
  induction h with
  | block h => exact execBlock_gpr hc h
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ fun i hi => hc i (List.mem_append_right _ hi), ih₁ fun i hi => hc i (List.mem_append_left _ hi)]
  | iteT _ _ ih => exact ih fun i hi => hc i (List.mem_append_left _ hi)
  | iteF _ _ ih => exact ih fun i hi => hc i (List.mem_append_right _ hi)
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]

/-- A register that no instruction writes keeps its value, as a
postcondition. -/
theorem WP.gpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {r : Reg}
    (hc : ∀ i ∈ instrs c, dstOf i ≠ some r) : WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

/-- Inlining verified code: from a state `s` in which the code's precondition
holds once its permissions are narrowed to `rd` and `wr`, the code
terminates in a state satisfying its postcondition and calling-convention
obligations (both on the narrowed states), which has the permissions of `s`,
differs from it in memory only within `wr`, and keeps every register that no
instruction writes. -/
theorem WP.inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, dstOf i ≠ some r) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s') : WP isa c s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, -, hf⟩ := Exec.regions he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl habi hf (fun r hr => Exec.gpr hr he') ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hpost

end VG.AArch64
