import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Proof.MlKem.X86.TopKem
import VerifiedGarbage.Proof.MlKem.X86.Extra
import VerifiedGarbage.Impl.MlKem.X86.Encrypt

/-!
# ML-KEM on x86 (32-bit): the setting of K-PKE.Encrypt

`encrypt L sc` is proven once, for any parameter set `L` and any layout whose
`scratch` has `L.scratch` bytes and whose stack is 88 bytes (`SOK`), which
encapsulation and decapsulation both have. The facts of the layout of its
buffers, all in `scratch`, that the proofs use are stated once for any such
layout (the classes `EncBaseOK`, …), and each parameter set has them by
computing them from its offsets (`ok_sc`, `sep_sc`: `sc_decide`). Its code
reaches the buffers through `esi`, so does not depend on the argument
`scratch` is (`ptrTo_sc`: `sc_taint`).

Its inputs (`Inp`) are `ek`, `m` and 64 bytes whose last 32 are `r`, at
`eEK`, `eM` and `eKR` (`Base`). A step's frame is within what a predicate
keeps (`Keeps`) if it is within a larger one (`Keeps.widen`).
`SamplePolyCBD₂(PRF₂(r, N))` is `cbd_piece`.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A layout whose `scratch` has `L.scratch` bytes, written, and whose stack is 88 bytes. -/
structure SOK (L : KemLay) (Y : Lay) : Prop where
  lt : Y.sc < Y.n
  wr : Y.awr Y.sc = true
  len : Y.alen Y.sc = L.scratch
  stk : Y.stk = 88

theorem SOK.le {L : KemLay} {Y : Lay} (h : SOK L Y) {n : Nat} (hn : n ≤ 88 := by decide) : n ≤ Y.stk :=
  h.stk ▸ hn

theorem ok_sc {L : KemLay} {Y : Lay} (h : SOK L Y) (o l : Nat) :
    Y.ok ⟨Y.sc, o, l⟩ = (decide (0 < l) && decide (o + l ≤ L.scratch)) := by
  simp only [Lay.ok, h.lt, h.len, decide_true, Bool.true_and]

theorem okW_sc {L : KemLay} {Y : Lay} (h : SOK L Y) (o l : Nat) :
    Y.okW ⟨Y.sc, o, l⟩ = (decide (0 < l) && decide (o + l ≤ L.scratch)) := by
  simp only [Lay.okW, ok_sc h, h.wr, Bool.and_true]

theorem sep_sc {Y : Lay} (o l o' l' : Nat) :
    Y.sep ⟨Y.sc, o, l⟩ ⟨Y.sc, o', l'⟩ = (decide (o + l ≤ o') || decide (o' + l' ≤ o)) := by
  simp only [Lay.sep, ite_true]

theorem ptrTo_sc (sc : Nat) (r : Reg) (o l : Nat) :
    ptrTo sc r ⟨sc, o, l⟩ = [.mov r (.reg .esi), .alu .add r (.imm (BitVec.ofNat 32 o))] := by
  simp only [ptrTo, ite_true]

/-! ## Inputs -/

/-- `ek`, `m`, and 64 bytes whose last 32 are `r`, as functions of the entry state. -/
structure Inp where
  ek : State → List Byte
  m : State → List Byte
  kr : State → List Byte

section
variable (L : KemLay) (I : Inp) (s₀ : State)
/-- `ρ`. -/
abbrev ρE : List Byte := ekRho L.p (I.ek s₀)
/-- `r`. -/
abbrev rE : List Byte := (I.kr s₀).drop 32
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aE (i j : Nat) : Poly := sv (matSeed (ρE L I s₀) i j)
/-- `ŷ[j]`. -/
abbrev yE (j : Nat) : Poly := encY (rE I s₀) j
end

section
variable (L : KemLay) (sc : Nat)
abbrev bY (j : Nat) : Buf := ⟨sc, 1024 * j, 1024⟩
abbrev bE : Buf := ⟨sc, L.eE, 1024⟩
abbrev bU : Buf := ⟨sc, L.eU, 1024⟩
abbrev bA : Buf := ⟨sc, L.eA, 1024⟩
abbrev bP : Buf := ⟨sc, L.eP, 1024⟩
abbrev bT : Buf := ⟨sc, L.eT, 1024⟩
abbrev bMU : Buf := ⟨sc, L.eMU, 1024⟩
abbrev bNS : Buf := ⟨sc, L.eNS, 1024⟩
abbrev bSS : Buf := ⟨sc, L.eSS, 2048⟩
abbrev bST : Buf := ⟨sc, L.eST, 200⟩
abbrev bWK : Buf := ⟨sc, L.eWK, 640⟩
abbrev bPRF : Buf := ⟨sc, L.ePRF, 128⟩
abbrev bACC : Buf := ⟨sc, L.eACC, 4⟩
abbrev bEK : Buf := ⟨sc, L.eEK, L.p.ekLen⟩
abbrev bM : Buf := ⟨sc, L.eM, 32⟩
abbrev bKR : Buf := ⟨sc, L.eKR, 64⟩
abbrev bC : Buf := ⟨sc, L.eC, L.p.ctLen⟩
/-- `r ‖ N`. -/
abbrev bRN : Buf := ⟨sc, L.eKR + 32, 33⟩
/-- `N`. -/
abbrev bN : Buf := ⟨sc, L.eKR + 64, 1⟩
/-- `ρ ‖ i ‖ j`. -/
abbrev bSeed : Buf := ⟨sc, L.eEK + 384 * L.p.k, 34⟩
end

/-- Whether `bs` is apart from the inputs. -/
def inApart (L : KemLay) (Y : Lay) (bs : List Buf) : Bool :=
  Y.apart (bEK L Y.sc) bs && Y.apart (bM L Y.sc) bs && Y.apart (bKR L Y.sc) bs

/-- A fact of the layout of buffers of `scratch`, computed from their offsets. -/
macro "sc_decide" : tactic => `(tactic| (simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true,
  ok_sc ‹SOK _ _›, okW_sc ‹SOK _ _›, sep_sc, (‹SOK _ _›).stk, inApart]; decide))

/-- The facts of the layout that `rn_split` and `cbd_piece` use. -/
class BaseOK (L : KemLay) : Prop where
  n : ∀ {Y : Lay}, SOK L Y → Y.okW (bN L Y.sc) = true
  rn : ∀ {Y : Lay}, SOK L Y →
    Y.ok ⟨Y.sc, L.eKR + 32, 32⟩ = true ∧ Y.ok (bN L Y.sc) = true ∧ Y.ok (bKR L Y.sc) = true
  hash : ∀ {Y : Lay}, SOK L Y → (Y.okW (bST L Y.sc) && Y.okW (bWK L Y.sc) && Y.ok (bRN L Y.sc) &&
    Y.okW (bPRF L Y.sc) && Y.sep (bST L Y.sc) (bWK L Y.sc) && Y.sep (bRN L Y.sc) (bST L Y.sc) &&
    Y.sep (bRN L Y.sc) (bWK L Y.sc) && Y.sep (bST L Y.sc) (bPRF L Y.sc) && Y.sep (bPRF L Y.sc) (bWK L Y.sc)) = true

/-- A taint check of code that reaches buffers of `scratch` through `esi`, for any parameter set. -/
macro "sc_taint" : tactic => `(tactic| ((try simp only [ptrTo_sc]); (try simp only [ptrTo, reduceIte,
  Nat.reduceEqDiff, List.cons_append, List.nil_append]); taint_rfl))

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

/-- The inputs, in `scratch`. -/
structure Base (L : KemLay) (Y : Lay) (I : Inp) (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  ek : bytesAt s.mem (Buf.addr s₀ (bEK L Y.sc)) L.p.ekLen = I.ek s₀
  m : bytesAt s.mem (Buf.addr s₀ (bM L Y.sc)) 32 = I.m s₀
  kr : bytesAt s.mem (Buf.addr s₀ (bKR L Y.sc)) 64 = I.kr s₀

theorem Base.keep {I : Inp} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : inApart L Y bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Base L Y I s₀ s) (c : Ctx Y s₀ s') :
    Base L Y I s₀ s' := by
  simp only [inApart, Bool.and_eq_true] at hs
  exact ⟨c, by rw [keepBytes hp hM hs.1.1 fr]; exact h.ek, by rw [keepBytes hp hM hs.1.2 fr]; exact h.m,
    by rw [keepBytes hp hM hs.2 fr]; exact h.kr⟩

/-- `Q` holds after anything whose frame is within `bs` and `M` bytes of stack. -/
def Keeps (Y : Lay) (Q : State → State → Prop) (bs : List Buf) (M : Nat) : Prop :=
  ∀ s₀ s s', TPre Y s₀ → Q s₀ s → Ctx Y s₀ s' → Frame (FR s₀ bs M) s.mem s'.mem → Q s₀ s'

theorem Keeps.widen {Q : State → State → Prop} {bs : List Buf} {M : Nat} (h : Keeps Y Q bs M) (hM : M + 16 ≤ Y.stk)
    {bs' : List Buf} {M' : Nat} (hb : ∀ b ∈ bs', b ∈ bs) (hM' : M' ≤ M) : Keeps Y Q bs' M' :=
  fun s₀ s s' hp hq c fr => h s₀ s s' hp hq c (fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (hb b hb')), fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp hM' hM⟩)

/-! ## `SamplePolyCBD₂(PRF₂(r, N))` -/

theorem st8_byte {s₀ : State} (m : Mem) (o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨Y.sc, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega
  simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero, ite_true]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

variable [BaseOK L]

/-- `r ‖ N`. -/
theorem rn_split {s₀ : State} (hS : SOK L Y) (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bRN L Y.sc)) 33 =
      (bytesAt m (Buf.addr s₀ (bKR L Y.sc)) 64).drop 32 ++ bytesAt m (Buf.addr s₀ (bN L Y.sc)) 1 := by
  obtain ⟨o₁, o₂, o₃⟩ := BaseOK.rn hS
  rw [bytes_split hp m (o' := L.eKR + 64) (l₁ := 32) (l₂ := 1) rfl rfl o₁ o₂,
    bytesAt_drop _ _ (show 32 ≤ 64 by decide)]
  have e : Buf.addr s₀ ⟨Y.sc, L.eKR + 32, 32⟩ = Buf.addr s₀ (bKR L Y.sc) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := ⟨Y.sc, L.eKR + 32, 32⟩) o₁, Buf.addr_eq hp (b := bKR L Y.sc) o₃,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
