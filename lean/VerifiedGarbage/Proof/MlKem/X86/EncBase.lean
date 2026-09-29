import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Proof.MlKem.X86.TopSeq2
import VerifiedGarbage.Proof.MlKem.X86.Extra
import VerifiedGarbage.Impl.MlKem.X86.Encrypt

/-!
# ML-KEM-768 on x86 (32-bit): the setting of K-PKE.Encrypt

Untrusted: everything here is checked by Lean. `encrypt sc` is proven once,
for any layout whose `scratch` has 32768 bytes and whose stack is 88 bytes
(`SOK`), which `vg_mlkem768_encaps` and `vg_mlkem768_decaps` both have. The
facts of the layout of its buffers, all in `scratch`, are then computed from
their offsets (`ok_sc`, `sep_sc`: `sc_decide`), and its code, which reaches
them through `esi`, does not depend on the argument `scratch` is
(`ptrTo_sc`: `sc_taint`).

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

/-- A layout whose `scratch` has 32768 bytes, written, and whose stack is 88 bytes. -/
structure SOK (Y : Lay) : Prop where
  lt : Y.sc < Y.n
  wr : Y.awr Y.sc = true
  len : Y.alen Y.sc = 32768
  stk : Y.stk = 88

theorem SOK.le {Y : Lay} (h : SOK Y) {n : Nat} (hn : n ≤ 88 := by decide) : n ≤ Y.stk := h.stk ▸ hn

theorem ok_sc {Y : Lay} (h : SOK Y) (o l : Nat) :
    Y.ok ⟨Y.sc, o, l⟩ = (decide (0 < l) && decide (o + l ≤ 32768)) := by
  simp only [Lay.ok, h.lt, h.len, decide_true, Bool.true_and]

theorem okW_sc {Y : Lay} (h : SOK Y) (o l : Nat) :
    Y.okW ⟨Y.sc, o, l⟩ = (decide (0 < l) && decide (o + l ≤ 32768)) := by
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
variable (I : Inp) (s₀ : State)
/-- `ρ`. -/
abbrev ρE : List Byte := ekRho mlKem768 (I.ek s₀)
/-- `r`. -/
abbrev rE : List Byte := (I.kr s₀).drop 32
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aE (i j : Nat) : Poly := sv (matSeed (ρE I s₀) i j)
/-- `ŷ[j]`. -/
abbrev yE (j : Nat) : Poly := encY (rE I s₀) j
end

section
variable (sc : Nat)
abbrev bY (j : Nat) : Buf := ⟨sc, 1024 * j, 1024⟩
abbrev bE : Buf := ⟨sc, eE, 1024⟩
abbrev bU : Buf := ⟨sc, eU, 1024⟩
abbrev bA : Buf := ⟨sc, eA, 1024⟩
abbrev bP : Buf := ⟨sc, eP, 1024⟩
abbrev bT : Buf := ⟨sc, eT, 1024⟩
abbrev bMU : Buf := ⟨sc, eMU, 1024⟩
abbrev bNS : Buf := ⟨sc, eNS, 1024⟩
abbrev bSS : Buf := ⟨sc, eSS, 2048⟩
abbrev bST : Buf := ⟨sc, eST, 200⟩
abbrev bWK : Buf := ⟨sc, eWK, 640⟩
abbrev bPRF : Buf := ⟨sc, ePRF, 128⟩
abbrev bACC : Buf := ⟨sc, eACC, 4⟩
abbrev bEK : Buf := ⟨sc, eEK, 1184⟩
abbrev bM : Buf := ⟨sc, eM, 32⟩
abbrev bKR : Buf := ⟨sc, eKR, 64⟩
abbrev bC : Buf := ⟨sc, eC, 1088⟩
/-- `r ‖ N`. -/
abbrev bRN : Buf := ⟨sc, eKR + 32, 33⟩
/-- `N`. -/
abbrev bN : Buf := ⟨sc, eKR + 64, 1⟩
/-- `ρ ‖ i ‖ j`. -/
abbrev bSeed : Buf := ⟨sc, eEK + 1152, 34⟩
end

/-- Whether `bs` is apart from the inputs. -/
def inApart (Y : Lay) (bs : List Buf) : Bool :=
  Y.apart (bEK Y.sc) bs && Y.apart (bM Y.sc) bs && Y.apart (bKR Y.sc) bs

/-- A fact of the layout of buffers of `scratch`, computed from their offsets. -/
macro "sc_decide" : tactic => `(tactic| (simp only [Lay.apart, List.all_cons, List.all_nil, Bool.and_true,
  ok_sc ‹SOK _›, okW_sc ‹SOK _›, sep_sc, (‹SOK _›).stk, inApart]; decide))

/-- A taint check of code that reaches buffers of `scratch` through `esi`. -/
macro "sc_taint" : tactic => `(tactic| ((try simp only [ptrTo_sc]); taint_decide))

variable {Y : Lay} {lk : State → List Byte}

/-- The inputs, in `scratch`. -/
structure Base (Y : Lay) (I : Inp) (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  ek : bytesAt s.mem (Buf.addr s₀ (bEK Y.sc)) 1184 = I.ek s₀
  m : bytesAt s.mem (Buf.addr s₀ (bM Y.sc)) 32 = I.m s₀
  kr : bytesAt s.mem (Buf.addr s₀ (bKR Y.sc)) 64 = I.kr s₀

theorem Base.keep {I : Inp} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : inApart Y bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Base Y I s₀ s) (c : Ctx Y s₀ s') :
    Base Y I s₀ s' := by
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

/-- `r ‖ N`. -/
theorem rn_split {s₀ : State} (hS : SOK Y) (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bRN Y.sc)) 33 =
      (bytesAt m (Buf.addr s₀ (bKR Y.sc)) 64).drop 32 ++ bytesAt m (Buf.addr s₀ (bN Y.sc)) 1 := by
  rw [bytes_split hp m (o' := eKR + 64) (l₁ := 32) (l₂ := 1) rfl rfl (by sc_decide) (by sc_decide),
    bytesAt_drop _ _ (show 32 ≤ 64 by decide)]
  have e : Buf.addr s₀ ⟨Y.sc, eKR + 32, 32⟩ = Buf.addr s₀ (bKR Y.sc) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := ⟨Y.sc, eKR + 32, 32⟩) (by sc_decide), Buf.addr_eq hp (b := bKR Y.sc) (by sc_decide),
      BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]

end VG.Proof.MlKem.X86.Enc
