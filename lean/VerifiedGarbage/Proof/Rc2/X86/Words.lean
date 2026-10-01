import VerifiedGarbage.Proof.Rc2.X86.RoundSteps

/-! # RC2 words in scratch memory and temporary registers -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

def wordBase (s : State) : Addr := addr32 (s.gpr .ebp) + 64

def MemWords (m : Mem) (p : Addr) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = (v.getD i 0).setWidth 32

def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 32

def temps : List Reg := [.esi, .edi]
def wordRegs : List Reg := [.eax, .ebx, .ecx, .edx]
def roundWrites : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi]

theorem wordReg_mem (i : Nat) : wordReg i ∈ wordRegs := by
  have fact : ∀ i < 4, wordReg i ∈ wordRegs := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ temps := by
  exact fun h => by
    have hs := wordReg_separate i
    simp only [temps, List.mem_cons, List.not_mem_nil, or_false] at h
    exact h.elim hs.1 hs.2.1

theorem wordOff_eq (s : State) (i : Nat) (hi : i < 4) :
    addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i) = wordBase s + BitVec.ofNat 64 (4 * i) := by
  simp only [wordOff, Nat.mod_eq_of_lt hi, wordBase, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by simp [Vector.getD, hi]

theorem MemWords.update {m : Mem} {p : Addr} {v : Spec.Rc2.State}
    (h : MemWords m p v) (i : Nat) (hi : i < 4) (x : BitVec 16) :
    MemWords (m.writeW (p + BitVec.ofNat 64 (4 * i)) (x.setWidth 32)) p (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j
    rw [Mem.readW_writeW_self32]
    simp [Vector.getD, hi]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide), h j hj]
    rw [vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.at_mod {s : State} {v : Spec.Rc2.State} (h : Words s v) (i : Nat) :
    s.gpr (wordReg i) = (v.getD (i % 4) 0).setWidth 32 := by
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (keep : Keep temps s s') : Words s' v := by
  intro i hi
  exact (keep.reg _ (wordReg_not_temps i)).trans (h i hi)

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 32)
    (keep : Keep (wordReg i :: temps) s s') : Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst j; simpa [Vector.getD, hi] using out
  · rw [keep.reg _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((wordReg_injective j hj i hi).mp e), wordReg_not_temps j⟩), h j hj]
    rw [vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

def wordIndex : Reg → Nat
  | .eax => 0 | .ebx => 1 | .ecx => 2 | .edx => 3 | _ => 0

theorem wordIndex_reg : ∀ i < 4, wordIndex (wordReg i) = i := by decide

theorem loadWords_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (fit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32)
    (readable : ∀ i < 4, InRegions (s.rd ++ s.wr) (wordBase s + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block loadWords) s (fun s' => Words s' v ∧ Keep wordRegs s s') := by
  let regs := fun i => wordReg (i - 16)
  let values := fun r => (v.getD (wordIndex r) 0).setWidth 32
  have code : loadWords = restoreCode .ebp regs [16, 17, 18, 19] := rfl
  have bounds : ∀ i ∈ [16, 17, 18, 19], 16 ≤ i ∧ i < 20 := by decide
  have addr (i : Nat) (hi : i ∈ [16, 17, 18, 19]) :
      addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i) = wordBase s + BitVec.ofNat 64 (4 * (i - 16)) := by
    have h := bounds i hi
    unfold wordBase
    rw [BitVec.add_assoc, show (64 : Addr) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => addr32 (s.gpr .ebp) + BitVec.ofNat 64 n) (by omega)
  rw [code]
  apply WP.mono (restoreCode_ok s .ebp regs [16, 17, 18, 19] values fit (by decide) (by decide)
    (fun i hi => by rw [addr i hi]; exact readable _ (by have := bounds i hi; omega))
    (fun i hi => by
      have h := bounds i hi
      rw [addr i hi, hv _ (by omega)]
      dsimp only [values, regs]
      rw [wordIndex_reg _ (by omega)]))
  intro s' h
  constructor
  · intro i hi
    have mem : wordReg i ∈ [16, 17, 18, 19].map regs := wordReg_mem i
    have out := h.1 (wordReg i) mem
    dsimp only [values] at out
    rw [wordIndex_reg i hi] at out
    exact out
  · exact h.2

end VG.Proof.Rc2.X86
