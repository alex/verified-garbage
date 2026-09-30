import VerifiedGarbage.Proof.Rc2.X86.Mix

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

def mixResult (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : BitVec 16 :=
  let x := v.getD i 0
  let a := v.getD ((i + 3) % 4) 0
  let b := v.getD ((i + 2) % 4) 0
  let c := v.getD ((i + 1) % 4) 0
  match d with
  | .encrypt => (x + k.getD j 0 + (a &&& b) + (~~~a &&& c)).rotateLeft (Spec.Rc2.rotation i)
  | .decrypt => x.rotateRight (Spec.Rc2.rotation i) - k.getD j 0 - (a &&& b) - (~~~a &&& c)

theorem mixCore_encrypt_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore .encrypt j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixResult .encrypt (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mixCore, WP.block_append_iff]
  apply WP.mono (mixArithmetic_ok false s i j hj stackRead fit readable)
  intro s₁ h₁
  have out := h₁.1
  rw [hv i hi, hv.at_mod (i + 3), hv.at_mod (i + 2), hv.at_mod (i + 1), mixValue_add] at out
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := rotate16_ok s₁ (wordReg i) (wordReg_separate i).1 _ out
    (Spec.Rc2.rotation i) (rotation_bounds i).1 (rotation_bounds i).2
  refine WP.of_runBlock ⟨s₂, run₂, out₂, h₁.2.trans (keep₂.weaken ?_)⟩
  simp [temps]

theorem neighbor_ne : ∀ i < 4, ∀ n < 4, 1 ≤ n → wordReg (i + n) ≠ wordReg i := by decide

theorem mixCore_decrypt_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore .decrypt j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixResult .decrypt (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mixCore, WP.block_append_iff]
  have bounds := rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := rotate16_ok s (wordReg i) (wordReg_separate i).1 _ (hv i hi)
    (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [Word32.rotateLeft_reverse _ _ bounds.1 bounds.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have sp : .esp ∉ [wordReg i, .esi] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (wordReg_separate i).2.2.2, by decide⟩
  have args := arg_keep keep₁ sp 0
  have stack := argAddr_keep keep₁ sp 0
  apply WP.mono (mixArithmetic_ok true s₁ i j hj
    (by rw [keep₁.rd, keep₁.wr, stack]; exact stackRead)
    (by rw [args]; exact fit)
    (by rw [keep₁.rd, keep₁.wr, args]; exact readable))
  intro s₂ h₂
  constructor
  · have nbr (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 3) :
        s₁.gpr (wordReg (i + n)) = (v.getD ((i + n) % 4) 0).setWidth 32 := by
      rw [keep₁.reg _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨neighbor_ne i hi n (by omega) hn, (wordReg_separate _).1⟩)]
      exact hv.at_mod _
    rw [h₂.1, out₁, nbr 3 (by decide) (by decide), nbr 2 (by decide) (by decide),
      nbr 1 (by decide) (by decide), keep₁.mem, args, mixValue_sub]
    rfl
  · exact (keep₁.weaken (by simp [temps])).trans h₂.2

theorem mixCore_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixCore d j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixResult d (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) j i v).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  cases d
  · exact mixCore_encrypt_ok s v hv i j hi hj stackRead fit readable
  · exact mixCore_decrypt_ok s v hv i j hi hj stackRead fit readable

end VG.Proof.Rc2.X86
