import VerifiedGarbage.TCB.Artifact

/-!
# Contracts with and without a scratch buffer argument

A function whose last argument was a scratch buffer, working space its
contract says nothing of, can instead take the buffer from its own stack
frame (`Impl/StackScratch/`). Its contract without the argument,
`sig.contract A pre post …`, then follows from the one with it
(`Sig.scratchContract`): the same `pre` and `post`, which ignore the buffer
(`Curry.withScratch`), on the signature with one more, last, parameter
(`Sig.withScratch`). Each target's `StackScratch.lean` proves the step.
-/

namespace VG

/-- `sig` with one more parameter, last: a writable array of `n` elements `e`. -/
def Sig.withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) : Sig :=
  { sig with params := sig.params ++ [(nm, .array true e n)] }

/-- `f`, its arguments after the first `a` taken through `g`. -/
def Curry.app {α : Type} {b b' : List ArgWord} (g : Curry b α → Curry b' α) :
    (a : List ArgWord) → Curry (a ++ b) α → Curry (a ++ b') α
  | [], f => g f
  | _ :: a, f => fun x => Curry.app g a (f x)

/-- `f` applied to the values `vs` of its first arguments `a`. -/
def Curry.part {α : Type} {b : List ArgWord} :
    (a : List ArgWord) → Curry (a ++ b) α → List (BitVec 64) → Curry b α
  | [], f, _ => f
  | w :: a, f, v :: vs => Curry.part a (f (w.ofRaw v)) vs
  | w :: a, f, [] => Curry.part a (f (w.ofRaw 0)) []

theorem Curry.apply_append {α : Type} {b : List ArgWord} :
    ∀ (a : List ArgWord) (f : Curry (a ++ b) α) (us vs : List (BitVec 64)), us.length = a.length →
      Curry.apply (a ++ b) f (us ++ vs) = Curry.apply b (Curry.part a f us) vs
  | [], _, [], _, _ => rfl
  | _ :: a, f, u :: us, vs, h => Curry.apply_append a _ us vs (by simpa using h)

theorem Curry.part_app {α : Type} {b b' : List ArgWord} (g : Curry b α → Curry b' α) :
    ∀ (a : List ArgWord) (f : Curry (a ++ b) α) (us : List (BitVec 64)), us.length = a.length →
      Curry.part a (Curry.app g a f) us = g (Curry.part a f us)
  | [], _, [], _ => rfl
  | _ :: a, f, u :: us, h => Curry.part_app g a _ us (by simpa using h)

/-- `f`, taking one more argument, a pointer, last, which it ignores. -/
def Curry.withScratch {α : Type} (pb : Nat) (nm : String) (e : Elem) (n : Nat) :
    (ps : List (String × Param)) → Curry (ps.flatMap fun p => p.2.words pb) α →
      Curry ((ps ++ [((nm, .array true e n) : String × Param)]).flatMap fun p => p.2.words pb) α
  | [], f => fun _ => f
  | p :: ps, f => Curry.app (Curry.withScratch pb nm e n ps) (p.2.words pb) f

theorem Curry.apply_withScratch {α : Type} (pb : Nat) (nm : String) (e : Elem) (n : Nat) :
    ∀ (ps : List (String × Param)) (f : Curry (ps.flatMap fun p => p.2.words pb) α)
      (vs : List (BitVec 64)) (x : BitVec 64), vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Curry.apply _ (Curry.withScratch pb nm e n ps f) (vs ++ [x]) = Curry.apply _ f vs
  | [], _, [], _, _ => rfl
  | p :: ps, f, vs, x, h => by
    rw [List.flatMap_cons, List.length_append] at h
    have hl : (vs.take (p.2.words pb).length).length = (p.2.words pb).length := by
      rw [List.length_take]; omega
    have hr : (vs.drop (p.2.words pb).length).length = (ps.flatMap fun p => p.2.words pb).length := by
      rw [List.length_drop]; omega
    rw [← List.take_append_drop (p.2.words pb).length vs, List.append_assoc]
    show Curry.apply (p.2.words pb ++ _) (Curry.app _ (p.2.words pb) f) _ =
      Curry.apply (p.2.words pb ++ _) f _
    rw [Curry.apply_append _ _ _ _ hl, Curry.apply_append _ _ _ _ hl, Curry.part_app _ _ _ _ hl]
    exact Curry.apply_withScratch pb nm e n ps _ _ x hr

/-- The contract of a function whose last argument is a scratch buffer of
`n` elements `e`, working space that `pre` and `post` ignore: the contract
that `sig.contract A pre post writeArgs stack` follows from, for a function
that allocates the buffer itself. -/
def Sig.scratchContract {M : ISA} (A : Abi M) (sig : Sig) (nm : String) (e : Elem) (n : Nat)
    (pre : Curry (sig.words A.ptrBits) (Mem → Prop)) (post : sig.Post A.ptrBits)
    (writeArgs : Bool) (stack : Nat) : Contract M :=
  (sig.withScratch nm e n).contract A (Curry.withScratch A.ptrBits nm e n sig.params pre)
    (Curry.withScratch A.ptrBits nm e n sig.params post) writeArgs stack

theorem Sig.words_withScratch (sig : Sig) (nm : String) (e : Elem) (n : Nat) (pb : Nat) :
    (sig.withScratch nm e n).words pb = sig.words pb ++ ([.addr] : List ArgWord) := by
  simp [Sig.withScratch, Sig.words, Param.words]

theorem Param.pubs_length (p : Param) (pb : Nat) : p.pubs.length = (p.words pb).length := by
  cases p <;> rfl

theorem Sig.pubs_length (ps : List (String × Param)) (pb : Nat) :
    (ps.flatMap (·.2.pubs)).length = (ps.flatMap fun p => p.2.words pb).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.flatMap_cons, ih, Param.pubs_length p.2 pb]

/-- The buffers of the parameters followed by one more array, given values
for the others and its address `x`. -/
theorem Sig.bufs_append_array (pb : Nat) (nm : String) (e : Elem) (n : Nat) (x : BitVec 64) :
    ∀ (ps : List (String × Param)) (vs : List (BitVec 64)),
      vs.length = (ps.flatMap fun p => p.2.words pb).length →
      Sig.bufs (ps ++ [((nm, .array true e n) : String × Param)]) (vs ++ [x]) =
        Sig.bufs ps vs ++ [(⟨x, n * e.size⟩, true)]
  | [], [], _ => rfl
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    exact Sig.bufs_append_array pb nm e n x ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_array pb nm e n x ps vs (by omega)]
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h
    simp only [List.cons_append, Sig.bufs]
    rw [Sig.bufs_append_array pb nm e n x ps vs (by omega)]
  | [], _ :: _, h => by simp at h
  | (_, .int ..) :: _, [], h => by simp [Param.words.eq_1] at h
  | (_, .array ..) :: _, [], h => by simp [Param.words.eq_2] at h
  | (_, .slice ..) :: _, [], h => by simp [Param.words.eq_3] at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h

end VG
