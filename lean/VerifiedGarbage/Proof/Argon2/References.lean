import VerifiedGarbage.Proof.Argon2.Iterations
import VerifiedGarbage.Proof.Argon2.FillStep

/-! The reviewed flattened reference log determines every lane/column pair. -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def Columns (q : Nat) (s : FillState) : Prop := ∀ ref ∈ s.indices, ref.2 < q

theorem fold_columns {α : Type} (q : Nat) (f : FillState → α → FillState)
    (step : ∀ s a, Columns q s → Columns q (f s a)) (xs : List α) (s : FillState) (h : Columns q s) :
    Columns q (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih (f s x) (step s x h)

theorem fillBlock_columns (p : Params) (positive : 0 < p.laneLen)
    (pass slice lane index : Nat) (s : FillState) (h : Columns p.laneLen s) :
    Columns p.laneLen (fillBlock p pass slice lane index s) := by
  by_cases skipped : pass = 0 ∧ slice = 0 ∧ index < 2
  · rw [fillBlock, ite_eq_left skipped]; exact h
  · unfold Columns
    rw [FillStep.indices p pass lane slice index s (by omega)]
    split
    · exact h
    · intro ref hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · change _ % p.laneLen < p.laneLen
        exact Nat.mod_lt _ positive
      · exact h ref hr

theorem fillPass_columns (p : Params) (positive : 0 < p.laneLen) (s : FillState) (pass : Nat)
    (h : Columns p.laneLen s) : Columns p.laneLen (fillPass p s pass) := by
  unfold fillPass
  apply fold_columns
  · intro s slice hs
    apply fold_columns
    · intro s lane hs
      exact fold_columns _ _ (fun s index hs => fillBlock_columns p positive pass slice lane index s hs) _ s hs
    · exact hs
  · exact h

theorem fill_columns (p : Params) (positive : 0 < p.laneLen) (password salt secret ad : List Byte) :
    Columns p.laneLen (fill p password salt secret ad) := by
  unfold fill
  apply fold_columns _ _ (fun s pass hs => fillPass_columns p positive s pass hs)
  intro ref hr
  exact False.elim (List.not_mem_nil hr)

def flattenRef (q : Nat) (ref : Nat × Nat) : Nat := ref.1 * q + ref.2

def decodeRef (q n : Nat) : Nat × Nat := (n / q, n % q)

theorem decode_flatten (q : Nat) (positive : 0 < q) (ref : Nat × Nat) (bound : ref.2 < q) :
    decodeRef q (flattenRef q ref) = ref := by
  unfold decodeRef flattenRef
  rw [Nat.mul_comm ref.1 q, Nat.mul_add_div positive,
    Nat.div_eq_of_lt bound, Nat.add_zero, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt bound]

theorem decode_list (q : Nat) (positive : 0 < q) (xs : List (Nat × Nat))
    (bound : ∀ ref ∈ xs, ref.2 < q) : (xs.map (flattenRef q)).map (decodeRef q) = xs := by
  induction xs with
  | nil => rfl
  | cons ref xs ih =>
    simp only [List.map_cons]
    rw [decode_flatten q positive ref (bound ref (List.mem_cons_self ..)),
      ih (fun r hr => bound r (List.mem_cons_of_mem ref hr))]

theorem references_injective (p : Params) (positive : 0 < p.laneLen)
    (password₁ salt₁ secret₁ ad₁ password₂ salt₂ secret₂ ad₂ : List Byte)
    (same : references p password₁ salt₁ secret₁ ad₁ = references p password₂ salt₂ secret₂ ad₂) :
    (fill p password₁ salt₁ secret₁ ad₁).indices = (fill p password₂ salt₂ secret₂ ad₂).indices := by
  apply List.reverse_inj.mp
  have left := fill_columns p positive password₁ salt₁ secret₁ ad₁
  have right := fill_columns p positive password₂ salt₂ secret₂ ad₂
  have decoded := congrArg (List.map (decodeRef p.laneLen)) same
  change ((fill p password₁ salt₁ secret₁ ad₁).indices.reverse.map (flattenRef p.laneLen)).map _ =
    ((fill p password₂ salt₂ secret₂ ad₂).indices.reverse.map (flattenRef p.laneLen)).map _ at decoded
  rw [decode_list p.laneLen positive _ (fun ref hr => left ref (List.mem_reverse.mp hr)),
    decode_list p.laneLen positive _ (fun ref hr => right ref (List.mem_reverse.mp hr))] at decoded
  exact decoded

end VG.Proof.Argon2
