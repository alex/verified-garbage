import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA key generation: coefficients and polynomials in memory

`mod± q` inverts the cast of a small integer to `ℤ_q` (`modPm_ofInt`), and the
cast inverts `mod± q` (`ofInt_modPm`); the ranges of the coefficients
`RejBoundedPoly` samples (`rejBoundedPoly_range`) and of `Power2Round`
(`power2Round_fst`, `power2Round_snd`); and ML-DSA's polynomials in memory
(`Spec/MlDsa/Poly.lean`) depend only on their 1024 bytes (`polyAt_congr`,
`polyIs_frame`, …).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `mod± q` and the cast to `ℤ_q` -/

theorem ofInt_val (x : Int) : ((ofInt x).val : Int) = x % 8380417 := by
  have h1 := Int.emod_nonneg x (show (8380417 : Int) ≠ 0 by decide)
  have h2 := Int.emod_lt_of_pos x (show (0 : Int) < 8380417 by decide)
  have hq : ((q : Nat) : Int) = 8380417 := rfl
  simp only [ofInt, Fin.val_ofNat]
  rw [Int.natCast_emod, hq, Int.toNat_of_nonneg (by rw [← hq]; exact h1)]
  omega

theorem modPm_q (m : Int) : modPm m q = if m % 8380417 > 4190208 then m % 8380417 - 8380417 else m % 8380417 := rfl

/-- `mod± q` of a small integer cast to `ℤ_q` is the integer. -/
theorem modPm_ofInt {x : Int} (h₁ : -4190208 ≤ x) (h₂ : x ≤ 4190208) : modPm (ofInt x).val q = x := by
  rw [modPm_q, ofInt_val]
  split <;> omega

/-- The cast of `mod± q` of an element of `ℤ_q` is the element. -/
theorem ofInt_modPm (c : Zq) : ofInt (modPm c.val q) = c := by
  apply Fin.ext
  have hc : c.val < 8380417 := c.isLt
  have key : modPm c.val q % 8380417 = c.val := by rw [modPm_q]; split <;> omega
  have h := ofInt_val (modPm c.val q)
  rw [key] at h
  exact_mod_cast h

theorem toRq_modPm (f : Poly) : toRq (f.map fun c => modPm c.val q) = f := by
  unfold toRq
  rw [Vector.map_map]
  exact (Vector.map_congr_left fun c _ => ofInt_modPm c).trans (Vector.map_id f)

theorem modPm_toRq {f : IPoly} (h : ∀ c ∈ f.toList, -4190208 ≤ c ∧ c ≤ 4190208) :
    (toRq f).map (fun c => modPm c.val q) = f := by
  unfold toRq
  rw [Vector.map_map]
  refine (Vector.map_congr_left fun c hc => ?_).trans (Vector.map_id f)
  exact modPm_ofInt (h c (Vector.mem_toList_iff.mpr hc)).1 (h c (Vector.mem_toList_iff.mpr hc)).2

/-! ## Ranges -/

theorem coeffFromHalfByte_range {η b : Nat} {v : Int} (h : coeffFromHalfByte η b = some v) :
    -(η : Int) ≤ v ∧ v ≤ η := by
  unfold coeffFromHalfByte at h
  split at h
  · rename_i hc; cases h; obtain ⟨rfl, _⟩ := hc; omega
  · split at h
    · rename_i hc; cases h; obtain ⟨rfl, _⟩ := hc; omega
    · cases h

theorem rejBoundedLoop_range {η : Nat} : ∀ {a : List Int} {l : List Byte} {r : List Int},
    (∀ c ∈ a, -(η : Int) ≤ c ∧ c ≤ η) → rejBoundedLoop η a l = some r → ∀ c ∈ r, -(η : Int) ≤ c ∧ c ≤ η
  | a, [], r, ha, h => by
    rw [rejBoundedLoop] at h
    split at h
    · cases h; exact ha
    · cases h
  | a, z :: out, r, ha, h => by
    rw [rejBoundedLoop] at h
    split at h
    · cases h; exact ha
    · refine rejBoundedLoop_range (fun c hc => ?_) h
      have r1 := @coeffFromHalfByte_range η (z.toNat % 16)
      have r2 := @coeffFromHalfByte_range η (z.toNat / 16)
      revert hc r1 r2
      generalize coeffFromHalfByte η (z.toNat % 16) = o1
      generalize coeffFromHalfByte η (z.toNat / 16) = o2
      intro hc r1 r2
      cases o1 <;> cases o2 <;> simp only at hc
      · exact ha c hc
      · split at hc
        · rcases List.mem_append.mp hc with hc | hc
          · exact ha c hc
          · rw [List.mem_singleton.mp hc]; exact r2 rfl
        · exact ha c hc
      · rcases List.mem_append.mp hc with hc | hc
        · exact ha c hc
        · rw [List.mem_singleton.mp hc]; exact r1 rfl
      · split at hc
        · rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · exact ha c hc
            · rw [List.mem_singleton.mp hc]; exact r1 rfl
          · rw [List.mem_singleton.mp hc]; exact r2 rfl
        · rcases List.mem_append.mp hc with hc | hc
          · exact ha c hc
          · rw [List.mem_singleton.mp hc]; exact r1 rfl

theorem rejBoundedPoly_range {η b : Nat} {ρ : List Byte} {x : IPoly} (h : rejBoundedPoly η b ρ = some x) :
    ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η := by
  unfold rejBoundedPoly at h
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have hr := rejBoundedLoop_range (fun _ h => absurd h List.not_mem_nil) ha
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
  cases e : a[i]? with
  | none => simp
  | some v => exact hr v (List.mem_of_getElem? e)

theorem power2Round_fst (c : Zq) : 0 ≤ (power2Round c).1 ∧ (power2Round c).1 ≤ 1023 := by
  have hc : c.val < 8380417 := c.isLt
  have h2 : ((2 ^ 13 : Nat) : Int) = 8192 := rfl
  simp only [power2Round, modPm, d, h2]
  split <;> omega

theorem power2Round_snd (c : Zq) : -4095 ≤ (power2Round c).2 ∧ (power2Round c).2 ≤ 4096 := by
  have h2 : ((2 ^ 13 : Nat) : Int) = 8192 := rfl
  simp only [power2Round, modPm, d, h2]
  split <;> omega

/-! ## Polynomials -/

theorem add_zero_left (f : Poly) : add zero f = f :=
  Vector.ext fun i hi => by simp [add, zero]

/-! ## Polynomials in memory -/

theorem coeffAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p i = coeffAt m p i := by
  refine Mem.readW_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by change i < 256 at hi; omega)

theorem polyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    polyAt m' p = polyAt m p :=
  Vector.ext fun i hi => by simp only [polyAt, Vector.getElem_ofFn, coeffAt_congr h hi]

theorem natPolyAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    natPolyAt m' p = natPolyAt m p :=
  Vector.ext fun i hi => by simp only [natPolyAt, Vector.getElem_ofFn, coeffAt_congr h hi]

theorem reduced_congr {m m' : Mem} {p : Addr}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [coeffAt_congr h hi]; exact hr i hi

theorem polyIs_congr {m m' : Mem} {p : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p f := ⟨reduced_congr h hf.1, (polyAt_congr h).trans hf.2⟩

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} (h : bytesAt m' p 1024 = bytesAt m p 1024) :
    ∀ k < 1024, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) := fun k hk => by
  have : (bytesAt m' p 1024)[k]! = (bytesAt m p 1024)[k]! := by rw [h]
  rwa [Proof.MlKem.bytesAt_getElem! _ _ hk, Proof.MlKem.bytesAt_getElem! _ _ hk] at this

end VG.Proof.MlDsa.KeyGen
