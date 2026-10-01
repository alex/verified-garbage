import VerifiedGarbage.Proof.Ed25519.Arm.PointTable

/-! Untrusted: restore compact table entries into working point coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fromTableQuarter_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (j : Nat) (hj : j < 4) :
    WP isa (.block (unpackField (64 + 64 * j) (32 * j))) s fun t =>
      env t.mem b ⟨j, by omega⟩ = tableF s.mem b (o + 32 * j) ∧ AllLim t.mem b ∧
      TableKeep b (64 + 64 * j) 64 s t := by
  have ea := hc.ptr_addr (by omega : o < 8192)
  refine WP.mono (unpackField_ok hc (by omega) (by omega) hp
    (by rw [hc.ptr_nat (by omega)]; have := hc.fit; omega)
    (fun i hi => by
      rw [ea, Offset.add_add]
      exact in_base (List.mem_append_right _ hc.wr) (by omega) (by omega))
    (by rw [ea, Offset.add_add]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)))
    fun t ⟨hr, hf, hlt, hv⟩ => ?_
  rw [ea, Offset.add_add] at hv
  have hu := field_update ⟨j, by omega⟩ hl (frame_o hf) hlt
  exact ⟨congrArg VG.Proof.X25519.toFe hv, hu.1, ⟨hr, hf⟩⟩

theorem fromTablePrefix_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j => unpackField (64 + 64 * j) (32 * j))) s fun t =>
      (∀ j (hj : j < n), env t.mem b ⟨j, by omega⟩ = tableF s.mem b (o + 32 * j)) ∧
      AllLim t.mem b ∧ TableKeep b 64 (64 * n) s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, hl, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hc hl hp (by omega)) fun t ⟨hv, hlt, hk⟩ => ?_
    refine WP.mono (fromTableQuarter_ok (hk.ctx hc) hlt
      ((hk.rest.gpr _ (by decide)).trans hp) hlo ho n (by omega)) fun u ⟨hu, hlu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, hlu,
      (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem b ⟨j, by omega⟩ = env t.mem b ⟨j, by omega⟩ :=
        congrArg VG.Proof.X25519.toFe (val16_congr (ku.slot (by omega) ⟨j, by omega⟩
          (.inl (by simp only [offset]; omega))))
      rw [he, hv j h]
    · have e : j = n := by omega
      subst j
      rw [hu, hk.tableF (by omega) (by omega) (.inr (by omega))]

theorem pointFromTable_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    {o : Nat} (hp : s.gpr .r12 = b + BitVec.ofNat 32 o) (hlo : 1600 ≤ o)
    (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t => point (env t.mem b) 0 1 2 3 = tablePoint s.mem b o ∧
      AllLim t.mem b ∧ TableKeep b 64 256 s t := by
  refine WP.mono (fromTablePrefix_ok hc hl hp hlo ho 4 (by decide)) fun t ⟨hv, hlt, hk⟩ => ?_
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  refine ⟨?_, hlt, hk⟩
  change env t.mem b 0 = _ at h0
  change env t.mem b 1 = _ at h1
  change env t.mem b 2 = _ at h2
  change env t.mem b 3 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

end VG.Proof.Ed25519.Arm
