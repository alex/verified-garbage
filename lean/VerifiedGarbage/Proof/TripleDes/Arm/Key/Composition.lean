import VerifiedGarbage.Proof.TripleDes.Arm.Key.Copy
import VerifiedGarbage.Proof.TripleDes.KeyMemory

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨(State.addr (s.gpr .r0)), (s.gpr .r1).toNat⟩
abbrev outputR (s : State) : Region := ⟨(State.addr (s.gpr .r2)), 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot ((State.addr (origin.gpr .r2))) c j) 64 =
    ((componentKeys origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 4 ≤ (s.gpr .r1).toNat →
    InRegions (s.rd ++ s.wr) ((State.addr (s.gpr .r0)) + BitVec.ofNat 64 offset) 4
  writes : ∀ offset, offset + 4 ≤ 384 → InRegions s.wr ((State.addr (s.gpr .r2)) + BitVec.ofNat 64 offset) 4
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .r1).toNat
  keyFit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  outputFit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .r1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.Arm.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have keyFit : (s.gpr .r0).toNat + 8 * c + 8 ≤ 2 ^ 32 := by
    rw [hs.reg .r0 (by decide)]
    omega_using [hp.keyFit, offsetBound]
  have outputFit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 := by
    rw [hs.reg .r2 (by decide)]; exact hp.outputFit
  have read : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (8 * c + 4 * t))) 4 := by
    intro t ht
    rw [hs.rd, hs.wr, hs.reg .r0 (by decide), addr_add (by omega_using [hp.keyFit, offsetBound, ht])]
    exact hp.reads _ (by omega_using [offsetBound, ht])
  have write : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * c) +
        BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4 := by
    intro j hj t ht
    rw [hs.wr, hs.reg .r2 (by decide), Offset.add_ofNat_add_ofNat,
      Offset.add_ofNat_add_ofNat, addr_add (by omega_using [hp.outputFit, hc, hj, ht])]
    exact hp.writes _ (by omega_using [hc, hj, ht])
  apply WP.mono (component_ok s (8 * c) c hc (by omega) keyFit outputFit read write)
  intro t ht
  have frame : Frame [⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .r2 (by decide), addr_add (by omega_using [hp.outputFit, hc])] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem ((State.addr (s.gpr .r0)) + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem ((State.addr (origin.gpr .r0)) + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .r0 (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [addr_add (a := s.gpr .r0) (k := 8 * c) (by omega_using [keyFit]), key, hs.reg .r2 (by decide),
        addr_add (by omega_using [hp.outputFit, hc]), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot ((State.addr (origin.gpr .r2))) k j) 8).Disjoint
          ⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot ((State.addr (origin.gpr .r2))) k j) (w := 64) (r := ⟨slot ((State.addr (origin.gpr .r2))) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .r1).toNat = 16) :
    WP isa (.block Impl.TripleDes.Arm.Key.copyThird) s (Components origin · 3) := by
  have fit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 := by
    rw [hs.reg .r2 (by decide)]; exact hp.outputFit
  have reads : ∀ i < 16, ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (8 * i + 4 * t))) 4 := by
    intro i hi t ht
    rw [hs.rd, hs.wr, hs.reg .r2 (by decide), addr_add (by omega_using [hp.outputFit, hi, ht])]
    obtain ⟨r, hr, hc⟩ := hp.writes (8 * i + 4 * t) (by omega_using [hi, ht])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have writes : ∀ i < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (256 + 8 * i + 4 * t))) 4 := by
    intro i hi t ht
    rw [hs.wr, hs.reg .r2 (by decide), addr_add (by omega_using [hp.outputFit, hi, ht])]
    exact hp.writes _ (by omega_using [hi, ht])
  have code : Impl.TripleDes.Arm.Key.copyThird = copyCode 16 := rfl
  rw [code]
  apply WP.mono (copy_ok s 16 (by decide) fit reads writes)
  intro t ht
  have frame : Frame [⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 256, 128⟩] s.mem t.mem := by
    have h := ht.frame
    rw [hs.reg .r2 (by decide)] at h
    exact h
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ?_, hs.frame.trans (frame.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat 2 =
          componentKeys origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat 0 := by
        rw [hn]; rfl
      have h := ht.keys j hj
      rw [hs.reg .r2 (by decide)] at h
      change t.mem.readW ((State.addr (origin.gpr .r2)) + BitVec.ofNat 64 (256 + 8 * j)) 64 = _
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      simp only [slot, Nat.mul_zero, Nat.zero_add] at first
      exact h.trans first
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot ((State.addr (origin.gpr .r2))) c j) 8).Disjoint
          ⟨(State.addr (origin.gpr .r2)) + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := frame.readW (a := slot ((State.addr (origin.gpr .r2))) c j) (w := 64) (r := ⟨slot ((State.addr (origin.gpr .r2))) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · intro r hr
    have unused : ∀ r ∈ keyKept, r ≠ .r4 ∧ r ≠ .r5 := by decide
    exact (ht.reg r (unused r hr).1 (unused r hr).2).trans (hs.reg r hr)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem ((State.addr (origin.gpr .r2))) =
      VG.Proof.TripleDes.expandedMemory origin.mem ((State.addr (origin.gpr .r0))) (origin.gpr .r1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem ((State.addr (origin.gpr .r2))) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys


end VG.Proof.TripleDes.Arm.Key
