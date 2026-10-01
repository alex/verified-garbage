import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Correct
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value)

def Slots (vs : List Value) (s t : State) : Prop :=
  ∀ j (hj : j < vs.length), Whole.slots (esp s) t j = argValue s (vs[j]'hj)

def initValues : List Value := [.caller 2 0]
def updateValues : List Value := [.caller 2 0, .const 0, .const 0, .caller 1 0, .const 32, .caller 2 192]
def finalizeValues : List Value := [.caller 2 0, .const 32, .const 0, .frame 192, .caller 2 192]
def baseValues : List Value := [.caller 0 0, .frame 32, .caller 2 0]

def init_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots initValues s t) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < initValues.length), Whole.slots (esp s) t j = argValue s (initValues[j]'hj) at hs
  unfold initValues at hs
  have a0 := hs 0 (by decide)
  change Whole.slots (esp s) t 0 = arg s 2 + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have H := hashSpace h
  have hp := Whole.init_pre hc.esp H a0
  have cov : Covers (Whole.initRd (esp s) ++ Whole.initWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s)))
  have ws := hash_writes (s := s) (rs := Whole.initWr (arg s 2)) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin s))
  exact ⟨Whole.initRd (esp s), Whole.initWr (arg s 2), hp, cov, ws⟩

def update_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots updateValues s t) :
    Whole.CallReady Proof.Sha512.updateX86 (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < updateValues.length), Whole.slots (esp s) t j = argValue s (updateValues[j]'hj) at hs
  unfold updateValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  have a5 := hs 5 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  have H := hashSpace h
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 h.sc
    (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))) h.seed
  have cov : Covers (Whole.updateRd (esp s) (arg s 1) 32 ++ Whole.hashWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inr (.inr ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.hashWr (arg s 2)) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inr (workWithin h))
  exact ⟨Whole.updateRd (esp s) (arg s 1) 32, Whole.hashWr (arg s 2), hp, cov, ws⟩

def finalize_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots finalizeValues s t) :
    Whole.CallReady Proof.Sha512.finalizeX86 (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < finalizeValues.length), Whole.slots (esp s) t j = argValue s (finalizeValues[j]'hj) at hs
  unfold finalizeValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4
  have H := hashSpace h
  have ds : Whole.Within ⟨(digestPtr s).setWidth 64, 64⟩ (Whole.FR (esp s)) :=
    ⟨192, digest_addr h, by change 192 + 64 ≤ 256; decide⟩
  have dd : Region.Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ (SCR s) :=
    h.kc.sub_left (fun p hp => Whole.frame_sub (esp s) p (ds.sub p hp))
  have db : (below (esp s) 24).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    change Region.Disjoint ⟨(esp s - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth H.below]
    exact Offset.disjoint_below_above _ (by decide)
  have da : (Whole.ARGS (esp s) 20).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have df : (digestPtr s).toNat + 64 ≤ 2 ^ 32 := by
    change (esp s + BitVec.ofNat 32 192).toNat + 64 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 192).toNat = 192 from rfl]
    have fe := H.frameFit
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 dd db da df
  have cov : Covers (Whole.finalizeRd (esp s) ++ Whole.finalizeWr (arg s 2) (digestPtr s))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inl ds
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.finalizeWr (arg s 2) (digestPtr s)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inl ds
    · exact .inr (workWithin h))
  exact ⟨Whole.finalizeRd (esp s), Whole.finalizeWr (arg s 2) (digestPtr s), hp, cov, ws⟩

def base_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots baseValues s t) :
    Whole.CallReady scalarBaseLocal (esp s) (pkRd s) (pkWr s) t := by
  unfold Slots baseValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have ha : BaseArgs s t := ⟨a0, a1, a2⟩
  have scalarWithin : Whole.Within ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.FR (esp s)) :=
    ⟨32, scalarPtr_addr h.toBounds, by change 32 + 32 ≤ 256; decide⟩
  have cov : Covers (baseRd s ++ pkWr s) (pkRd s ++ Whole.FR (esp s) :: pkWr s) := by
    refine Covers.of_sub ?_
    simp only [baseRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨Whole.FR (esp s), by simp, scalarWithin⟩
    · exact ⟨Whole.FR (esp s), by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨OUT s, by simp, 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    · exact ⟨SCR s, by simp, 0, by simp, by change 0 + 8192 ≤ 8192; decide⟩
  have ws : ∀ r ∈ pkWr s, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R :=
    fun r hr => .inr ⟨r, hr, 0, by simp, by simp⟩
  exact ⟨baseRd s, pkWr s, base_pre h hc ha, cov, ws⟩

end VG.Proof.Ed25519.X86.PublicKey
