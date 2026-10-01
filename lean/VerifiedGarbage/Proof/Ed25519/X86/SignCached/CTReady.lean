import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashFinalize
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashUpdate
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.MulAdd
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def init_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    (a0 : Whole.slots L.E s 0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have cov := hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L))
  have ws := hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin L))
  exact ⟨_, _, Whole.init_pre hc.esp H a0, cov, ws⟩

def update_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {c p n : BitVec 32}
    (hi : Input L p n) (ha : UpdateArgs L c p n s) :
    Whole.CallReady Proof.Sha512.updateX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, _, _, a3, a4, a5⟩ := ha
  have H := hashSpace hL
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def finalize_ready (hc : Ctx L g m₀ s) (hL : L.Ok) {count : BitVec 64}
    (ha : FinArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeX86 L.E L.inputs L.outputs s := by
  obtain ⟨a0, a3, a4, _⟩ := ha
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  exact ⟨_, _, hp, cov, ws⟩

def reduce_ready (hc : Ctx L g m₀ s) (hL : L.Ok)
    {d : Nat} (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : Whole.slots L.E s 0 = L.E + BitVec.ofNat 32 d)
    (a1 : Whole.slots L.E s 1 = L.E + 192) (a2 : Whole.slots L.E s 2 = L.scr) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have wo : Whole.Within ⟨(L.E + BitVec.ofNat 32 d).setWidth 64, 32⟩ L.FR :=
    ⟨d, Whole.frame_addr H.frameFit (by omega), hd'⟩
  have cov : Covers (Whole.reduceRd L.E ++ Whole.reduceWr L.E L.scr d)
      (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [Whole.reduceRd, Whole.reduceWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (digestWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inl wo
    · exact scratch_covered ⟨0, by simp, by simp⟩
  have ws : ∀ r ∈ Whole.reduceWr L.E L.scr d,
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply hash_writes
    simp only [Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨0, by simp, by simp⟩
  exact ⟨_, _, Whole.reduce_pre hc H hd hd' a0 a1 a2, cov, ws⟩

def base_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov := hash_covers (L := L) (rs := baseRd L ++ baseWr L) (by
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  exact ⟨_, _, base_pre hc hL ha, cov, ws⟩

def mul_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov := hash_covers (L := L) (rs := mulRd L ++ mulWr L) (by
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  exact ⟨_, _, mul_pre hc hL ha, cov, ws⟩

end VG.Proof.Ed25519.X86.SignCached
