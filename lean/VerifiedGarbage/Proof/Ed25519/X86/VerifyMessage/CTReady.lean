import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT

namespace VG.Proof.Ed25519.X86.VerifyMessage
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
    (a0 : Whole.slots L.E s 0 = L.E + 128)
    (a1 : Whole.slots L.E s 1 = L.E + 192) (a2 : Whole.slots L.E s 2 = L.scr) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have H := hashSpace hL
  have wo : Whole.Within ⟨(L.E + 128).setWidth 64, 32⟩ L.FR :=
    ⟨128, Whole.frame_addr H.frameFit (by decide), by change 128 + 32 ≤ 256; decide⟩
  have cov : Covers (Whole.reduceRd L.E ++ Whole.reduceWr L.E L.scr 128)
      (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [Whole.reduceRd, Whole.reduceWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (digestWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inl wo
    · exact scratch_covered ⟨0, by simp, by simp⟩
  have ws : ∀ r ∈ Whole.reduceWr L.E L.scr 128,
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply hash_writes
    simp only [Whole.reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨0, by simp, by simp⟩
  exact ⟨_, _, Whole.reduce_pre hc H (by decide) (by decide) a0 a1 a2, cov, ws⟩

def equation_ready (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    Whole.CallReady verifyLocal L.E L.inputs L.outputs s := by
  have wz : Whole.Within ⟨L.scr.setWidth 64, 0⟩ L.SCR := ⟨0, by simp, by change 0 ≤ 8192; decide⟩
  have wsc : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩
  have cov : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [equationRd, equationWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inl (challengeWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered wz
    · exact scratch_covered wsc
  have ws : ∀ r ∈ equationWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
    hash_writes (by
      simp only [equationWr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact .inr wz
      · exact .inr wsc)
  exact ⟨_, _, equation_pre hc hL ha, cov, ws⟩

end VG.Proof.Ed25519.X86.VerifyMessage
