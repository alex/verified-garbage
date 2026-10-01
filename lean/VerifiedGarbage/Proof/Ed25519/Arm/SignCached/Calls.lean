import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Layout
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm

variable {L : Lay}

def field (L : Lay) (d : Nat) : Region := ⟨State.addr L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 184, 64⟩
def baseOut (L : Lay) : Region := ⟨State.addr L.out, 32⟩
def half (L : Lay) : Region := ⟨State.addr L.out + BitVec.ofNat 64 32, 32⟩

theorem fieldWithin (L : Lay) {d : Nat} (hd : d + 32 ≤ 248) : Whole.Within (field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : Lay) : Whole.Within (digest L) L.FR := ⟨184, rfl, by change 184 + 64 ≤ 248; decide⟩
theorem baseWithin (L : Lay) : Whole.Within (baseOut L) L.OUT := ⟨0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
theorem halfWithin (L : Lay) : Whole.Within (half L) L.OUT := ⟨32, rfl, by change 32 + 32 ≤ 64; decide⟩
theorem scratchWithin (L : Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

theorem covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  apply Covers.of_sub
  intro r hr
  rcases h r hr with hf | ⟨R, hR, hsub⟩
  · exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hsub⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem scratch_covered (L : Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], scratchWithin L⟩

theorem output_covered {r : Region} (h : Whole.Within r L.OUT) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨L.OUT, by simp [Lay.outputs], h⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.OUT ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | ho | hs
  · exact .inl hf
  · exact .inr ⟨L.OUT, by simp [Lay.outputs], ho⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], hs⟩

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 248) :
    (field L d).Disjoint L.SCR := hL.kc.sub_left (fieldWithin L hd).sub

theorem field_mem {m n : Mem} (hm : n = m) (d : Nat) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by rw [hm]

theorem frame_addr (hL : L.Ok) {d : Nat} (hd : d < 272) :
    State.addr (L.E + BitVec.ofNat 32 d) = State.addr L.E + BitVec.ofNat 64 d :=
  addr_add (by have := hL.top; omega)

theorem frame_fit (hL : L.Ok) {d n : Nat} (hd : d + n ≤ 248) :
    (L.E + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  have ht := hL.top
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : L.E.toNat + d < 2 ^ 32)]
  omega

end VG.Proof.Ed25519.Arm.SignCached
