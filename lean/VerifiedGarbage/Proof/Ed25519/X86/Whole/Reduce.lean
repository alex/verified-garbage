import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.X86.ScalarVerified

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86

theorem frame_addr {E : BitVec 32} {d : Nat} (hf : E.toNat + 256 ≤ 2 ^ 32) (hd : d < 256) :
    (E + BitVec.ofNat 32 d).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega)

theorem frame_fit {E : BitVec 32} {d n : Nat} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hd : d < 256) (hn : d + n ≤ 256) : (E + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem frame_below {E : BitVec 32} {d n : Nat} (he : 24 ≤ E.toNat)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hd : d < 256) (hn : d + n ≤ 256) :
    (below E 4).Disjoint ⟨(E + BitVec.ofNat 32 d).setWidth 64, n⟩ := by
  change Region.Disjoint ⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
  rw [Taint.sub_setWidth (by omega : 4 ≤ E.toNat), frame_addr hf hd]
  exact Offset.disjoint_below_above _ (by omega)

theorem reduce_nosp : NoSp scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse scalarReduce = 0 := by lit_decide

def reduceRd (E : BitVec 32) : List Region :=
  [⟨(E + 192).setWidth 64, 64⟩, ⟨E.setWidth 64, 12⟩]
def reduceWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩, ⟨scr.setWidth 64, 8192⟩]

variable {E scr : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} {d : Nat}

theorem reduce_pre (hc : Ctx E g m₀ rd wr s) (H : HashSpace E scr)
    (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : slots E s 0 = E + BitVec.ofNat 32 d)
    (a1 : slots E s 1 = E + 192) (a2 : slots E s 2 = scr) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd E) (reduceWr E scr d)) := by
  have ca {j : Nat} (hj : j < 64) := call_arg hc.esp H.below H.frameFit hj
  have e0 := (ca (j := 0) (by decide)).trans a0
  have e1 := (ca (j := 1) (by decide)).trans a1
  have e2 := (ca (j := 2) (by decide)).trans a2
  have outSub : Region.Sub ⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩ (STK E) := by
    rw [frame_addr H.frameFit (by omega)]
    exact fun p hp => frame_sub E p (Offset.sub_base _ hd' p hp)
  have digSub : Region.Sub ⟨(E + 192).setWidth 64, 64⟩ (STK E) := by
    have e : (E + 192).setWidth 64 = E.setWidth 64 + 192 := frame_addr H.frameFit (by decide : 192 < 256)
    rw [e]
    exact fun p hp => frame_sub E p (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp)
  have argSub : Region.Sub ⟨E.setWidth 64, 12⟩ (STK E) :=
    fun p hp => frame_sub E p (Region.sub_prefix (by decide) p hp)
  have ab := arg_base hc.esp (reduceRd E) (reduceWr E scr d)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, e0, e1, e2, ab]
  refine ⟨rfl, rfl, H.sep.sub_left outSub, H.sep.sub_left digSub, ?_, H.sep.sub_left argSub,
    frame_below H.below H.frameFit (by omega) hd', H.sep.sub_left (below_sub_stack H.below (by decide)),
    frame_fit H.frameFit (by omega) hd', frame_fit H.frameFit (by decide) (by decide), H.scratchFit, ?_⟩
  · rw [frame_addr H.frameFit (by omega)]
    exact Offset.base_disjoint _ (by omega) (by omega)
  · have e : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by have := H.below; omega)
    rw [e]
    have := H.frameFit; omega

theorem reduce_call (hc : Ctx E g m₀ rd wr s) (H : HashSpace E scr)
    (hscr : (⟨scr.setWidth 64, 8192⟩ : Region) ∈ wr)
    (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : slots E s 0 = E + BitVec.ofNat 32 d)
    (a1 : slots E s 1 = E + 192) (a2 : slots E s 2 = scr) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx E g m₀ rd wr t ∧
      Frame (reduceWr E scr d ++ [below E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((E + BitVec.ofNat 32 d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem ((E + 192).setWidth 64) 64) := by
  have wd : Within ⟨(E + 192).setWidth 64, 64⟩ (FR E) :=
    ⟨192, frame_addr H.frameFit (by decide), by change 192 + 64 ≤ 256; decide⟩
  have wo : Within ⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩ (FR E) :=
    ⟨d, frame_addr H.frameFit (by omega), hd'⟩
  have cov : Covers (reduceRd E ++ reduceWr E scr d) (rd ++ FR E :: wr) := by
    refine Covers.of_sub ?_
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨FR E, by simp, wd⟩
    · exact ⟨FR E, by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨FR E, by simp, wo⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ hscr), 0, by simp, by simp⟩
  have ws : ∀ r ∈ reduceWr E scr d, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨_, hscr, 0, by simp, by simp⟩
  with_reducible
    refine call_ok hc H.below scalarReduce_ok reduce_nosp (by rw [reduce_stack]; decide)
      (reduce_pre hc H hd hd' a0 a1 a2) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨t₂, hm, _, hp⟩ := post
  have ca {j : Nat} (hj : j < 64) := call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt t₂.mem ((arg s.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 64) at hp
  rw [hm, (ca (j := 0) (by decide)).trans a0, (ca (j := 1) (by decide)).trans a1] at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  apply callEntry_bytes (r := ⟨(E + 192).setWidth 64, 64⟩) ?_ (by change 64 ≤ 2 ^ 64; decide)
  rw [hc.esp]
  exact (frame_below H.below H.frameFit (by decide : 192 < 256) (by decide : 192 + 64 ≤ 256)).symm

end VG.Proof.Ed25519.X86.Whole
