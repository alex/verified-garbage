import VerifiedGarbage.Proof.X448.Arm.Bits
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Ladder
import VerifiedGarbage.Proof.X448.Arm.FinalSwap
import VerifiedGarbage.Proof.X448.Arm.Inv
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.Arm.Target

/-!
# X448 on ARMv7: the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X448.x448Contract` it uses, stated
for ARMv7), and the correctness of `vg_x448` against it: every write is in
the working space but the result's, so the arguments are read unchanged, the
callee-saved registers restored from the working space, and the return
address kept.
-/

namespace VG.Proof.X448

open VG VG.Arm in
/-- `vg_x448(out = r0, scalar = r1, point = r2, scratch = r3)`. -/
def x448Arm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 56⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 56⟩
    let point : Region := ⟨State.addr (s.gpr .r2), 56⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧
      (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .r0).toNat + 56 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 56 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 56 ≤ 2 ^ 32
  post s s' := Spec.X448.bytesAt s'.mem (State.addr (s.gpr .r0)) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (State.addr (s.gpr .r1)) 56)
      (Spec.X448.bytesAt s.mem (State.addr (s.gpr .r2)) 56)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

end VG.Proof.X448

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448

section
variable (s₀ : State)
abbrev outR : Region := ⟨State.addr (s₀.gpr .r0), 56⟩
abbrev scalarR : Region := ⟨State.addr (s₀.gpr .r1), 56⟩
abbrev pointR : Region := ⟨State.addr (s₀.gpr .r2), 56⟩
abbrev scR : Region := ⟨State.addr (s₀.gpr .r3), 8192⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [scalarR s₀, pointR s₀]
  wr : s₀.wr = [outR s₀, scR s₀]
  out_sc : (outR s₀).Disjoint (scR s₀)
  scalar_sc : (scalarR s₀).Disjoint (scR s₀)
  point_sc : (pointR s₀).Disjoint (scR s₀)
  sc_fit : (s₀.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  out_fit : (s₀.gpr .r0).toNat + 56 ≤ 2 ^ 32
  scalar_fit : (s₀.gpr .r1).toNat + 56 ≤ 2 ^ 32
  point_fit : (s₀.gpr .r2).toNat + 56 ≤ 2 ^ 32

theorem Pre.of (s₀ : State) (h : Proof.X448.x448Arm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa x448 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.X448.x448Arm.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s₀.gpr .r3) = b := ⟨_, rfl⟩
  have hn := hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (State.addr (s₀.gpr .r2)) j) 1 := fun j hj =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (State.addr (s₀.gpr .r2)) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off (State.addr (s₀.gpr .r1)) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (setup_ok hbase hw₀ hn rfl hp.point_fit hr hd)
    fun s₁ ⟨hs₁, b₁, savedOut₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (off (State.addr (s₀.gpr .r1)) j) 1 := fun j hj =>
    ⟨scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (bits_ok (k := State.addr (s₀.gpr .r1)) hs₁ (by rw [k₁.1 _ (by decide)])
    (by rw [k₁.1 _ (by decide)]; exact hp.scalar_fit) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : Keeps bitRegs s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  have k02 := k₁.then k₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have sv₂ : Saved base s₀.gpr s₂.mem := by exact sv₁.outside o₂ (by decide)
  have e₂ : ∀ i : Index, E s₂.mem base i = E s₁.mem base i := by
    intro i; exact E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₂ : BoundedEnv s₂.mem base := by
    intro i j hj
    rw [o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (ladder_ok (s₀ := s₂) (s := s₂)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r2)) 56)))
    (fun t ht => by rw [bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨by rw [hg _ (by decide)]; exact hs₂.r0, (hg _ (by decide)).trans hs₂.mask, hw ▸ hs₂.wr,
        by rw [hg _ (by decide)]; exact hs₂.nowrap⟩, hm ▸ b₂,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₂ 0, x1₁], by rw [hm, e₂ 1, x2₁]; rfl,
      by rw [hm, e₂ 2, z2₁]; rfl, by rw [hm, e₂ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₂ 4, z3₁]; rfl,
      by rw [hm, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r2)) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k26 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₂.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have out₆ : s₆.gpr .r12 = s₀.gpr .r0 :=
    (k26.1 _ (by decide)).trans ((g₂ _ (by decide)).trans savedOut₁)
  have k06 := k02.then k26
  have hw₆ : ∀ j < 56, InRegions s₆.wr (off (State.addr (s₀.gpr .r0)) j) 1 := fun j hj =>
    ⟨outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (finish_ok (k₆.scr hs₅) b₆ (congrArg State.addr out₆)
    (by rw [out₆]; exact hp.out_fit) hw₆
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨restored, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored 0 (by decide)
    · exact restored 1 (by decide)
    · exact restored 2 (by decide)
    · exact restored 3 (by decide)
    · exact restored 4 (by decide)
    · exact restored 5 (by decide)
    · exact restored 6 (by decide)
    · exact restored 7 (by decide)
    · exact kall.1 _ (by decide)
  · change Spec.X448.bytesAt s'.mem (State.addr (s₀.gpr .r0)) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, invEnv_x2, invEnv_eval, e₅]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, cswap_fst, cswap_fst]

end VG.Proof.X448.Arm
