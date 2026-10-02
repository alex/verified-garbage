import VerifiedGarbage.Proof.X448.X86_64.Finish
import VerifiedGarbage.Proof.X448.X86_64.Ladder
import VerifiedGarbage.Proof.X448.X86_64.FinalSwap
import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# X448 on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.X448.x448Contract` it uses, stated for x86-64), and the correctness of
`vg_x448` against it: every write is in the working space but the result's, so
the arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

namespace VG.Proof.X448

open VG VG.X86_64 in
/-- `vg_x448(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`. -/
def x448X86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 56⟩
    let scalar : Region := ⟨s.gpr .rsi, 56⟩
    let point : Region := ⟨s.gpr .rdx, 56⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .rdi) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .rsi) 56)
      (Spec.X448.bytesAt s.mem (s.gpr .rdx) 56)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.X448

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

section
variable (s₀ : State)
abbrev outR : Region := ⟨s₀.gpr .rdi, 56⟩
abbrev scalarR : Region := ⟨s₀.gpr .rsi, 56⟩
abbrev pointR : Region := ⟨s₀.gpr .rdx, 56⟩
abbrev scR : Region := ⟨s₀.gpr .rcx, 8192⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [scalarR s₀, pointR s₀]
  wr : s₀.wr = [outR s₀, scR s₀]
  out_sc : (outR s₀).Disjoint (scR s₀)
  scalar_sc : (scalarR s₀).Disjoint (scR s₀)
  point_sc : (pointR s₀).Disjoint (scR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_sc : (retR s₀).Disjoint (scR s₀)
  sc_fit : (s₀.gpr .rcx).toNat + 8192 ≤ 2 ^ 64

theorem Pre.of (s₀ : State) (h : Proof.X448.x448X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

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
    (hi : slot i.val + 128 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa x448 s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X448.x448X86_64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .rcx = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .rdx) j) 1 := fun j hj =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .rdx) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .rsi) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, b₁, r12₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (off (s₀.gpr .rsi) j) 1 := fun j hj =>
    ⟨scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (bits_ok hs₁ (k₁.1 _ (by decide)) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : Keeps [.rax, .rdx, .rbx] s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono (movRsi_ok s₂) fun s₃ ⟨rsi₃, m₃, k₃⟩ => ?_)
  have k03 := k₁.then (k₂.then k₃)
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have o03 : Outside base 0 8192 s₀.mem s₃.mem := by
    rw [m₃]; exact o₁.trans (o₂.mono (by decide) (by decide))
  have sv₃ : Saved base s₀.gpr s₃.mem := by rw [m₃]; exact sv₁.outside o₂ (by decide)
  have e₃ : ∀ i : Index, E s₃.mem base i = E s₁.mem base i := by
    intro i; rw [m₃]; exact E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₃ : BoundedEnv s₃.mem base := by
    intro i j hj
    rw [m₃, o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (ladder_ok (s₀ := s₃) (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .rsi) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .rdx) 56)))
    (fun t ht => by rw [m₃, bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨(hg _ (by decide)).trans hs₃.rdi, hw ▸ hs₃.wr, hn⟩, hm ▸ b₃,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₃ 0, x1₁], by rw [hm, e₃ 1, x2₁]; rfl,
      by rw [hm, e₃ 2, z2₁]; rfl, by rw [hm, e₃ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₃ 4, z3₁]; rfl,
      by rw [hm, m₃, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .rsi) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .rdx) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k36 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have rsi₆ : s₆.gpr .rsi = s₀.gpr .rdi :=
    (k36.1 _ (by decide)).trans (rsi₃.trans ((g₂ _ (by decide)).trans r12₁))
  have k06 := k03.then k36
  have hw₆ : ∀ j < 56, InRegions s₆.wr (off (s₀.gpr .rdi) j) 1 := fun j hj =>
    ⟨outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (finish_ok (k₆.scr hs₅) b₆ rsi₆ hw₆
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨rb, r12, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  have o06 : Outside base 0 8192 s₀.mem s₆.mem :=
    o03.trans ((L.mem.whole (by decide) (by decide)).trans
      ((k₅.mem.whole (by decide) (by decide)).trans (k₆.mem.whole (by decide) (by decide))))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact kall.1 _ (by decide)
    · exact kall.1 _ (by decide)
    · exact r12
    · exact kall.1 _ (by decide)
    · exact kall.1 _ (by decide)
    · exact kall.1 _ (by decide)
  · have frame : Frame [scR s₀, outR s₀] s₀.mem s'.mem := by
      rw [← hbase] at fm o06
      exact (o06.frame.mono (by simp)).trans fm
    exact frame.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_sc
      · exact hp.ret_out) (by decide)
  · change Spec.X448.bytesAt s'.mem (s₀.gpr .rdi) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, invEnv_x2, invEnv_eval, e₅]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, cswap_fst, cswap_fst]

end VG.Proof.X448.X86_64
