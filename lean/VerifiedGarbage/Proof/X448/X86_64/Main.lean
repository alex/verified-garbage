import VerifiedGarbage.Proof.X448.X86_64.Finish
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

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 56 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  have := slot_lt i
  simp only [ACC] at this
  simp only [E, F]
  show toFe (mv m' base (slot i.val) 7) = toFe (mv m base (slot i.val) 7)
  rw [h.mv (by omega) (by omega)]

theorem Outside.frame {base : Addr} {m m' : Mem} (h : Outside base 0 8192 m m') :
    Frame [⟨base, 8192⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this; show 0 + 8192 ≤ (x - base).toNat; omega))

/-- A word of the working space, after writes to a region disjoint from it. -/
theorem word_frame {base : Addr} {m m' : Mem} {R : Region} (hF : Frame [R] m m')
    (hd : R.Disjoint ⟨base, 8192⟩) {d : Nat} (hd8 : d + 8 ≤ 8192) :
    word m' base d = word m base d := by
  refine (Mem.readW_congr fun i hi => (hF _ fun r hr hc => ?_).symm).symm
  rw [List.mem_singleton.mp hr] at hc
  refine hd _ hc ?_
  rw [Offset.add_add]
  exact Offset.contains_base base (d := d + i) (n := 1) (by omega) (by omega)

variable {fld : Field} (hf : FieldOk fld)

theorem finish_eq : finish fld = fld.mul X2 X2 T7 ++ (freeze X2 ++ (storesR .rsi 0 W ++ restore)) := by
  simp only [finish, List.append_assoc, outStores_eq]

theorem x448_eq' (lad : Prog isa) : x448Of fld lad = .seq (.block setup) (.seq bits (.seq
    (.block ([.mov .rsi (.reg .r15)] : List Instr)) (.seq lad (.seq (.block lastSwap)
    (.seq (Impl.X448.X86_64.invert fld) (.block (finish fld))))))) := rfl

include hf in
/-- X448 with any ladder `lad` that leaves the ladder's final state as
`ladder` does (`LPost`). -/
theorem correct_of {lad : Prog isa}
    (hlad : ∀ {s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}, LPre base k u s →
      WP isa lad s (LPost base k u s))
    {s₀ : State} (hp : Pre s₀) :
    WP isa (x448Of fld lad) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X448.x448X86_64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .rcx = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hwo : outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hr : ∀ d, d + 8 ≤ 56 → InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .rdx) d) 8 := fun d hd =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ hd (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .rdx) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  rw [x448_eq']
  refine WP.seq (WP.mono (setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, r15₁, g₁, rd₁, wr₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have hkr : ∀ q < 56, InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 q) 1 :=
    fun q hq => ⟨scalarR s₀, by rw [rd₁, hp.rd]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 56) (by omega) (by omega)⟩
  have hkd : ∀ q < 56, 8192 ≤ ofs base (s₀.gpr .rsi + BitVec.ofNat 64 q) :=
    fun q hq => far (hbase ▸ hp.scalar_sc) hq (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ (g₁ _ (by decide)) hkr hkd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (movRsi_ok s₂) fun s₃ ⟨rsi₃, k₃⟩ => ?_)
  have hs₃ : Scr s₃ base :=
    ⟨by rw [k₃.1 _ (by decide), g₂ _ (by decide)]; exact hs₁.rdi,
      by rw [k₃.2.2.2, wr₂]; exact hs₁.wr, hn⟩
  have hkb := bytesAt_outside o₁ hkd
  have e₃ : ∀ i : Index, E s₃.mem base i = E s₁.mem base i :=
    fun i => by
      rw [k₃.2.1]; exact E_outside o₂ i (Or.inl (by have := slot_lt i; simp only [BITS, ACC] at *; omega))
  refine WP.seq (WP.mono (hlad (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .rsi) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .rdx) 56)))
    ⟨hs₃, fun t ht => by rw [k₃.2.1, b₂ t ht, hkb],
      by rw [e₃ 0, x1₁], by rw [e₃ 1, x2₁], by rw [e₃ 2, z2₁],
      by rw [e₃ 3, x3₁], by rw [e₃ 4, z3₁],
      by rw [k₃.2.1, o₂.word (by decide) (by decide), sw₁]⟩) fun s₄ L => ?_)
  refine WP.seq (WP.mono (lastSwap_ok L.scr
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .rsi) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .rdx) 56)))
          (n := 0) (by omega)
        omega) L.swap L.x2 L.z2 L.x3 L.z3) fun s₅ ⟨K₅, e1₅, e2₅⟩ => ?_)
  have hs₅ := K₅.scr L.scr
  refine WP.seq (WP.mono (invert_ok hf hs₅) fun s₆ ⟨g₆, rd₆, wr₆, o₆, e₆⟩ => ?_)
  have hs₆ : Scr s₆ base := ⟨(g₆ _ (by decide) (by decide)).trans hs₅.rdi, wr₆ ▸ hs₅.wr, hn⟩
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (mulE hf hs₆ 1 1 21) fun s₇ ⟨K₇, e₇⟩ => ?_
  have hs₇ := K₇.scr hs₆
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs₇ (a := X2) (by decide)) fun s₈ ⟨v₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  have rsi₈ : s₈.gpr .rsi = s₀.gpr .rdi := by
    rw [k₈.1 _ (by decide), K₇.gpr _ (by decide), g₆ _ (by decide) (by decide),
      K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide), rsi₃, g₂ _ (by decide), r15₁]
  have hwo₈ : outR s₀ ∈ s₈.wr := by
    rw [k₈.2.2.2, K₇.wr, wr₆, K₅.wr, L.wr, k₃.2.2.2, wr₂, wr₁]; exact hwo
  rw [WP.block_append_iff]
  refine WP.mono (storesR_ok s₈ 0 W rsi₈ hwo₈
    (fun d _ hd => by rw [W_len] at hd; exact Offset.contains_base _ (by omega) (by omega))
    (by decide))
    fun s₉ ⟨v₉, _, F₉, g₉, rd₉, wr₉⟩ => ?_
  have sv₈ : Saved base s₀.gpr s₈.mem := by
    have sv₃ : Saved base s₀.gpr s₃.mem := by rw [k₃.2.1]; exact sv₁.outside o₂ (by decide)
    rw [k₈.2.1]
    exact (((sv₃.outside L.mem (by decide)).outside K₅.mem (by decide)).outside o₆
      (by decide)).outside K₇.mem (by decide)
  have sv₉ : Saved base s₀.gpr s₉.mem := fun rd hrd => by
    have := saved_lt rd hrd
    rw [← sv₈ rd hrd]
    exact word_frame F₉ (hbase ▸ hp.out_sc) (by omega)
  have hs₉ : Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hn⟩
  refine WP.mono (restore_ok hs₉ sv₉) fun s' ⟨r', g', m', rd', wr'⟩ => ?_
  have O₃ : Outside base 0 8192 s₀.mem s₃.mem := by
    rw [k₃.2.1]; exact o₁.trans (o₂.mono (by decide) (by decide))
  have O : Outside base 0 8192 s₀.mem s₈.mem := by
    rw [k₈.2.1]
    exact (((O₃.trans (L.mem.mono (by decide) (by decide))).trans
      (K₅.mem.mono (by decide) (by decide))).trans (o₆.mono (by decide) (by decide))).trans
      (K₇.mem.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r' (.rbx, 0) (by decide)
    · exact r' (.rbp, 8) (by decide)
    · rw [g' _ (by decide), g₉, k₈.1 _ (by decide), K₇.gpr _ (by decide),
        g₆ _ (by decide) (by decide), K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide),
        k₃.1 _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
    · exact r' (.r12, 16) (by decide)
    · exact r' (.r13, 24) (by decide)
    · exact r' (.r14, 32) (by decide)
    · exact r' (.r15, 40) (by decide)
  · have F₁ : Frame [scR s₀, outR s₀] s₀.mem s'.mem := by
      rw [m']
      exact ((hbase ▸ O.frame).mono (by simp)).trans (F₉.mono (by simp))
    exact F₁.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_sc
      · exact hp.ret_out) (by decide)
  · show Spec.X448.bytesAt s'.mem (s₀.gpr .rdi) 56 = _
    rw [m', bytesAt_mv, x448_eq]
    rw [W_len] at v₉
    rw [v₉, v₈]
    dsimp only
    rw [encodeUCoordinate_eq]
    refine congrArg (X25519.leBytes 56) ?_
    rw [← toFe_val]
    change (E s₇.mem base 1).val = _
    rw [e₇]
    simp only [opMul, Function.update_self]
    rw [E_outside o₆ 1 (by decide), e1₅, e₆, e2₅]

include hf in
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa (x448With fld) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X448.x448X86_64.post s₀ s' :=
  correct_of hf (fun h => ladder_post hf h) hp

end VG.Proof.X448.X86_64
