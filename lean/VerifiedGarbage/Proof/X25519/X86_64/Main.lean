import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# X25519 on x86-64: the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X25519.x25519Contract` it uses, stated
for x86-64), and the correctness of `vg_x25519` against it: every write is in
the working space but the result's, so the arguments are read unchanged, the
callee-saved registers restored from the working space, and the return
address kept.
-/

namespace VG.Proof.X25519

open VG VG.X86_64 in
/-- `vg_x25519(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`. -/
def x25519X86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 32⟩
    let scalar : Region := ⟨s.gpr .rsi, 32⟩
    let point : Region := ⟨s.gpr .rdx, 32⟩
    let scratch : Region := ⟨s.gpr .rcx, 4096⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 4096 ≤ 2 ^ 64
  post s s' := Spec.X25519.bytesAt s'.mem (s.gpr .rdi) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .rsi) 32)
      (Spec.X25519.bytesAt s.mem (s.gpr .rdx) 32)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.X25519

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

section
variable (s₀ : State)
abbrev outR : Region := ⟨s₀.gpr .rdi, 32⟩
abbrev scalarR : Region := ⟨s₀.gpr .rsi, 32⟩
abbrev pointR : Region := ⟨s₀.gpr .rdx, 32⟩
abbrev scR : Region := ⟨s₀.gpr .rcx, 4096⟩
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
  sc_fit : (s₀.gpr .rcx).toNat + 4096 ≤ 2 ^ 64

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 4096⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 4096 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 4096 m m')
    (hp : ∀ i < 32, 4096 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X25519.bytesAt m' p 32 = Spec.X25519.bytesAt m p 32 := by
  simp only [Spec.X25519.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Fin 128)
    (hi : 32 * i.val + 32 ≤ o ∨ o + n ≤ 32 * i.val) : E m' base i = E m base i := by
  simp only [E, F]; rw [h.fe hi (by omega)]

theorem Outside.frame {base : Addr} {m m' : Mem} (h : Outside base 0 4096 m m') :
    Frame [⟨base, 4096⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this; show 0 + 4096 ≤ (x - base).toNat; omega))

variable {fld : Field} (hf : FieldOk fld)

theorem finish_eq : finish fld = fld.mul X2 X2 T1 ++ (freeze X2 ++ (restore ++
    ([.store (at_ .rsi 0) .r8, .store (at_ .rsi 8) .r9, .store (at_ .rsi 16) .r10,
      .store (at_ .rsi 24) .r11] : List Instr))) := by
  simp only [finish, List.append_assoc]

theorem x25519_eq' : x25519With fld = .seq (.block setup) (.seq bits (.seq
    (.block ([.mov .rsi (.reg .r12)] : List Instr)) (.seq (ladder fld) (.seq (.block lastSwap)
    (.seq (Impl.X25519.X86_64.invert fld) (.block (finish fld))))))) := rfl

include hf in
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa (x25519With fld) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X25519.x25519X86_64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .rcx = b := ⟨_, rfl⟩
  have hn : base.toNat + 4096 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 4096⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hwo : outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hr : ∀ d, d + 8 ≤ 32 → InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .rdx) d) 8 := fun d hd =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ hd (by omega)⟩
  rw [x25519_eq']
  refine WP.seq (WP.mono (setup_ok hbase hw₀ hn rfl hr)
    fun s₁ ⟨hs₁, r12₁, g₁, rd₁, wr₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have hkr : ∀ q < 32, InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 q) 1 :=
    fun q hq => ⟨scalarR s₀, by rw [rd₁, hp.rd]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 32) (by omega) (by omega)⟩
  have hkd : ∀ q < 32, 4096 ≤ ofs base (s₀.gpr .rsi + BitVec.ofNat 64 q) :=
    fun q hq => far (hbase ▸ hp.scalar_sc) hq (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ (g₁ _ (by decide)) hkr hkd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (movRsi_ok s₂) fun s₃ ⟨rsi₃, k₃⟩ => ?_)
  have hs₃ : Scr s₃ base :=
    ⟨by rw [k₃.1 _ (by decide), g₂ _ (by decide)]; exact hs₁.rdi,
      by rw [k₃.2.2.2, wr₂]; exact hs₁.wr, hn⟩
  have hkb := bytesAt_outside o₁ hkd
  have e₃ : ∀ i : Fin 128, i.val < 24 → E s₃.mem base i = E s₁.mem base i :=
    fun i h₂ => by rw [k₃.2.1]; exact E_outside o₂ i (Or.inl (by simp only [BITS]; omega))
  refine WP.seq (WP.mono (ladder_ok hf (s₀ := s₃) (s := s₃)
    (k := Spec.X25519.decodeScalar25519 (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rsi) 32))
    (u := toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rdx) 32)))
    (fun t ht => by rw [k₃.2.1, b₂ t ht, hkb])
    (fun s' hb g m rd wr => ⟨⟨by rw [g _ (by decide)]; exact hs₃.rdi, by rw [wr]; exact hs₃.wr, hn⟩,
      fun r _ h => g r h, hb, rd, wr, by rw [m]; exact Outside.refl _ _ _ _,
      by rw [m, e₃ 2 (by decide), x1₁],
      by rw [m, e₃ 3 (by decide), x2₁]; rfl,
      by rw [m, e₃ 4 (by decide), z2₁]; rfl,
      by rw [m, e₃ 5 (by decide), x3₁]; rfl,
      by rw [m, e₃ 6 (by decide), z3₁]; rfl,
      by rw [m, k₃.2.1, o₂.word (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (lastSwap_ok L.scr
    (by have := ladderAfter_swap_le
          (Spec.X25519.decodeScalar25519 (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rsi) 32))
          (toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s₀.mem (s₀.gpr .rdx) 32)))
          (n := 0) (by omega)
        omega) L.swap L.x2 L.z2 L.x3 L.z3) fun s₅ ⟨K₅, e3₅, e4₅⟩ => ?_)
  have hs₅ := K₅.scr L.scr
  refine WP.seq (WP.mono (invert_ok hf hs₅) fun s₆ ⟨g₆, rd₆, wr₆, o₆, e₆⟩ => ?_)
  have hs₆ : Scr s₆ base := ⟨(g₆ _ (by decide) (by decide)).trans hs₅.rdi, wr₆ ▸ hs₅.wr, hn⟩
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (mulE hf hs₆ 3 3 17 (by decide)) fun s₇ ⟨K₇, e₇⟩ => ?_
  have hs₇ := K₇.scr hs₆
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs₇ (a := X2) (by decide)) fun s₈ ⟨v₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  have sv₈ : Saved base s₀.gpr s₈.mem := by
    have sv₃ : Saved base s₀.gpr s₃.mem := by rw [k₃.2.1]; exact sv₁.outside o₂ (by decide)
    rw [k₈.2.1]
    exact (((sv₃.outside L.mem (by decide)).outside K₅.mem (by decide)).outside o₆
      (by decide)).outside K₇.mem (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hs₈ sv₈) fun s₉ ⟨r₉, g₉, m₉, rd₉, wr₉⟩ => ?_
  have rsi₉ : s₉.gpr .rsi = s₀.gpr .rdi := by
    rw [g₉ _ (by decide), k₈.1 _ (by decide), K₇.gpr _ (by decide), g₆ _ (by decide) (by decide),
      K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide), rsi₃, g₂ _ (by decide), r12₁]
  have hwo₉ : outR s₀ ∈ s₉.wr := by
    rw [wr₉, k₈.2.2.2, K₇.wr, wr₆, K₅.wr, L.wr, k₃.2.2.2, wr₂, wr₁]; exact hwo
  refine WP.mono (outStores_ok rsi₉ hwo₉) fun s' ⟨m', g', _, _⟩ => ?_
  have O₃ : Outside base 0 4096 s₀.mem s₃.mem := by
    rw [k₃.2.1]; exact o₁.trans (o₂.mono (by decide) (by decide))
  have O : Outside base 0 4096 s₀.mem s₉.mem := by
    rw [m₉, k₈.2.1]
    exact (((O₃.trans (L.mem.mono (by decide) (by decide))).trans
      (K₅.mem.mono (by decide) (by decide))).trans (o₆.mono (by decide) (by decide))).trans
      (K₇.mem.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g']
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₉ (.rbx, 0) (by decide)
    · exact r₉ (.rbp, 8) (by decide)
    · rw [g₉ _ (by decide), k₈.1 _ (by decide), K₇.gpr _ (by decide),
        g₆ _ (by decide) (by decide), K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide),
        k₃.1 _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
    · exact r₉ (.r12, 16) (by decide)
    · exact r₉ (.r13, 24) (by decide)
    · exact r₉ (.r14, 32) (by decide)
    · exact r₉ (.r15, 40) (by decide)
  · have F₁ : Frame [scR s₀, outR s₀] s₀.mem s'.mem := by
      rw [m']
      have c : ∀ d, d + 8 ≤ 32 → (outR s₀).Contains (off (s₀.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hmem : outR s₀ ∈ [scR s₀, outR s₀] := by simp
      exact ((((hbase ▸ O.frame).mono (by simp)).writeW hmem _ (c 0 (by omega))).writeW hmem _
        (c 8 (by omega))).writeW hmem _ (c 16 (by omega)) |>.writeW hmem _ (c 24 (by omega))
    exact F₁.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_sc
      · exact hp.ret_out) (by decide)
  · show Spec.X25519.bytesAt s'.mem (s₀.gpr .rdi) 32 = _
    rw [m', bytesAt_st4, x25519_eq]
    dsimp only
    rw [encodeUCoordinate_eq]
    refine congrArg (leBytes 32) ?_
    rw [g₉ .r8 (by decide), g₉ .r9 (by decide), g₉ .r10 (by decide), g₉ .r11 (by decide), v₈,
      ← toFe_val]
    change (E s₇.mem base 3).val = _
    rw [e₇]
    simp only [opMul, Function.update_self]
    rw [E_outside o₆ 3 (by decide), e3₅, e₆, e4₅]

end VG.Proof.X25519.X86_64
