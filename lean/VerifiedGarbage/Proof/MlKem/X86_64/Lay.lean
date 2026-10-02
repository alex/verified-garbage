import VerifiedGarbage.Proof.MlKem.X86_64.FragK

/-!
# ML-KEM-768 on x86-64: the buffers of the top-level functions

The top-level functions keep the address of each buffer they work in (their
arguments and their working space) in a callee-saved register; a layout
(`Lay`) lists these registers with the lengths of their buffers, which are
apart from each other and from the stack. A pointer (a register and an offset)
into a buffer, and two pointers into the same buffer or different ones, are
then checked by evaluation (`inB`, `sepB`): each pair of regions a call needs
apart is, and each region is readable or writable (`Lay.disj`, `Lay.stk`,
`Lay.cR`, `Lay.cW`). A call leaves the layout as it was (`Lay.post`), and the
bytes of a region apart from those it writes (`Lay.keepBytes`,
`Lay.keepPoly`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the top-level functions write (`scratch`
and the outputs): a buffer they only read may overlap another such
buffer, but not one of these. -/
abbrev wRegs : List Reg := [.rbx, .r12, .r13]

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) : Bool :=
  inB bs p l && inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ wRegs) || decide (q.1 ∈ wRegs))) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

theorem lookup_mem : ∀ {bs : List (Reg × Nat)} {r : Reg} {n : Nat}, bs.lookup r = some n → (r, n) ∈ bs
  | [], _, _, h => by simp [List.lookup] at h
  | (r', n') :: bs, r, n, h => by
    unfold List.lookup at h
    by_cases e : r = r'
    · subst e
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have : (r == r') = false := by simp [e]
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold inB at h
  split at h
  · rename_i n hn; exact ⟨n, lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : Ptr} {l k : Nat} (h : sepB bs p l q k = true) :
    inB bs p l = true ∧ inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ wRegs ∨ q.1 ∈ wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1 |> fun h1 => ⟨h1, h.1.2, h.2⟩

/-! ## Regions -/

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 off - r.base = (a - r.base) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

theorem covers_one {X : List Region} {a : Addr} {l : Nat} (h : InRegions X a l) : Covers [⟨a, l⟩] X := by
  intro a' n' ⟨r0, hr0, hc⟩
  simp only [List.mem_singleton] at hr0
  subst hr0
  obtain ⟨r, hr, hc'⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [show a' - r.base = (a' - a) + (a - r.base) by bv_omega, BitVec.toNat_add]
  have := Nat.mod_le ((a' - a).toNat + (a - r.base).toNat) (2 ^ 64)
  omega

theorem covers_nil {X : List Region} : Covers [] X := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_cons {r : Region} {rs X : List Region} (h : Covers [r] X) (h' : Covers rs X) :
    Covers (r :: rs) X := by
  intro a n ⟨r0, hr0, hc⟩
  rcases List.mem_cons.mp hr0 with rfl | hr0
  · exact h a n ⟨r0, List.mem_singleton_self _, hc⟩
  · exact h' a n ⟨r0, hr0, hc⟩

theorem covers_append {rs ts X : List Region} (h : Covers rs X) (h' : Covers ts X) : Covers (rs ++ ts) X := by
  intro a n ⟨r0, hr0, hc⟩
  rcases List.mem_append.mp hr0 with hr0 | hr0
  · exact h a n ⟨r0, hr0, hc⟩
  · exact h' a n ⟨r0, hr0, hc⟩

/-! ## Layouts -/

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other and from the stack, not
wrapping around, and permitted. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ wRegs ∨ b'.1 ∈ wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (retR s).Disjoint ⟨s.gpr b.1, b.2⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
include L

theorem Lay.sub {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨pa s p, l⟩ ⟨s.gpr p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := inB_spec h
  exact ⟨n, hm, sub_offset' hl (by have := L.small _ hm; omega)⟩

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨pa s p, l⟩ ⟨pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := sepB_spec h
  obtain ⟨n, hn, hl⟩ := inB_spec hp
  obtain ⟨m, hm, hk⟩ := inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (sub_offset' hl (by omega))).sub_right (sub_offset' hk (by omega))
  · show Region.Disjoint ⟨s.gpr p.1 + _, l⟩ ⟨s.gpr q.1 + _, k⟩
    rw [← e]
    rcases hs with h1 | h2
    · exact off_disj h1 (by omega)
    · exact (off_disj h2 (by omega)).symm

theorem Lay.stkD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (below (s.gpr .rsp) 32).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.nwp {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : (pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.cR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : Covers [⟨pa s p, l⟩] (s.rd ++ s.wr) := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact covers_one (inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega))

theorem Lay.cW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : Covers [⟨pa s p, l⟩] s.wr := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact covers_one (inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega))

end

/-! ## What a call leaves -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨pa s w.1, w.2⟩

/-- `Post`, with the regions written given as pointers. -/
abbrev PPost (s s' : State) (ws : List (Ptr × Nat)) : Prop := Post s s' (ws.map (toR s))

/-- The registers the top-level functions keep the addresses of their buffers in. -/
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the stack. (A call keeps
every callee-saved register, `Post`; a call of `SampleNTT` changes `r15`.) -/
structure PostB (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

theorem Post.b {s s' : State} {W : List Region} (h : Post s s' W) : PostB s s' W :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
    simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), h.rsp, h.frame⟩

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (s s' : State) (ws : List (Ptr × Nat)) : Prop := PostB s s' (ws.map (toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ bases) && inB bs p l && ws.all fun w => sepB bs p l w.1 w.2

theorem Post.pa {s s' : State} {W : List Region} (hP : Post s s' W) {p : Ptr} (h : p.1 ∈ calleeSaved) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlKem.X86_64.pa, hP.cs _ h]

theorem PostB.pa {s s' : State} {W : List Region} (hP : PostB s s' W) {p : Ptr} (h : p.1 ∈ bases) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlKem.X86_64.pa, hP.bs _ h]

theorem Lay.post {rbs wbs : List (Reg × Nat)} {s s' : State} {W : List Region} (L : Lay rbs wbs s)
    (hP : PostB s s' W) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) : Lay rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (hcs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · simp only [retR, e b hb, hP.rsp]; exact L.ret b hb

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (toR s) ++ [below (s.gpr .rsp) 32], Region.Disjoint ⟨pa s p, l⟩ r := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

omit L in
theorem keepB_cs (hc : keepB (rbs ++ wbs) ws p l = true) : p.1 ∈ bases := by
  simp only [keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

theorem Lay.keepBytes (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (pa s' p) l = bytesAt s.mem (pa s p) l := by
  rw [hP.pa (keepB_cs hc)]
  have hin : inB (rbs ++ wbs) p l = true := by
    simp only [keepB, Bool.and_eq_true] at hc; exact hc.1.2
  obtain ⟨n, hn, hl⟩ := inB_spec hin
  exact bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : Poly} (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : PolyIs s.mem (pa s p) f) : PolyIs s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_cs hc)]
  exact polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepRed (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Reduced s.mem (pa s p)) : Reduced s'.mem (pa s' p) := by
  rw [hP.pa (keepB_cs hc)]
  exact reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepW (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (pa s' p) 64 = s.mem.readW (pa s p) 64 := by
  rw [hP.pa (keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

theorem ret_below32 (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 32) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hin : ∀ w ∈ ws, inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨n, hn, hsub⟩ := L.sub (hin w hw)
    exact (L.ret _ hn).sub_right hsub
  · rw [List.mem_singleton] at hr; subst hr
    exact ret_below32 _

end VG.Proof.MlKem.X86_64
