import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlDsa.Sign.Mem

/-!
# ML-DSA signing on x86-64: the buffers of the function

The function keeps the address of each buffer it works in (its arguments and
its working space) in a callee-saved register; a layout (`Lay`) lists these
registers with the lengths of their buffers, which are apart from each other
and from the `D` bytes of stack below `rsp` that the calls use. A pointer (a
register and an offset) into a buffer, and two pointers into the same buffer
or different ones, are then checked by evaluation (`inB`, `sepB`): each pair
of regions a call needs apart is, and each region is readable or writable
(`Lay.disj`, `Lay.stkD`, `Lay.cR`, `Lay.cW`). A call leaves the layout as it
was (`Lay.post`), and the bytes of a region apart from those it writes
(`Lay.keepBytes`, `Lay.keepPoly`).

(As ML-KEM's `Proof/MlKem/X86_64/Lay.lean`, with the stack below `rsp` a
parameter: the primitives' own calls may nest.)
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the function writes (`scratch` and `sig`):
a buffer it only reads may overlap another such buffer, but not one of
these. -/
abbrev wRegs : List Reg := [.rbx, .r14]

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

theorem contains_offset' {base : Addr} {off len n : Nat} (h : off + len ≤ n) (hn : n < 2 ^ 64) :
    (⟨base, n⟩ : Region).Contains (base + BitVec.ofNat 64 off) len := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem sub_offset' {base : Addr} {off len n : Nat} (h : off + len ≤ n) (hn : n < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, n⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - (base + BitVec.ofNat 64 off)).toNat + off) (2 ^ 64)
  omega

theorem off_disj {base : Addr} {a b la lb : Nat} (h : a + la ≤ b) (hb : b + lb < 2 ^ 64) :
    Region.Disjoint ⟨base + BitVec.ofNat 64 a, la⟩ ⟨base + BitVec.ofNat 64 b, lb⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have e : x - (base + BitVec.ofNat 64 a) = (x - (base + BitVec.ofNat 64 b)) + BitVec.ofNat 64 (b - a) := by
    rw [show BitVec.ofNat 64 (b - a) = BitVec.ofNat 64 b - BitVec.ofNat 64 a by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega]
    bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b - a) (by omega),
    Nat.mod_eq_of_lt (by omega)] at h₁
  omega

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

theorem covers_wr {rs : List Region} {s : State} (h : Covers rs s.wr) : Covers rs (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Layouts -/

section
variable (D : Nat)

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other, from the return address and
from the `D` bytes of stack below `rsp`, not wrapping around, and
permitted; and `D` bytes of stack below `rsp` that do not wrap around. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ wRegs ∨ b'.1 ∈ wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) D).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (retR s).Disjoint ⟨s.gpr b.1, b.2⟩
  sp : D ≤ (s.gpr .rsp).toNat
  dsm : D < 2 ^ 32

end

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
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
    (below (s.gpr .rsp) D).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.retD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (retR s).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.ret _ hn).sub_right hsub

theorem Lay.nwp {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : (pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.iR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (pa s p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega)

theorem Lay.iW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : InRegions s.wr (pa s p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega)

theorem Lay.cR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : Covers [⟨pa s p, l⟩] (s.rd ++ s.wr) :=
  covers_one (L.iR h)

theorem Lay.cW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : Covers [⟨pa s p, l⟩] s.wr :=
  covers_one (L.iW h)

end

/-! ## What a piece of code leaves -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨pa s w.1, w.2⟩

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the `D` bytes of stack. -/
structure PostB (D : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) D]) s.mem s'.mem

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (D : Nat) (s s' : State) (ws : List (Ptr × Nat)) : Prop := PostB D s s' (ws.map (toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ bases) && inB bs p l && ws.all fun w => sepB bs p l w.1 w.2

theorem PostB.pa {D : Nat} {s s' : State} {W : List Region} (hP : PostB D s s' W) {p : Ptr} (h : p.1 ∈ bases) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, hP.bs _ h]

theorem PostB.refl (D : Nat) (s : State) (W : List Region) : PostB D s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.trans {D : Nat} {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : PostB D s s₁ W₁)
    (h₂ : PostB D s₁ s₂ W₂) (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : PostB D s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.rsp.trans h₁.rsp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

theorem map_toR_post {D : Nat} {s s' : State} {W : List Region} (hP : PostB D s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ bases) : ws.map (toR s') = ws.map (toR s) :=
  List.map_congr_left fun w hw => by simp only [toR, hP.pa (h w hw)]

/-- `PostB.trans`, with the regions written given as pointers. -/
theorem PPostB.trans {D : Nat} {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : PPostB D s s₁ ws₁)
    (h₂ : PPostB D s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ bases) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : PPostB D s s₂ ws := by
  have h₂' : PostB D s₁ s₂ (ws₂.map (toR s)) := by rw [← map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem Lay.post {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} {W : List Region} (L : Lay D rbs wbs s)
    (hP : PostB D s s' W) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) : Lay D rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (hcs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, ?_, ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · simp only [retR, e b hb, hP.rsp]; exact L.ret b hb
  · rw [hP.rsp]; exact L.sp
  · exact L.dsm

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (toR s) ++ [below (s.gpr .rsp) D], Region.Disjoint ⟨pa s p, l⟩ r := by
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

omit L in
theorem keepB_in (hc : keepB (rbs ++ wbs) ws p l = true) : inB (rbs ++ wbs) p l = true := by
  simp only [keepB, Bool.and_eq_true] at hc; exact hc.1.2

theorem Lay.keepBytes (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (pa s' p) l = bytesAt s.mem (pa s p) l := by
  rw [hP.pa (keepB_cs hc)]
  obtain ⟨n, hn, hl⟩ := inB_spec (keepB_in hc)
  exact VG.Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : Poly} (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : PolyIs s.mem (pa s p) f) : PolyIs s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_cs hc)]
  exact polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepRed (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Reduced s.mem (pa s p)) : Reduced s'.mem (pa s' p) := by
  rw [hP.pa (keepB_cs hc)]
  exact reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true) :
    polyAt s'.mem (pa s' p) = polyAt s.mem (pa s p) := by
  rw [hP.pa (keepB_cs hc)]
  exact polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepW (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (pa s' p) 64 = s.mem.readW (pa s p) 64 := by
  rw [hP.pa (keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hin : ∀ w ∈ ws, inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨n, hn, hsub⟩ := L.sub (hin w hw)
    exact (L.ret _ hn).sub_right hsub
  · rw [List.mem_singleton] at hr; subst hr
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := L.sp
    have := L.dsm
    bv_omega

/-! ## Two runs in the same layout -/

/-- Two states in the same layout, with the same stack pointer. -/
structure LRel (D : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop where
  lx : Lay D rbs wbs x
  ly : Lay D rbs wbs y
  regs : ∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1
  rsp : x.gpr .rsp = y.gpr .rsp

theorem LRel.eq {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel D rbs wbs x y) {p : Ptr} {l : Nat}
    (hp : inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := inB_spec hp
  exact h.regs (p.1, n) hn

theorem LRel.pa {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel D rbs wbs x y) {p : Ptr} {l : Nat}
    (hp : inB (rbs ++ wbs) p l = true) : pa x p = pa y p := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, h.eq hp]

theorem LRel.post {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : LRel D rbs wbs x y) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hx : PostB D x x' W₁) (hy : PostB D y y' W₂) :
    LRel D rbs wbs x' y' :=
  ⟨h.lx.post hx hcs, h.ly.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb), h.regs b hb],
    by rw [hx.rsp, hy.rsp, h.rsp]⟩

end VG.Proof.MlDsa.X86_64.Sign
