import VerifiedGarbage.Proof.MlKem.X86_64.Lay

/-!
# ML-KEM-768 on x86-64: the calls, in a layout

Untrusted: everything here is checked by Lean. What each call of the
top-level functions needs (`IpH`, `MulH`, …) from a layout (`Lay`) and a
check of its pointers that evaluates to `true` (`ipChk`, `mulChk`, …), and
two runs in the same layout (`LRel`), with the same addresses in its
registers, which every call keeps.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt rates)

/-! ## Checks -/

/-- A pointer an argument is moved from: its offset fits an immediate, and its bytes are readable. -/
def rdOk (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) : Bool := decide (p.2 < 2 ^ 31) && inB bs p l

/-- A pointer to bytes that a call writes. -/
def wrOk (bs wbs : List (Reg × Nat)) (p : Ptr) (l : Nat) : Bool := rdOk bs p l && inB wbs p l

def ipChk (bs wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  wrOk bs wbs f 1024 && wrOk bs wbs (sc oSS) 1024 && sepB bs f 1024 (sc oSS) 1024

def accChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  wrOk bs wbs f 1024 && rdOk bs g 1024 && sepB bs f 1024 g 1024

def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  wrOk bs wbs h 1024 && rdOk bs f 1024 && rdOk bs g 1024 && wrOk bs wbs (sc oSS) 1024 &&
    sepB bs h 1024 f 1024 && sepB bs h 1024 g 1024 && sepB bs h 1024 (sc oSS) 1024 &&
    sepB bs f 1024 (sc oSS) 1024 && sepB bs g 1024 (sc oSS) 1024

def twoChk (bs wbs : List (Reg × Nat)) (p : Ptr) (n : Nat) (q : Ptr) (m : Nat) : Bool :=
  rdOk bs p n && wrOk bs wbs q m && sepB bs p n q m

def sampChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  rdOk bs (sc oSB) 34 && wrOk bs wbs a 1024 && wrOk bs wbs (sc oSS) 2048 && sepB bs (sc oSB) 34 a 1024 &&
    sepB bs (sc oSB) 34 (sc oSS) 2048 && sepB bs a 1024 (sc oSS) 2048

/-- The Keccak state and the sponge functions' working space. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  wrOk bs wbs (sc 0) 200 && wrOk bs wbs (sc 200) 640 && sepB bs (sc 0) 200 (sc 200) 640

def kabsChk (bs wbs : List (Reg × Nat)) (src : Ptr) (len : Nat) : Bool :=
  kChk bs wbs && rdOk bs src len && decide (len < 2 ^ 31) && sepB bs src len (sc 0) 200 &&
    sepB bs src len (sc 200) 640

def ksqzChk (bs wbs : List (Reg × Nat)) (dst : Ptr) (len : Nat) : Bool :=
  kChk bs wbs && wrOk bs wbs dst len && decide (len < 2 ^ 31) && sepB bs (sc 0) 200 dst len &&
    sepB bs dst len (sc 200) 640

/-! ## What the calls need -/

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s)
include L

theorem IpH.of {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true) (red : Reduced s.mem (pa s f)) : IpH f s := by
  simp only [ipChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ho, hr⟩, hw⟩, ⟨_, hr2⟩, hw2⟩, hs⟩ := hc
  exact ⟨ho, red, L.disj hs, L.stkD hr, L.stkD hr2, covers_cons (L.cW hw) (covers_cons (L.cW hw2) covers_nil)⟩

theorem AccH.of {f g : Ptr} (hc : accChk (rbs ++ wbs) wbs f g = true) (redF : Reduced s.mem (pa s f))
    (redG : Reduced s.mem (pa s g)) : AccH f g s := by
  simp only [accChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ho, hr⟩, hw⟩, ho2, hr2⟩, hs⟩ := hc
  exact ⟨⟨ho, ho2⟩, redF, redG, L.disj hs, L.stkD hr, L.stkD hr2,
    covers_append (covers_cons (L.cR hr2) covers_nil) (covers_cons (L.cR hr) covers_nil),
    covers_cons (L.cW hw) covers_nil⟩

theorem MulH.of {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) (redF : Reduced s.mem (pa s f))
    (redG : Reduced s.mem (pa s g)) : MulH h f g s := by
  simp only [mulChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hoh, hrh⟩, hwh⟩, hof, hrf⟩, hog, hrg⟩, ⟨_, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩ := hc
  exact ⟨⟨hoh, hof, hog⟩, redF, redG, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5, L.stkD hrh,
    L.stkD hrf, L.stkD hrg, L.stkD hrz,
    covers_append (covers_cons (L.cR hrf) (covers_cons (L.cR hrg) covers_nil))
      (covers_cons (L.cR hrh) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwh) (covers_cons (L.cW hwz) covers_nil)⟩

theorem TwoH.of {p q : Ptr} {n m : Nat} (hc : twoChk (rbs ++ wbs) wbs p n q m = true) : TwoH p q n m s := by
  simp only [twoChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hop, hrp⟩, ⟨hoq, hrq⟩, hwq⟩, hs⟩ := hc
  exact ⟨⟨hop, hoq⟩, L.disj hs, L.stkD hrp, L.stkD hrq,
    covers_append (covers_cons (L.cR hrp) covers_nil) (covers_cons (L.cR hrq) covers_nil),
    covers_cons (L.cW hwq) covers_nil⟩

theorem CEH.of {f out : Ptr} {d : Nat} (hc : twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true)
    (hd : d ∈ compressWidths) (red : Reduced s.mem (pa s f)) : CEH f out d s :=
  have h := TwoH.of L hc
  ⟨h.off, hd, red, h.d, h.kP, h.kQ, h.c, h.w⟩

theorem DDH.of {b f : Ptr} {d : Nat} (hc : twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true)
    (hd : d ∈ compressWidths) : DDH b f d s :=
  have h := TwoH.of L hc
  ⟨h.off, hd, h.d, h.kP, h.kQ, h.c, h.w⟩

theorem SampH.of {a : Ptr} (hc : sampChk (rbs ++ wbs) wbs a = true) : SampH a s := by
  simp only [sampChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨_, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hrz,
    covers_append (covers_cons (L.cR hrs) covers_nil) (covers_cons (L.cR hra) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwa) (covers_cons (L.cW hwz) covers_nil)⟩

theorem kChk_spec (hc : kChk (rbs ++ wbs) wbs = true) :
    Region.Disjoint ⟨pa s (sc 0), 200⟩ ⟨pa s (sc 200), 640⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 200⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 200), 640⟩ ∧
    Covers [⟨pa s (sc 0), 200⟩] (s.rd ++ s.wr) ∧ Covers [⟨pa s (sc 200), 640⟩] (s.rd ++ s.wr) ∧
    Covers [⟨pa s (sc 0), 200⟩] s.wr ∧ Covers [⟨pa s (sc 200), 640⟩] s.wr := by
  simp only [kChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_, h1⟩, w1⟩, ⟨_, h2⟩, w2⟩, hs⟩ := hc
  exact ⟨L.disj hs, L.stkD h1, L.stkD h2, L.cR h1, L.cR h2, L.cW w1, L.cW w2⟩

theorem KAbsH.of {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) wbs src len = true)
    (hrate : rate ∈ rates) (hpos : pos < rate) : KAbsH src len rate pos s := by
  simp only [kabsChk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hk, ho, hr⟩, hl⟩, s1⟩, s2⟩ := hc
  obtain ⟨d0, k0, k1, c0, c1, w0, w1⟩ := kChk_spec L hk
  exact ⟨ho, hl, hrate, hpos, d0, L.disj s1, L.disj s2, k0, L.stkD hr, k1,
    covers_append (covers_cons (L.cR hr) covers_nil) (covers_cons c0 (covers_cons c1 covers_nil)),
    covers_cons w0 (covers_cons w1 covers_nil)⟩

theorem KPadH.of {rate pos : Nat} (hc : kChk (rbs ++ wbs) wbs = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    KPadH rate pos s := by
  obtain ⟨d0, k0, k1, _, _, w0, w1⟩ := kChk_spec L hc
  exact ⟨hrate, hpos, d0, k0, k1, covers_cons w0 (covers_cons w1 covers_nil)⟩

theorem KSqzH.of {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    KSqzH dst len rate s := by
  simp only [ksqzChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hk, ⟨ho, hr⟩, hw⟩, hl⟩, s1⟩, s2⟩ := hc
  obtain ⟨d0, k0, k1, _, _, w0, w1⟩ := kChk_spec L hk
  exact ⟨ho, hl, hrate, L.disj s1, d0, L.disj s2, k0, L.stkD hr, k1,
    covers_cons w0 (covers_cons (L.cW hw) (covers_cons w1 covers_nil))⟩

end

/-! ## Two runs in a layout -/

/-- Two states in the layout, with the same addresses in its registers and the same stack pointer. -/
def LRel (rbs wbs : List (Reg × Nat)) (x y : State) : Prop :=
  Lay rbs wbs x ∧ Lay rbs wbs y ∧ (∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1) ∧ x.gpr .rsp = y.gpr .rsp

theorem LRel.eq {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel rbs wbs x y) {p : Ptr} {l : Nat}
    (hin : inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := inB_spec hin
  exact h.2.2.1 (p.1, n) hn

theorem LRel.pa {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel rbs wbs x y) {p : Ptr} {l : Nat}
    (hin : inB (rbs ++ wbs) p l = true) : pa x p = pa y p := by
  simp only [VG.Proof.MlKem.X86_64.pa, h.eq hin]

theorem LRel.post {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region} (h : LRel rbs wbs x y)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hx : PostB x x' W₁) (hy : PostB y y' W₂) : LRel rbs wbs x' y' :=
  ⟨h.1.post hx hcs, h.2.1.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb)]; exact h.2.2.1 b hb,
    by rw [hx.rsp, hy.rsp]; exact h.2.2.2⟩

end VG.Proof.MlKem.X86_64
