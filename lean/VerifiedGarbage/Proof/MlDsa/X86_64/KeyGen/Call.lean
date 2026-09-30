import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly

/-!
# ML-DSA key generation on x86-64: calling the primitives

Untrusted: everything here is checked by Lean. A call of a primitive
(`primOk`, `primTr`), with the moves of its arguments (`glue3_ok`, …): the
callee's precondition on entry, from the layout (`ceD1`, `ceD2`, `ceWf`
for the stack, and the memory of the callee's entry, `ce_polyAt`, …), and
what its postcondition says once it returns.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc oSS lea)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## The stack of a call -/

section
variable {p : Params} {s s1 : State} (L : Lay kgR (kgW p) s) (hsp : s1.gpr .rsp = s.gpr .rsp)
include L hsp

theorem ceD1 {q : Ptr} {l : Nat} (h : inB (kgB p) q l = true) :
    Region.Disjoint ⟨s1.gpr .rsp - 8, 8⟩ ⟨pa s q, l⟩ := by
  have := ret_disj s1 (R := ⟨pa s q, l⟩) (by rw [hsp]; exact L.stkD h)
  simpa [retR] using this

theorem ceD2 {n : Nat} (hn : n + 1 ≤ 16) {q : Ptr} {l : Nat} (h : inB (kgB p) q l = true) :
    Region.Disjoint ⟨s1.gpr .rsp - 8 - BitVec.ofNat 64 (n + 1), n + 1⟩ ⟨pa s q, l⟩ := by
  have := stk_disj s1 (R := ⟨pa s q, l⟩) (by rw [hsp]; exact L.stkD h)
  simp only [State.callEntry_rsp] at this
  exact this.sub_left (below_sub hn (by omega))

omit L in
theorem ceWf (h24 : 24 ≤ (s.gpr .rsp).toNat) {n : Nat} (hn : n + 1 ≤ 16) : n + 1 ≤ (s1.gpr .rsp - 8).toNat := by
  rw [hsp, BitVec.toNat_sub]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  have := (s.gpr .rsp).isLt
  omega

end

/-! ## The memory of a call's entry -/

section
variable {s1 : State}

/-- The memory a callee starts with. -/
abbrev ceM (s1 : State) : Mem := s1.mem.writeW (s1.gpr .rsp - 8) (s1.unknowns 0)

theorem ceM_bytes {q : Addr} (h : (below (s1.gpr .rsp) 24).Disjoint ⟨q, 1024⟩) :
    ∀ k < 1024, ceM s1 (q + BitVec.ofNat 64 k) = s1.mem (q + BitVec.ofNat 64 k) :=
  fun _ hk => callEntry_bytes s1 (R := ⟨q, 1024⟩) (k16 s1 h) (show 1024 ≤ 2 ^ 64 by decide) hk

theorem ce_polyAt {q : Addr} (h : (below (s1.gpr .rsp) 24).Disjoint ⟨q, 1024⟩) :
    Spec.MlDsa.polyAt (ceM s1) q = Spec.MlDsa.polyAt s1.mem q := Proof.MlDsa.KeyGen.polyAt_congr (ceM_bytes h)

theorem ce_natPolyAt {q : Addr} (h : (below (s1.gpr .rsp) 24).Disjoint ⟨q, 1024⟩) :
    Spec.MlDsa.natPolyAt (ceM s1) q = Spec.MlDsa.natPolyAt s1.mem q := Proof.MlDsa.KeyGen.natPolyAt_congr (ceM_bytes h)

theorem ce_coeffAt {q : Addr} (h : (below (s1.gpr .rsp) 24).Disjoint ⟨q, 1024⟩) {i : Nat} (hi : i < 256) :
    Spec.MlDsa.coeffAt (ceM s1) q i = Spec.MlDsa.coeffAt s1.mem q i :=
  Proof.MlDsa.KeyGen.coeffAt_congr (ceM_bytes h) hi

theorem ce_reduced {q : Addr} (h : (below (s1.gpr .rsp) 24).Disjoint ⟨q, 1024⟩) :
    Spec.MlDsa.Reduced (ceM s1) q ↔ Spec.MlDsa.Reduced s1.mem q :=
  ⟨Proof.MlDsa.KeyGen.reduced_congr fun k hk => (ceM_bytes h k hk).symm,
    Proof.MlDsa.KeyGen.reduced_congr (ceM_bytes h)⟩

theorem ce_bytesAt' {q : Addr} {n : Nat} (hn : n < 2 ^ 64) (h : (below (s1.gpr .rsp) 24).Disjoint ⟨q, n⟩) :
    bytesAt (ceM s1) q n = bytesAt s1.mem q n := callEntry_bytesAt s1 hn (k16 s1 h)

end

/-! ## A call -/

/-- A call of a primitive, from the moves of its arguments (`V`), its
precondition on entry and the regions it may read and write. -/
theorem primOk {c : Prog isa} {kk : Nat → Contract isa} (hc : Callee c kk) {glue : List Instr} {n : String}
    (hgl : ∀ i ∈ glue, loadsMxcsr i = false) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1)
    {rd wr : List Region} (hpre : ∀ stk ≤ 16, ∀ s1, V s1 → s1.mem = s.mem → Keep MlKem.X86_64.argRegs s s1 →
      (kk stk).pre (s1.callEntry.withRegions rd wr))
    (hcov : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => Post s s' wr ∧ MX s' = MX s ∧
      ∃ stk, stk ≤ 16 ∧ ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep MlKem.X86_64.argRegs s s1 ∧
        ∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
          (kk stk).post (s1.callEntry.withRegions rd wr) s₂ := by
  obtain ⟨stk, hs, hver⟩ := hc.verified
  exact WP.mono (glueCallMx_ok hver.1 hc.nosp hc.depth hgl hg (hpre stk hs) hcov hw)
    fun s' ⟨h1, h2, h3⟩ => ⟨h1, h2, stk, hs, h3⟩

/-- A block of moves leaks nothing. -/
theorem moves_tr {glue : List Instr} (h : ∀ i ∈ glue, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block glue) fun _ _ => True := block_nomem_tr h

/-- Two calls of a primitive leak the same, if their preconditions and public data do. -/
theorem primTr {c : Prog isa} {kk : Nat → Contract isa} (hc : Callee c kk) {glue : List Instr} {n : String}
    (hnm : ∀ i ∈ glue, ∀ s, isa.addrs i s = []) {P : State → State → Prop} {V : State → State → Prop}
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ stk ≤ 16, ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      (kk stk).pre (x1.callEntry.withRegions rd₁ wr₁) ∧ (kk stk).pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      (kk stk).pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c)) fun _ _ => True := by
  obtain ⟨stk, hs, hver⟩ := hc.verified
  exact glueCall_tr hver.1 hver.2.1 (moves_tr hnm) hg (hP stk hs)

/-! ## The moves of the arguments -/

/-- `d ← v`, a 32-bit immediate. -/
theorem imm_eq {v : Nat} (h : v < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v :=
  sw_ofNat h

theorem lea_noLd (d : Reg) (q : Ptr) : ∀ i ∈ lea d q, loadsMxcsr i = false := by
  intro i hi; simp only [lea, List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl

theorem imm_noLd (d : Reg) (v : Nat) : ∀ i ∈ imm d v, loadsMxcsr i = false := by
  intro i hi; simp only [imm, List.mem_singleton] at hi; subst hi; rfl

theorem imm_nomem (d : Reg) (v : Nat) : ∀ i ∈ imm d v, ∀ s, isa.addrs i s = [] := by
  intro i hi s; simp only [imm, List.mem_singleton] at hi; subst hi; rfl

theorem noLd_append {a b : List Instr} (ha : ∀ i ∈ a, loadsMxcsr i = false) (hb : ∀ i ∈ b, loadsMxcsr i = false) :
    ∀ i ∈ a ++ b, loadsMxcsr i = false := fun i hi => by
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h, hb i h]

/-- A pointer whose register no move of arguments writes. -/
structure PtrOk (q : Ptr) : Prop where
  off : q.2 < 2 ^ 31
  na : q.1 ∉ MlKem.X86_64.argRegs

theorem PtrOk.ne {q : Ptr} (h : PtrOk q) {r : Reg} (hr : r ∈ MlKem.X86_64.argRegs) : q.1 ≠ r :=
  fun e => h.na (e ▸ hr)

theorem glue2_ok {a b : Ptr} (ha : PtrOk a) (hb : PtrOk b) (s : State) :
    WP isa (.block (lea .rdi a ++ lea .rsi b)) s fun s1 =>
      ((s1.gpr .rdi = pa s a ∧ s1.gpr .rsi = pa s b) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 :=
  accGlue_ok a b ha.off hb.off (hb.ne (by decide)) s

theorem glue3_ok {a b c : Ptr} (ha : PtrOk a) (hb : PtrOk b) (hc : PtrOk c) (s : State) :
    WP isa (.block (lea .rdi a ++ lea .rsi b ++ lea .rdx c)) s fun s1 =>
      ((s1.gpr .rdi = pa s a ∧ s1.gpr .rsi = pa s b ∧ s1.gpr .rdx = pa s c) ∧ s1.mem = s.mem) ∧
        Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ha.off, sx_ofNat hb.off, sx_ofNat hc.off, hb.ne (r := .rdi) (by decide),
    hc.ne (r := .rdi) (by decide), hc.ne (r := .rsi) (by decide), List.cons_append, List.nil_append]

end VG.Proof.MlDsa.X86_64.KeyGen

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc oSS lea)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem sc_ok (o : Nat) (h : o < 2 ^ 31) : PtrOk (sc o) := ⟨h, show Reg.rbx ∉ MlKem.X86_64.argRegs by decide⟩

/-- The region facts of a callee's precondition, from the layout. -/
syntax "cpre " term:max term:max term:max : tactic
macro_rules
  | `(tactic| cpre $L $hsp $h24) => `(tactic| (
      and_intros
      all_goals first
        | with_reducible exact True.intro
        | with_reducible exact ceWf $hsp $h24 (by omega)
        | with_reducible exact ceD1 $L $hsp (by with_reducible assumption)
        | with_reducible exact ceD2 $L $hsp (by omega) (by with_reducible assumption)
        | with_reducible exact Lay.disj $L (by with_reducible assumption)
        | with_reducible exact Lay.nwp $L (by with_reducible assumption)
        | skip))

theorem covers2 {s : State} {p : Params} (L : Lay kgR (kgW p) s) {a b : Ptr} {la lb : Nat}
    (ha : inB (kgW p) a la = true) (hb : inB (kgW p) b lb = true) :
    Covers [⟨pa s a, la⟩, ⟨pa s b, lb⟩] s.wr := covers_cons (L.cW ha) (covers_cons (L.cW hb) covers_nil)

/-- A state of the function, where a call can be made. -/
structure Site (p : Params) (s : State) : Prop where
  lay : Lay kgR (kgW p) s
  h24 : 24 ≤ (s.gpr .rsp).toNat

/-- Two such states with the same pointers and stack pointer. -/
structure Two (p : Params) (x y : State) : Prop where
  sx : Site p x
  sy : Site p y
  regs : ∀ r ∈ bases, x.gpr r = y.gpr r
  rsp : x.gpr .rsp = y.gpr .rsp

theorem Two.pa {p : Params} {x y : State} (h : Two p x y) {q : Ptr} (hq : q.1 ∈ bases) : pa x q = pa y q := by
  simp only [VG.Proof.MlKem.X86_64.pa, h.regs _ hq]

/-- The registers the moves of arguments write keep the stack pointer. -/
theorem keep_rsp {s s1 : State} (k : Keep MlKem.X86_64.argRegs s s1) : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)

theorem inB_mono {p : Params} {q : Ptr} {l : Nat} (h : inB (kgW p) q l = true) : inB (kgB p) q l = true := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  unfold inB
  rcases q with ⟨r, o⟩
  simp only [kgW, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact decide_eq_true hl

/-! ## `NTT` and `NTT⁻¹` -/

section
variable {p : Params} {f : Ptr} (hf : PtrOk f) (h1 : sepB (kgB p) f 1024 (sc oSS) 1024 = true)
  (w1 : inB (kgW p) f 1024 = true) (w2 : inB (kgW p) (sc oSS) 1024 = true)

include h1 in
theorem ip_pre {t : Spec.MlDsa.Poly → Spec.MlDsa.Poly} {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (red : Spec.MlDsa.Reduced s.mem (pa s f)) (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = pa s (sc oSS))
    (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.inPlaceContract X86_64.abi t stk).pre
      (s1.callEntry.withRegions [] [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2]
    cpre L hsp S.h24
    exact (ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ red)

include hf h1 w1 w2 in
theorem ipAt_ok {t : Spec.MlDsa.Poly → Spec.MlDsa.Poly} {c : Prog isa} {n : String}
    (hc : Callee c fun stk => Spec.MlDsa.inPlaceContract X86_64.abi t stk) {s : State} (S : Site p s)
    (red : Spec.MlDsa.Reduced s.mem (pa s f)) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call n c)) s fun s' =>
      Post s s' [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩] ∧ MX s' = MX s ∧
      Spec.MlDsa.PolyIs s'.mem (pa s f) (t (Spec.MlDsa.polyAt s.mem (pa s f))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (lea_noLd _ _) (lea_noLd _ _)) (glue2_ok hf (sc_ok oSS (by decide)) s)
    (fun stk hs s1 hv hm k => ip_pre h1 hs S red hv hm k) (covers_nil_wr (covers2 L w1 w2)) (covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hm₂] at hpost
  rwa [ce_polyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hf h1 w1 w2 in
theorem ipAt_tr {t : Spec.MlDsa.Poly → Spec.MlDsa.Poly} {c : Prog isa} {n : String}
    (hc : Callee c fun stk => Spec.MlDsa.inPlaceContract X86_64.abi t stk) (hb : f.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ Spec.MlDsa.Reduced x.mem (pa x f) ∧ Spec.MlDsa.Reduced y.mem (pa y f))
      (.seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call n c)) fun _ _ => True := by
  have g := fun s => glue2_ok hf (sc_ok oSS (by decide)) s
  refine primTr hc (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨[], _, [], _, ip_pre h1 hs T.sx rx hv1 hm1 k1, ip_pre h1 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_nil_wr (covers2 T.sx.lay w1 w2),
        by rw [k1.2.2]; exact covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact covers_nil_wr (covers2 T.sy.lay w1 w2),
        by rw [k2.2.2]; exact covers2 T.sy.lay w1 w2, by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2, hv2.1, hv2.2, keep_rsp k1, keep_rsp k2, T.rsp, T.pa hb, T.pa (q := sc oSS) (by decide),
    and_self]

end

/-! ## Addition -/

section
variable {p : Params} {f g : Ptr} (hf : PtrOk f) (hg : PtrOk g) (h1 : sepB (kgB p) f 1024 g 1024 = true)
  (w1 : inB (kgW p) f 1024 = true)

include h1 in
theorem add_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (rf : Spec.MlDsa.Reduced s.mem (pa s f)) (rg : Spec.MlDsa.Reduced s.mem (pa s g))
    (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = pa s g) (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.addContract X86_64.abi stk).pre (s1.callEntry.withRegions [⟨pa s g, 1024⟩] [⟨pa s f, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.addContract, Spec.MlDsa.accSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2]
    cpre L hsp S.h24
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ rf)
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i2)).mpr (hm ▸ rg)

theorem covers_rw {s : State} {p : Params} (L : Lay kgR (kgW p) s) {a b : Ptr} {la lb : Nat}
    (ha : inB (kgB p) a la = true) (hb : inB (kgW p) b lb = true) :
    Covers ([⟨pa s a, la⟩] ++ [⟨pa s b, lb⟩]) (s.rd ++ s.wr) :=
  covers_append (covers_cons (L.cR ha) covers_nil) (covers_cons (L.cR (inB_mono hb)) covers_nil)

include hf hg h1 w1 in
theorem addAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.addContract X86_64.abi stk) {s : State}
    (S : Site p s) (rf : Spec.MlDsa.Reduced s.mem (pa s f)) (rg : Spec.MlDsa.Reduced s.mem (pa s g)) :
    WP isa (addAt c f g) s fun s' => Post s s' [⟨pa s f, 1024⟩] ∧ MX s' = MX s ∧
      Spec.MlDsa.PolyIs s'.mem (pa s f) (Spec.MlDsa.add (Spec.MlDsa.polyAt s.mem (pa s f))
        (Spec.MlDsa.polyAt s.mem (pa s g))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (lea_noLd _ _) (lea_noLd _ _)) (glue2_ok hf hg s)
    (fun stk hs s1 hv hm k => add_pre h1 hs S rf rg hv hm k) (covers_rw L i2 w1)
    (covers_cons (L.cW w1) covers_nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.addContract, Spec.MlDsa.accSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2, hm₂] at hpost
  rwa [ce_polyAt (by rw [hsp]; exact L.stkD i1), ce_polyAt (by rw [hsp]; exact L.stkD i2), hm] at hpost

include hf hg h1 w1 in
theorem addAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.addContract X86_64.abi stk)
    (hbf : f.1 ∈ bases) (hbg : g.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ (Spec.MlDsa.Reduced x.mem (pa x f) ∧ Spec.MlDsa.Reduced x.mem (pa x g)) ∧
      (Spec.MlDsa.Reduced y.mem (pa y f) ∧ Spec.MlDsa.Reduced y.mem (pa y g))) (addAt c f g) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  refine primTr hc (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (fun x y _ => ⟨glue2_ok hf hg x, glue2_ok hf hg y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, add_pre h1 hs T.sx rx.1 rx.2 hv1 hm1 k1, add_pre h1 hs T.sy ry.1 ry.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rw T.sx.lay i2 w1,
        by rw [k1.2.2]; exact covers_cons (T.sx.lay.cW w1) covers_nil,
        by rw [k2.2.1, k2.2.2]; exact covers_rw T.sy.lay i2 w1,
        by rw [k2.2.2]; exact covers_cons (T.sy.lay.cW w1) covers_nil, by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.addContract, Spec.MlDsa.accSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2, hv2.1, hv2.2, keep_rsp k1, keep_rsp k2, T.rsp, T.pa hbf, T.pa hbg, and_self]

end

/-! ## `MultiplyNTT` -/

section
variable {p : Params} {h f g : Ptr} (hh : PtrOk h) (hf : PtrOk f) (hg : PtrOk g)
  (h1 : sepB (kgB p) h 1024 f 1024 = true) (h2 : sepB (kgB p) h 1024 g 1024 = true)
  (w1 : inB (kgW p) h 1024 = true)

theorem covers_rrw {s : State} {p : Params} (L : Lay kgR (kgW p) s) {a b c : Ptr} {la lb lc : Nat}
    (ha : inB (kgB p) a la = true) (hb : inB (kgB p) b lb = true) (hc : inB (kgW p) c lc = true) :
    Covers ([⟨pa s a, la⟩, ⟨pa s b, lb⟩] ++ [⟨pa s c, lc⟩]) (s.rd ++ s.wr) :=
  covers_append (covers_cons (L.cR ha) (covers_cons (L.cR hb) covers_nil)) (covers_cons (L.cR (inB_mono hc)) covers_nil)

include h1 h2 in
theorem mul_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (rf : Spec.MlDsa.Reduced s.mem (pa s f)) (rg : Spec.MlDsa.Reduced s.mem (pa s g))
    (hv : s1.gpr .rdi = pa s h ∧ s1.gpr .rsi = pa s f ∧ s1.gpr .rdx = pa s g) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.mulContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i2)).mpr (hm ▸ rf)
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i3)).mpr (hm ▸ rg)

include hh hf hg h1 h2 w1 in
theorem mulAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.mulContract X86_64.abi stk) {s : State}
    (S : Site p s) (rf : Spec.MlDsa.Reduced s.mem (pa s f)) (rg : Spec.MlDsa.Reduced s.mem (pa s g)) :
    WP isa (mulAt c h f g) s fun s' => Post s s' [⟨pa s h, 1024⟩] ∧ MX s' = MX s ∧
      Spec.MlDsa.PolyIs s'.mem (pa s h) (Spec.MlDsa.multiplyNTT (Spec.MlDsa.polyAt s.mem (pa s f)) (Spec.MlDsa.polyAt s.mem (pa s g))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (lea_noLd _ _) (lea_noLd _ _)) (lea_noLd _ _))
    (glue3_ok hh hf hg s) (fun stk hs s1 hv hm k => mul_pre h1 h2 hs S rf rg hv hm k) (covers_rrw L i2 i3 w1)
    (covers_cons (L.cW w1) covers_nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2, hm₂] at hpost
  rwa [ce_polyAt (by rw [hsp]; exact L.stkD i2), ce_polyAt (by rw [hsp]; exact L.stkD i3), hm] at hpost

include hh hf hg h1 h2 w1 in
theorem mulAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.mulContract X86_64.abi stk)
    (hbh : h.1 ∈ bases) (hbf : f.1 ∈ bases) (hbg : g.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ (Spec.MlDsa.Reduced x.mem (pa x f) ∧ Spec.MlDsa.Reduced x.mem (pa x g)) ∧ (Spec.MlDsa.Reduced y.mem (pa y f) ∧ Spec.MlDsa.Reduced y.mem (pa y g))) (mulAt c h f g) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  refine primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨glue3_ok hh hf hg x, glue3_ok hh hf hg y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, mul_pre h1 h2 hs T.sx rx.1 rx.2 hv1 hm1 k1, mul_pre h1 h2 hs T.sy ry.1 ry.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rrw T.sx.lay i2 i3 w1,
        by rw [k1.2.2]; exact covers_cons (T.sx.lay.cW w1) covers_nil,
        by rw [k2.2.1, k2.2.2]; exact covers_rrw T.sy.lay i2 i3 w1,
        by rw [k2.2.2]; exact covers_cons (T.sy.lay.cW w1) covers_nil, by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, keep_rsp k1, keep_rsp k2, T.rsp, T.pa hbh, T.pa hbf,
    T.pa hbg, and_self]

end

/-! ## `AddNTT(h, MultiplyNTT(f, g))` -/

section
variable {p : Params} {h f g : Ptr} (hh : PtrOk h) (hf : PtrOk f) (hg : PtrOk g)
  (h1 : sepB (kgB p) h 1024 f 1024 = true) (h2 : sepB (kgB p) h 1024 g 1024 = true)
  (w1 : inB (kgW p) h 1024 = true)

include h1 h2 in
theorem mulAdd_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (rh : Spec.MlDsa.Reduced s.mem (pa s h)) (rf : Spec.MlDsa.Reduced s.mem (pa s f)) (rg : Spec.MlDsa.Reduced s.mem (pa s g))
    (hv : s1.gpr .rdi = pa s h ∧ s1.gpr .rsi = pa s f ∧ s1.gpr .rdx = pa s g) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.mulAddContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ rh)
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i2)).mpr (hm ▸ rf)
    · exact (ce_reduced (by rw [hsp]; exact L.stkD i3)).mpr (hm ▸ rg)

include hh hf hg h1 h2 w1 in
theorem mulAddAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.mulAddContract X86_64.abi stk) {s : State}
    (S : Site p s) (rh : Spec.MlDsa.Reduced s.mem (pa s h)) (rf : Spec.MlDsa.Reduced s.mem (pa s f)) (rg : Spec.MlDsa.Reduced s.mem (pa s g)) :
    WP isa (mulAddAt c h f g) s fun s' => Post s s' [⟨pa s h, 1024⟩] ∧ MX s' = MX s ∧
      Spec.MlDsa.PolyIs s'.mem (pa s h) (Spec.MlDsa.add (Spec.MlDsa.polyAt s.mem (pa s h)) (Spec.MlDsa.multiplyNTT (Spec.MlDsa.polyAt s.mem (pa s f)) (Spec.MlDsa.polyAt s.mem (pa s g)))) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (lea_noLd _ _) (lea_noLd _ _)) (lea_noLd _ _))
    (glue3_ok hh hf hg s) (fun stk hs s1 hv hm k => mulAdd_pre h1 h2 hs S rh rf rg hv hm k) (covers_rrw L i2 i3 w1)
    (covers_cons (L.cW w1) covers_nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2, hm₂] at hpost
  rwa [ce_polyAt (by rw [hsp]; exact L.stkD i1), ce_polyAt (by rw [hsp]; exact L.stkD i2), ce_polyAt (by rw [hsp]; exact L.stkD i3), hm] at hpost

include hh hf hg h1 h2 w1 in
theorem mulAddAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.mulAddContract X86_64.abi stk)
    (hbh : h.1 ∈ bases) (hbf : f.1 ∈ bases) (hbg : g.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ (Spec.MlDsa.Reduced x.mem (pa x h) ∧ Spec.MlDsa.Reduced x.mem (pa x f) ∧ Spec.MlDsa.Reduced x.mem (pa x g)) ∧ (Spec.MlDsa.Reduced y.mem (pa y h) ∧ Spec.MlDsa.Reduced y.mem (pa y f) ∧ Spec.MlDsa.Reduced y.mem (pa y g))) (mulAddAt c h f g) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  refine primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨glue3_ok hh hf hg x, glue3_ok hh hf hg y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, mulAdd_pre h1 h2 hs T.sx rx.1 rx.2.1 rx.2.2 hv1 hm1 k1, mulAdd_pre h1 h2 hs T.sy ry.1 ry.2.1 ry.2.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rrw T.sx.lay i2 i3 w1,
        by rw [k1.2.2]; exact covers_cons (T.sx.lay.cW w1) covers_nil,
        by rw [k2.2.1, k2.2.2]; exact covers_rrw T.sy.lay i2 i3 w1,
        by rw [k2.2.2]; exact covers_cons (T.sy.lay.cW w1) covers_nil, by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, keep_rsp k1, keep_rsp k2, T.rsp, T.pa hbh, T.pa hbf,
    T.pa hbg, and_self]

end

/-! ## `Power2Round` -/

section
variable {p : Params} {t t1 t0 : Ptr} (ht : PtrOk t) (ht1 : PtrOk t1) (ht0 : PtrOk t0)
  (h1 : sepB (kgB p) t 1024 t1 1024 = true) (h2 : sepB (kgB p) t 1024 t0 1024 = true)
  (h3 : sepB (kgB p) t1 1024 t0 1024 = true)
  (w1 : inB (kgW p) t1 1024 = true) (w2 : inB (kgW p) t0 1024 = true)

theorem covers_rww {s : State} {p : Params} (L : Lay kgR (kgW p) s) {a b c : Ptr} {la lb lc : Nat}
    (ha : inB (kgB p) a la = true) (hb : inB (kgW p) b lb = true) (hc : inB (kgW p) c lc = true) :
    Covers ([⟨pa s a, la⟩] ++ [⟨pa s b, lb⟩, ⟨pa s c, lc⟩]) (s.rd ++ s.wr) :=
  covers_append (covers_cons (L.cR ha) covers_nil)
    (covers_cons (L.cR (inB_mono hb)) (covers_cons (L.cR (inB_mono hc)) covers_nil))

include h1 h2 h3 in
theorem p2r_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (rt : Spec.MlDsa.Reduced s.mem (pa s t))
    (hv : s1.gpr .rdi = pa s t ∧ s1.gpr .rsi = pa s t1 ∧ s1.gpr .rdx = pa s t0) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.power2RoundContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s t, 1024⟩] [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  obtain ⟨_, i3, _⟩ := sepB_spec h2
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24
    exact (ce_reduced (by rw [hsp]; exact L.stkD i1)).mpr (hm ▸ rt)

include ht ht1 ht0 h1 h2 h3 w1 w2 in
theorem p2rAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.power2RoundContract X86_64.abi stk)
    {s : State} (S : Site p s) (rt : Spec.MlDsa.Reduced s.mem (pa s t)) :
    WP isa (power2RoundAt c t t1 t0) s fun s' => Post s s' [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩] ∧ MX s' = MX s ∧
      Spec.MlDsa.NatPolyIs s'.mem (pa s t1)
        ((Spec.MlDsa.polyAt s.mem (pa s t)).map fun c => (Spec.MlDsa.power2Round c).1.toNat) ∧
      Spec.MlDsa.PolyIs s'.mem (pa s t0)
        ((Spec.MlDsa.polyAt s.mem (pa s t)).map fun c => Spec.MlDsa.ofInt (Spec.MlDsa.power2Round c).2) := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (lea_noLd _ _) (lea_noLd _ _)) (lea_noLd _ _))
    (glue3_ok ht ht1 ht0 s) (fun stk hs s1 hv hm k => p2r_pre h1 h2 h3 hs S rt hv hm k) (covers_rww L i1 w1 w2)
    (covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2, hm₂] at hpost
  rwa [ce_polyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include ht ht1 ht0 h1 h2 h3 w1 w2 in
theorem p2rAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.power2RoundContract X86_64.abi stk)
    (hbt : t.1 ∈ bases) (hb1 : t1.1 ∈ bases) (hb0 : t0.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ Spec.MlDsa.Reduced x.mem (pa x t) ∧ Spec.MlDsa.Reduced y.mem (pa y t))
      (power2RoundAt c t t1 t0) fun _ _ => True := by
  obtain ⟨i1, i2, _⟩ := sepB_spec h1
  refine primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨glue3_ok ht ht1 ht0 x, glue3_ok ht ht1 ht0 y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, p2r_pre h1 h2 h3 hs T.sx rx hv1 hm1 k1, p2r_pre h1 h2 h3 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact covers2 T.sy.lay w1 w2,
        by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, keep_rsp k1, keep_rsp k2, T.rsp, T.pa hbt, T.pa hb1,
    T.pa hb0, and_self]

end

/-! ## `RejNTTPoly` -/

section
variable {p : Params} {sd a : Ptr} (hsd : PtrOk sd) (ha : PtrOk a)
  (h1 : sepB (kgB p) sd 34 a 1024 = true) (h2 : sepB (kgB p) sd 34 (sc oSS) 2048 = true)
  (h3 : sepB (kgB p) a 1024 (sc oSS) 2048 = true)
  (w1 : inB (kgW p) a 1024 = true) (w2 : inB (kgW p) (sc oSS) 2048 = true)

include h1 h2 h3 in
theorem rejNtt_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (hv : s1.gpr .rdi = pa s sd ∧ s1.gpr .rsi = pa s a ∧ s1.gpr .rdx = pa s (sc oSS)) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.rejNTTContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s sd, 34⟩] [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩]) := by
  obtain ⟨_, _, _⟩ := sepB_spec h1
  obtain ⟨_, _, _⟩ := sepB_spec h3
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2]
    cpre L hsp S.h24

include hsd ha h1 h2 h3 w1 w2 in
theorem rejNttAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.rejNTTContract X86_64.abi stk)
    {s : State} (S : Site p s) :
    WP isa (rejNttAt c sd a) s fun s' => Post s s' [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩] ∧ MX s' = MX s ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Spec.MlDsa.Reduced s'.mem (pa s a)) ∧
      Spec.MlDsa.Outcome (fun b => Spec.MlDsa.rejNTTPoly b.rejNTT (bytesAt s.mem (pa s sd) 34))
        ((s'.gpr .rax).setWidth 32) (Spec.MlDsa.polyAt s'.mem (pa s a)) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (lea_noLd _ _) (lea_noLd _ _)) (lea_noLd _ _))
    (glue3_ok hsd ha (sc_ok oSS (by decide)) s) (fun stk hs s1 hv _ k => rejNtt_pre h1 h2 h3 hs S hv k)
    (covers_rww L i1 w1 w2) (covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, hg₂, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hm₂, hg₂ .rax (by decide)] at hpost
  rwa [ce_bytesAt' (by decide) (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hsd ha h1 h2 h3 w1 w2 in
theorem rejNttAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.rejNTTContract X86_64.abi stk)
    (hbs : sd.1 ∈ bases) (hba : a.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ bytesAt x.mem (pa x sd) 34 = bytesAt y.mem (pa y sd) 34)
      (rejNttAt c sd a) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => glue3_ok hsd ha (sc_ok oSS (by decide)) x
  refine primTr hc (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, e⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, rejNtt_pre h1 h2 h3 hs T.sx hv1 k1, rejNtt_pre h1 h2 h3 hs T.sy hv2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact covers2 T.sy.lay w1 w2,
        by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2, T.pa hbs, T.pa hba, T.pa (q := sc oSS) (by decide),
    and_true]
  refine ⟨by rw [keep_rsp k1, keep_rsp k2, T.rsp], ?_⟩
  rw [T.pa hbs] at e
  rw [ce_bytesAt' (by decide) (by rw [keep_rsp k1, ← T.pa hbs]; exact T.sx.lay.stkD i1),
    ce_bytesAt' (by decide) (by rw [keep_rsp k2]; exact T.sy.lay.stkD i1), hm1, hm2, e]

end

/-! ## Moves with immediates -/

theorem w32_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem w64_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 64 v).toNat = v := by
  simp only [BitVec.toNat_ofNat]; omega

theorem glueRB_ok {a b c : Ptr} (v : Nat) (hv : v < 2 ^ 32) (ha : PtrOk a) (hb : PtrOk b) (hc : PtrOk c) (s : State) :
    WP isa (.block (lea .rdi a ++ imm .rsi v ++ lea .rdx b ++ lea .rcx c)) s fun s1 =>
      ((s1.gpr .rdi = pa s a ∧ s1.gpr .rsi = BitVec.ofNat 64 v ∧ s1.gpr .rdx = pa s b ∧ s1.gpr .rcx = pa s c) ∧
        s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea imm
  xrun [sx_ofNat ha.off, sx_ofNat hb.off, sx_ofNat hc.off, imm_eq hv, hb.ne (r := .rdi) (by decide),
    hb.ne (r := .rsi) (by decide), hc.ne (r := .rdi) (by decide), hc.ne (r := .rsi) (by decide),
    hc.ne (r := .rdx) (by decide), List.cons_append, List.nil_append]

theorem glueSB_ok {a b : Ptr} (v w : Nat) (hv : v < 2 ^ 32) (hw : w < 2 ^ 32) (ha : PtrOk a) (hb : PtrOk b) (s : State) :
    WP isa (.block (lea .rdi a ++ imm .rsi v ++ lea .rdx b ++ imm .rcx w)) s fun s1 =>
      ((s1.gpr .rdi = pa s a ∧ s1.gpr .rsi = BitVec.ofNat 64 v ∧ s1.gpr .rdx = pa s b ∧
        s1.gpr .rcx = BitVec.ofNat 64 w) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea imm
  xrun [sx_ofNat ha.off, sx_ofNat hb.off, imm_eq hv, imm_eq hw, hb.ne (r := .rdi) (by decide),
    hb.ne (r := .rsi) (by decide), List.cons_append, List.nil_append]

theorem glueBP_ok {a b : Ptr} (u v w : Nat) (hu : u < 2 ^ 32) (hv : v < 2 ^ 32) (hw : w < 2 ^ 32) (ha : PtrOk a)
    (hb : PtrOk b) (s : State) :
    WP isa (.block (lea .rdi a ++ imm .rsi u ++ imm .rdx v ++ lea .rcx b ++ imm .r8 w)) s fun s1 =>
      ((s1.gpr .rdi = pa s a ∧ s1.gpr .rsi = BitVec.ofNat 64 u ∧ s1.gpr .rdx = BitVec.ofNat 64 v ∧
        s1.gpr .rcx = pa s b ∧ s1.gpr .r8 = BitVec.ofNat 64 w) ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea imm
  xrun [sx_ofNat ha.off, sx_ofNat hb.off, imm_eq hu, imm_eq hv, imm_eq hw, hb.ne (r := .rdi) (by decide),
    hb.ne (r := .rsi) (by decide), hb.ne (r := .rdx) (by decide), List.cons_append, List.nil_append]

/-! ## `RejBoundedPoly` -/

section
variable {p : Params} {sd a : Ptr} {eta : Nat} (heta : eta = 2 ∨ eta = 4) (hsd : PtrOk sd) (ha : PtrOk a)
  (h1 : sepB (kgB p) sd 66 a 1024 = true) (h2 : sepB (kgB p) sd 66 (sc oSS) 2048 = true)
  (h3 : sepB (kgB p) a 1024 (sc oSS) 2048 = true)
  (w1 : inB (kgW p) a 1024 = true) (w2 : inB (kgW p) (sc oSS) 2048 = true)

theorem eta_lt (heta : eta = 2 ∨ eta = 4) : eta < 2 ^ 32 := by omega

include heta h1 h2 h3 in
theorem rejB_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (hv : s1.gpr .rdi = pa s sd ∧ s1.gpr .rsi = BitVec.ofNat 64 eta ∧ s1.gpr .rdx = pa s a ∧
      s1.gpr .rcx = pa s (sc oSS)) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.rejBoundedContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s sd, 66⟩] [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩]) := by
  obtain ⟨_, _, _⟩ := sepB_spec h1
  obtain ⟨_, _, _⟩ := sepB_spec h3
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, w32_toNat (eta_lt heta)]
    cpre L hsp S.h24
    exact heta

include heta hsd ha h1 h2 h3 w1 w2 in
theorem rejBAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.rejBoundedContract X86_64.abi stk)
    {s : State} (S : Site p s) :
    WP isa (rejBoundedAt c sd eta a) s fun s' => Post s s' [⟨pa s a, 1024⟩, ⟨pa s (sc oSS), 2048⟩] ∧ MX s' = MX s ∧
      ((s'.gpr .rax).setWidth 32 = 1 → Spec.MlDsa.Reduced s'.mem (pa s a)) ∧
      Spec.MlDsa.Outcome (fun b => (Spec.MlDsa.rejBoundedPoly eta b.rejBounded (bytesAt s.mem (pa s sd) 66)).map
        Spec.MlDsa.toRq) ((s'.gpr .rax).setWidth 32) (Spec.MlDsa.polyAt s'.mem (pa s a)) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (noLd_append (lea_noLd _ _) (imm_noLd _ _)) (lea_noLd _ _))
      (lea_noLd _ _))
    (glueRB_ok eta (eta_lt heta) hsd ha (sc_ok oSS (by decide)) s) (fun stk hs s1 hv _ k => rejB_pre heta h1 h2 h3 hs S hv k)
    (covers_rww L i1 w1 w2) (covers2 L w1 w2))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, hg₂, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2.1, hm₂, hg₂ .rax (by decide), w32_toNat (eta_lt heta)] at hpost
  rwa [ce_bytesAt' (by decide) (by rw [hsp]; exact L.stkD i1), hm] at hpost

include heta hsd ha h1 h2 h3 w1 w2 in
theorem rejBAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.rejBoundedContract X86_64.abi stk)
    (hbs : sd.1 ∈ bases) (hba : a.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ Spec.MlDsa.rejBoundedLeak eta (bytesAt x.mem (pa x sd) 66) =
      Spec.MlDsa.rejBoundedLeak eta (bytesAt y.mem (pa y sd) 66)) (rejBoundedAt c sd eta a) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => glueRB_ok eta (eta_lt heta) hsd ha (sc_ok oSS (by decide)) x
  refine primTr hc (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (imm_nomem _ _)) (lea_nomem _ _))
      (lea_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, e⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, rejB_pre heta h1 h2 h3 hs T.sx hv1 k1, rejB_pre heta h1 h2 h3 hs T.sy hv2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rww T.sx.lay i1 w1 w2, by rw [k1.2.2]; exact covers2 T.sx.lay w1 w2,
        by rw [k2.2.1, k2.2.2]; exact covers_rww T.sy.lay i1 w1 w2, by rw [k2.2.2]; exact covers2 T.sy.lay w1 w2,
        by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, T.pa hbs, T.pa hba,
    T.pa (q := sc oSS) (by decide), w32_toNat (eta_lt heta), and_true]
  refine ⟨by rw [keep_rsp k1, keep_rsp k2, T.rsp], ?_⟩
  rw [T.pa hbs] at e
  rw [ce_bytesAt' (by decide) (by rw [keep_rsp k1, ← T.pa hbs]; exact T.sx.lay.stkD i1),
    ce_bytesAt' (by decide) (by rw [keep_rsp k2]; exact T.sy.lay.stkD i1), hm1, hm2, e]

end

/-! ## `SimpleBitPack` -/

section
variable {p : Params} {f out : Ptr} {b len : Nat} (hb : b ∈ Spec.MlDsa.simpleBitPackBounds)
  (hl : len = 32 * Spec.MlDsa.bitlen b) (hf : PtrOk f) (ho : PtrOk out)
  (h1 : sepB (kgB p) f 1024 out len = true) (w1 : inB (kgW p) out len = true)

theorem sbp_lt (hb : b ∈ Spec.MlDsa.simpleBitPackBounds) : b < 2 ^ 32 := by
  simp only [Spec.MlDsa.simpleBitPackBounds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem sbpLen_lt (hb : b ∈ Spec.MlDsa.simpleBitPackBounds) (hl : len = 32 * Spec.MlDsa.bitlen b) : len < 2 ^ 32 := by
  simp only [Spec.MlDsa.simpleBitPackBounds, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> subst hl <;> decide

include hb hl h1 in
theorem sbp_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s)
    (hbd : ∀ i < 256, (Spec.MlDsa.coeffAt s.mem (pa s f) i).toNat ≤ b)
    (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 b ∧ s1.gpr .rdx = pa s out ∧
      s1.gpr .rcx = BitVec.ofNat 64 len) (hm : s1.mem = s.mem) (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.simpleBitPackContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩] [⟨pa s out, len⟩]) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := keep_rsp k
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, w32_toNat (sbp_lt hb), w64_toNat (sbpLen_lt hb hl)]
    cpre L hsp S.h24
    · exact hb
    · exact hl
    · intro i hi
      rw [ce_coeffAt (by rw [hsp]; exact L.stkD i1) hi, hm]
      exact hbd i hi

include hb hl hf ho h1 w1 in
theorem sbpAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.simpleBitPackContract X86_64.abi stk)
    {s : State} (S : Site p s) (hbd : ∀ i < 256, (Spec.MlDsa.coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt c f b out len) s fun s' => Post s s' [⟨pa s out, len⟩] ∧ MX s' = MX s ∧
      bytesAt s'.mem (pa s out) len = Spec.MlDsa.simpleBitPack (Spec.MlDsa.natPolyAt s.mem (pa s f)) b := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (noLd_append (lea_noLd _ _) (imm_noLd _ _)) (lea_noLd _ _))
      (imm_noLd _ _))
    (glueSB_ok b len (sbp_lt hb) (sbpLen_lt hb hl) hf ho s) (fun stk hs s1 hv hm k => sbp_pre hb hl h1 hs S hbd hv hm k)
    (covers_rw L i1 w1) (covers_cons (L.cW w1) covers_nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hm₂, w32_toNat (sbp_lt hb), w64_toNat (sbpLen_lt hb hl)] at hpost
  rwa [ce_natPolyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hb hl hf ho h1 w1 in
theorem sbpAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.simpleBitPackContract X86_64.abi stk)
    (hbf : f.1 ∈ bases) (hbo : out.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ (∀ i < 256, (Spec.MlDsa.coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (Spec.MlDsa.coeffAt y.mem (pa y f) i).toNat ≤ b)) (simpleBitPackAt c f b out len) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => glueSB_ok b len (sbp_lt hb) (sbpLen_lt hb hl) hf ho x
  refine primTr hc (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (imm_nomem _ _)) (lea_nomem _ _))
      (imm_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, sbp_pre hb hl h1 hs T.sx rx hv1 hm1 k1, sbp_pre hb hl h1 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rw T.sx.lay i1 w1,
        by rw [k1.2.2]; exact covers_cons (T.sx.lay.cW w1) covers_nil,
        by rw [k2.2.1, k2.2.2]; exact covers_rw T.sy.lay i1 w1,
        by rw [k2.2.2]; exact covers_cons (T.sy.lay.cW w1) covers_nil, by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.simpleBitPackContract, Spec.MlDsa.simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, keep_rsp k1, keep_rsp k2,
    T.rsp, T.pa hbf, T.pa hbo, and_self]

end

/-! ## `BitPack` -/

section
variable {p : Params} {f out : Ptr} {a b len : Nat} (hab : (a, b) ∈ Spec.MlDsa.bitPackParams)
  (hl : len = 32 * Spec.MlDsa.bitlen (a + b)) (hf : PtrOk f) (ho : PtrOk out)
  (h1 : sepB (kgB p) f 1024 out len = true) (w1 : inB (kgW p) out len = true)

/-- The coefficients a `BitPack` to `(a, b)` packs. -/
def PackIn (m : Mem) (q : Addr) (a b : Nat) : Prop :=
  Spec.MlDsa.Reduced m q ∧ ∀ i < 256, -(a : Int) ≤ Spec.MlDsa.modPm (Spec.MlDsa.coeffAt m q i).toNat Spec.MlDsa.q ∧
    Spec.MlDsa.modPm (Spec.MlDsa.coeffAt m q i).toNat Spec.MlDsa.q ≤ b

theorem bp_lt (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) : a < 2 ^ 32 ∧ b < 2 ^ 32 := by
  simp only [Spec.MlDsa.bitPackParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpLen_lt (hab : (a, b) ∈ Spec.MlDsa.bitPackParams) (hl : len = 32 * Spec.MlDsa.bitlen (a + b)) :
    len < 2 ^ 32 := by
  simp only [Spec.MlDsa.bitPackParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> subst hl <;> decide

include hab hl h1 in
theorem bp_pre {stk : Nat} (hstk : stk ≤ 16) {s s1 : State} (S : Site p s) (hin : PackIn s.mem (pa s f) a b)
    (hv : s1.gpr .rdi = pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 a ∧ s1.gpr .rdx = BitVec.ofNat 64 b ∧
      s1.gpr .rcx = pa s out ∧ s1.gpr .r8 = BitVec.ofNat 64 len) (hm : s1.mem = s.mem)
    (k : Keep MlKem.X86_64.argRegs s s1) :
    (Spec.MlDsa.bitPackContract X86_64.abi stk).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩] [⟨pa s out, len⟩]) := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  have hsp := keep_rsp k
  have hk : (below (s1.gpr .rsp) 24).Disjoint ⟨pa s f, 1024⟩ := by rw [hsp]; exact L.stkD i1
  rcases stk with _ | n <;>
  · sig_pre [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86_64.abi, VG.X86_64.argRegs]
    simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, w32_toNat (bp_lt hab).1, w32_toNat (bp_lt hab).2,
      w64_toNat (bpLen_lt hab hl)]
    cpre L hsp S.h24
    · exact hab
    · exact hl
    · exact (ce_reduced hk).mpr (hm ▸ hin.1)
    · intro i hi
      rw [ce_coeffAt hk hi, hm]
      exact hin.2 i hi

include hab hl hf ho h1 w1 in
theorem bpAt_ok {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.bitPackContract X86_64.abi stk)
    {s : State} (S : Site p s) (hin : PackIn s.mem (pa s f) a b) :
    WP isa (bitPackAt c f a b out len) s fun s' => Post s s' [⟨pa s out, len⟩] ∧ MX s' = MX s ∧
      bytesAt s'.mem (pa s out) len = Spec.MlDsa.bitPack ((Spec.MlDsa.polyAt s.mem (pa s f)).map
        fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) a b := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have L := S.lay
  refine WP.mono (primOk hc (noLd_append (noLd_append (noLd_append (noLd_append (lea_noLd _ _) (imm_noLd _ _))
      (imm_noLd _ _)) (lea_noLd _ _)) (imm_noLd _ _))
    (glueBP_ok a b len (bp_lt hab).1 (bp_lt hab).2 (bpLen_lt hab hl) hf ho s)
    (fun stk hs s1 hv hm k => bp_pre hab hl h1 hs S hin hv hm k)
    (covers_rw L i1 w1) (covers_cons (L.cW w1) covers_nil))
    fun s' ⟨hP, hx, stk, _, s1, hv, hm, k, s₂, hm₂, _, hpost⟩ => ⟨hP, hx, ?_⟩
  have hsp := keep_rsp k
  sig_post [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86_64.abi, VG.X86_64.argRegs] at hpost
  simp only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hm₂, w32_toNat (bp_lt hab).1, w32_toNat (bp_lt hab).2,
    w64_toNat (bpLen_lt hab hl)] at hpost
  rwa [ce_polyAt (by rw [hsp]; exact L.stkD i1), hm] at hpost

include hab hl hf ho h1 w1 in
theorem bpAt_tr {c : Prog isa} (hc : Callee c fun stk => Spec.MlDsa.bitPackContract X86_64.abi stk)
    (hbf : f.1 ∈ bases) (hbo : out.1 ∈ bases) :
    RelCT isa (fun x y => Two p x y ∧ PackIn x.mem (pa x f) a b ∧ PackIn y.mem (pa y f) a b)
      (bitPackAt c f a b out len) fun _ _ => True := by
  obtain ⟨i1, _, _⟩ := sepB_spec h1
  have g := fun x => glueBP_ok a b len (bp_lt hab).1 (bp_lt hab).2 (bpLen_lt hab hl) hf ho x
  refine primTr hc (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (imm_nomem _ _))
      (imm_nomem _ _)) (lea_nomem _ _)) (imm_nomem _ _))
    (fun x y _ => ⟨g x, g y⟩)
    fun stk hs x y x1 y1 ⟨T, rx, ry⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ =>
      ⟨_, _, _, _, bp_pre hab hl h1 hs T.sx rx hv1 hm1 k1, bp_pre hab hl h1 hs T.sy ry hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact covers_rw T.sx.lay i1 w1,
        by rw [k1.2.2]; exact covers_cons (T.sx.lay.cW w1) covers_nil,
        by rw [k2.2.1, k2.2.2]; exact covers_rw T.sy.lay i1 w1,
        by rw [k2.2.2]; exact covers_cons (T.sy.lay.cW w1) covers_nil, by rw [keep_rsp k1, keep_rsp k2, T.rsp]⟩
  sig_pub [Spec.MlDsa.bitPackContract, Spec.MlDsa.bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2,
    keep_rsp k1, keep_rsp k2, T.rsp, T.pa hbf, T.pa hbo, and_self]

end

end VG.Proof.MlDsa.X86_64.KeyGen
