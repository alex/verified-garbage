import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.Mul
import VerifiedGarbage.Proof.MlKem.Arm.Cbd2
import VerifiedGarbage.Proof.MlKem.Arm.Encode12
import VerifiedGarbage.Proof.MlKem.Arm.Decode12
import VerifiedGarbage.Proof.MlKem.Arm.CompressEncode
import VerifiedGarbage.Proof.MlKem.Arm.Decompress
import VerifiedGarbage.Proof.MlKem.Arm.CallF

/-!
# ML-KEM on 32-bit ARM: calling the primitives

Untrusted: everything here is checked by Lean. For each primitive, a
contract written with the precondition of its proof (`Add.Pre`, …) and
what its correctness proof shows (`kAdd`, …), from which a caller runs a
call of it (`add_call`, …, by `WP.call`, or `WP.callF` for
`vg_mlkem_sample_ntt`, which has frames), given its arguments in the
registers and its buffers where it may access them (`AccArgs`, …); and
that two runs that call it with the same pointers leak the same trace
(`add_ct`, …, by `RelCT.call`, with constant time from the taint analysis
of its code, or from `Sample.all_ct`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Generic -/

/-- A contract from a precondition, what the code leaves and the public data. -/
def mkK (P : State → Prop) (Q : State → State → Prop) (pub : State → State → Prop) : Contract isa :=
  { pre := P, post := Q, pub := pub }

/-- The registers `rs` are the same. -/
def regsEq (rs : List Reg) (s₁ s₂ : State) : Prop := ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem mkK_ok {c : Prog isa} {P : State → Prop} {Q : State → State → Prop} {pub : State → State → Prop}
    (h : ∀ s₀, P s₀ → WP isa c s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ Q s₀ s) :
    ∀ s, (mkK P Q pub).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (mkK P Q pub).post s s' :=
  fun s hs => let ⟨t, s', he, h1, h2, h3⟩ := h s hs; ⟨t, s', he, ⟨h1, h2⟩, h3⟩

/-- The state a callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State := s.callEntry.withRegions rd wr

theorem view_gpr' (s : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-- A call of a primitive without calls: what it keeps, and its postcondition. -/
theorem call_kept {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) {s : State} {rd wr : List Region} (hpre : k.pre (view s rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept wr s s' → k.post (view s rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q :=
  WP.call hv hpre hc hw (fun s' hrd hwr hsp hf hcs _ hp => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hp) hn

/-- Two runs that call a primitive with the same arguments `x`. -/
theorem call_ct {α : Type} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (A : α → State → Prop) (rd wr : α → List Region)
    (hpre : ∀ x s, A x s → k.pre (view s (rd x) (wr x)))
    (hcov : ∀ x s, A x s → Covers (rd x ++ wr x) (s.rd ++ s.wr) ∧ Covers (wr x) s.wr)
    (hpub : ∀ x a b, A x a → A x b → k.pub (view a (rd x) (wr x)) (view b (rd x) (wr x)))
    {P : State → State → Prop} (hP : ∀ a b, P a b → ∃ x, A x a ∧ A x b) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine RelCT.mono (P := fun a b => ∃ x, A x a ∧ A x b) (RelCT.exists_ fun x => ?_) hP (fun _ _ h => h)
  exact RelCT.call hv hct (rd x) (wr x) fun a b ⟨ha, hb⟩ =>
    ⟨hpre x a ha, hpre x b hb, hpub x a b ha hb, (hcov x a ha).1, (hcov x a ha).2, (hcov x b hb).1,
      (hcov x b hb).2⟩

/-- A region the state may access. -/
theorem covers_self {r : Region} {ws : List Region} (h : r ∈ ws) : Covers [r] ws := by
  intro x n ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  exact ⟨_, h, hc⟩

/-- Part of a region the state may access. -/
theorem covers_off {base : Addr} {L o n : Nat} {ws : List Region} (h : (⟨base, L⟩ : Region) ∈ ws)
    (ho : o + n ≤ L) : Covers [⟨base + BitVec.ofNat 64 o, n⟩] ws := by
  intro x m ⟨q, hq, hc⟩
  rw [List.mem_singleton] at hq; subst hq
  refine ⟨_, h, ?_⟩
  simp only [Region.Contains] at hc ⊢
  bv_omega

theorem covers_append {rs ts ws : List Region} (h₁ : Covers rs ws) (h₂ : Covers ts ws) : Covers (rs ++ ts) ws :=
  fun x n ⟨q, hq, hc⟩ => (List.mem_append.mp hq).elim (fun h => h₁ x n ⟨q, h, hc⟩) (fun h => h₂ x n ⟨q, h, hc⟩)

theorem covers_cons' {r : Region} {rs ws : List Region} (h₁ : Covers [r] ws) (h₂ : Covers rs ws) :
    Covers (r :: rs) ws := covers_append (rs := [r]) h₁ h₂

theorem covers_nil' {ws : List Region} : Covers [] ws := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_rd {rs rd wr : List Region} (h : Covers rs rd) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_left _ hr, hc⟩

theorem covers_wr {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun x n hi =>
  let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## `vg_mlkem_add` and `vg_mlkem_sub` -/

def kAdd : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (add (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.r0, .r1])

def kSub : Contract isa := mkK Add.Pre
  (fun s₀ s => PolyIs s.mem (Add.F s₀) (sub (polyAt s₀.mem (Add.F s₀)) (polyAt s₀.mem (Add.G s₀))))
  (regsEq [.r0, .r1])

theorem kAdd_ok : ∀ s, kAdd.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.add s t s' ∧ abiPreserved s s' ∧
    kAdd.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.add_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kSub_ok : ∀ s, kSub.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.sub s t s' ∧ abiPreserved s s' ∧
    kSub.post s s' :=
  mkK_ok fun _ hp => WP.mono (Add.loop_ok hp (Add.sub_hb hp)) fun _ h =>
    ⟨h.pres, h.sp, Add.polyIs_of_inv h fun _ _ => rfl⟩

theorem kAdd_ct : ConstantTime isa kAdd.pre kAdd.pub Impl.MlKem.Arm.add :=
  Add.ctRegs [.r0, .r1] (fun _ _ h => h) (by taint_decide)

theorem kSub_ct : ConstantTime isa kSub.pre kSub.pub Impl.MlKem.Arm.sub :=
  Add.ctRegs [.r0, .r1] (fun _ _ h => h) (by taint_decide)

/-- The arguments of `vg_mlkem_add` or `vg_mlkem_sub`: `f` and `g`. -/
structure AccArgs (s : State) (f g : BitVec 32) : Prop where
  r0 : s.gpr .r0 = f
  r1 : s.gpr .r1 = g
  disj : (polyRegion (State.addr f)).Disjoint (polyRegion (State.addr g))
  ff : f.toNat + 1024 ≤ 2 ^ 32
  fg : g.toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (State.addr f)
  redG : Reduced s.mem (State.addr g)
  cw : Covers [polyRegion (State.addr f)] s.wr
  cr : Covers [polyRegion (State.addr g)] (s.rd ++ s.wr)

theorem acc_pre {s : State} {f g : BitVec 32} (h : AccArgs s f g) :
    Add.Pre (view s [polyRegion (State.addr g)] [polyRegion (State.addr f)]) := by
  have e0 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
  have e1 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
  rw [h.r0] at e0; rw [h.r1] at e1
  exact ⟨by simp only [Add.G, Add.pg, e1]; rfl, by simp only [Add.F, Add.pf, e0]; rfl,
    by simp only [Add.F, Add.G, Add.pf, Add.pg, e0, e1]; exact h.disj,
    by simp only [Add.pf, e0]; exact h.ff, by simp only [Add.pg, e1]; exact h.fg,
    by simp only [Add.F, Add.pf, e0]; exact h.redF, by simp only [Add.G, Add.pg, e1]; exact h.redG⟩

theorem add_call {s : State} {f g : BitVec 32} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion (State.addr f)] s s' →
      PolyIs s'.mem (State.addr f) (add (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) → Q s') :
    WP isa (.call "vg_mlkem_add" Impl.MlKem.Arm.add) s Q :=
  call_kept (k := kAdd) kAdd_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
      have e1 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
      rw [h.r0] at e0; rw [h.r1] at e1
      simpa only [kAdd, mkK, Add.F, Add.G, Add.pf, Add.pg, e0, e1, State.withRegions_mem,
        State.callEntry_mem] using hp)

theorem sub_call {s : State} {f g : BitVec 32} (h : AccArgs s f g) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion (State.addr f)] s s' →
      PolyIs s'.mem (State.addr f) (sub (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) → Q s') :
    WP isa (.call "vg_mlkem_sub" Impl.MlKem.Arm.sub) s Q :=
  call_kept (k := kSub) kSub_ok (by decide +kernel) (acc_pre h) (covers_append h.cr (covers_wr h.cw)) h.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r0) (by decide)
      have e1 := view_gpr' s [polyRegion (State.addr g)] [polyRegion (State.addr f)] (r := .r1) (by decide)
      rw [h.r0] at e0; rw [h.r1] at e1
      simpa only [kSub, mkK, Add.F, Add.G, Add.pf, Add.pg, e0, e1, State.withRegions_mem,
        State.callEntry_mem] using hp)

theorem acc_pub {f g : BitVec 32} {a b : State} (ha : AccArgs a f g) (hb : AccArgs b f g) :
    regsEq [.r0, .r1] (view a [polyRegion (State.addr g)] [polyRegion (State.addr f)])
      (view b [polyRegion (State.addr g)] [polyRegion (State.addr f)]) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [view_gpr' _ _ _ (by decide), view_gpr' _ _ _ (by decide), ha.r0, hb.r0]
  · rw [view_gpr' _ _ _ (by decide), view_gpr' _ _ _ (by decide), ha.r1, hb.r1]

theorem add_ct {P : State → State → Prop} (hP : ∀ a b, P a b → ∃ f g, AccArgs a f g ∧ AccArgs b f g) :
    RelCT isa P (.call "vg_mlkem_add" Impl.MlKem.Arm.add) fun _ _ => True :=
  call_ct (k := kAdd) kAdd_ok kAdd_ct (fun (x : BitVec 32 × BitVec 32) s => AccArgs s x.1 x.2)
    (fun x => [polyRegion (State.addr x.2)]) (fun x => [polyRegion (State.addr x.1)])
    (fun _ _ h => acc_pre h) (fun _ _ h => ⟨covers_append h.cr (covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb => acc_pub ha hb) fun a b hab => let ⟨f, g, h₁, h₂⟩ := hP a b hab; ⟨(f, g), h₁, h₂⟩

theorem sub_ct {P : State → State → Prop} (hP : ∀ a b, P a b → ∃ f g, AccArgs a f g ∧ AccArgs b f g) :
    RelCT isa P (.call "vg_mlkem_sub" Impl.MlKem.Arm.sub) fun _ _ => True :=
  call_ct (k := kSub) kSub_ok kSub_ct (fun (x : BitVec 32 × BitVec 32) s => AccArgs s x.1 x.2)
    (fun x => [polyRegion (State.addr x.2)]) (fun x => [polyRegion (State.addr x.1)])
    (fun _ _ h => acc_pre h) (fun _ _ h => ⟨covers_append h.cr (covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb => acc_pub ha hb) fun a b hab => let ⟨f, g, h₁, h₂⟩ := hP a b hab; ⟨(f, g), h₁, h₂⟩

/-! ## `vg_mlkem_multiply_ntts` -/

def kMul : Contract isa := mkK Mul.Pre
  (fun s₀ s => PolyIs s.mem (Mul.H s₀) (multiplyNTTs (Mul.fp s₀) (Mul.gp s₀))) (regsEq [.r0, .r1, .r2, .r3])

theorem kMul_ok : ∀ s, kMul.pre s → ∃ t s', Exec isa Impl.MlKem.Arm.multiplyNTTs s t s' ∧ abiPreserved s s' ∧
    kMul.post s s' :=
  mkK_ok fun _ hp => Mul.correct hp

theorem kMul_ct : ConstantTime isa kMul.pre kMul.pub Impl.MlKem.Arm.multiplyNTTs :=
  Add.ctRegs [.r0, .r1, .r2, .r3] (fun _ _ h => h) (by taint_decide)

/-- The arguments of `vg_mlkem_multiply_ntts`. -/
structure MulArgs (s : State) (h f g scr : BitVec 32) : Prop where
  r0 : s.gpr .r0 = h
  r1 : s.gpr .r1 = f
  r2 : s.gpr .r2 = g
  r3 : s.gpr .r3 = scr
  hf : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr f))
  hg : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr g))
  hs : (polyRegion (State.addr h)).Disjoint (polyRegion (State.addr scr))
  fs : (polyRegion (State.addr f)).Disjoint (polyRegion (State.addr scr))
  gs : (polyRegion (State.addr g)).Disjoint (polyRegion (State.addr scr))
  fh : h.toNat + 1024 ≤ 2 ^ 32
  ff : f.toNat + 1024 ≤ 2 ^ 32
  fg : g.toNat + 1024 ≤ 2 ^ 32
  fscr : scr.toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (State.addr f)
  redG : Reduced s.mem (State.addr g)
  cw : Covers [polyRegion (State.addr h), polyRegion (State.addr scr)] s.wr
  cr : Covers [polyRegion (State.addr f), polyRegion (State.addr g)] (s.rd ++ s.wr)

abbrev mulRd (f g : BitVec 32) : List Region := [polyRegion (State.addr f), polyRegion (State.addr g)]
abbrev mulWr (h scr : BitVec 32) : List Region := [polyRegion (State.addr h), polyRegion (State.addr scr)]

theorem mul_pre {s : State} {h f g scr : BitVec 32} (a : MulArgs s h f g scr) :
    Mul.Pre (view s (mulRd f g) (mulWr h scr)) := by
  have e0 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r0) (by decide)
  have e1 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r1) (by decide)
  have e2 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r2) (by decide)
  have e3 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r3) (by decide)
  rw [a.r0] at e0; rw [a.r1] at e1; rw [a.r2] at e2; rw [a.r3] at e3
  exact ⟨by simp only [Mul.F, Mul.G, Mul.pf, Mul.pg, e1, e2]; rfl, by simp only [Mul.H, Mul.S, Mul.ph, Mul.ps, e0, e3]; rfl,
    by simp only [Mul.H, Mul.F, Mul.ph, Mul.pf, e0, e1]; exact a.hf,
    by simp only [Mul.H, Mul.G, Mul.ph, Mul.pg, e0, e2]; exact a.hg,
    by simp only [Mul.H, Mul.S, Mul.ph, Mul.ps, e0, e3]; exact a.hs,
    by simp only [Mul.F, Mul.S, Mul.pf, Mul.ps, e1, e3]; exact a.fs,
    by simp only [Mul.G, Mul.S, Mul.pg, Mul.ps, e2, e3]; exact a.gs,
    by simp only [Mul.ph, e0]; exact a.fh, by simp only [Mul.pf, e1]; exact a.ff,
    by simp only [Mul.pg, e2]; exact a.fg, by simp only [Mul.ps, e3]; exact a.fscr,
    by simp only [Mul.F, Mul.pf, e1]; exact a.redF, by simp only [Mul.G, Mul.pg, e2]; exact a.redG⟩

theorem mul_call {s : State} {h f g scr : BitVec 32} (a : MulArgs s h f g scr) {Q : State → Prop}
    (hQ : ∀ s', Kept (mulWr h scr) s s' →
      PolyIs s'.mem (State.addr h) (multiplyNTTs (polyAt s.mem (State.addr f)) (polyAt s.mem (State.addr g))) →
      Q s') :
    WP isa (.call "vg_mlkem_multiply_ntts" Impl.MlKem.Arm.multiplyNTTs) s Q :=
  call_kept (k := kMul) kMul_ok (by decide +kernel) (mul_pre a) (covers_append a.cr (covers_wr a.cw)) a.cw
    fun s' hk hp => hQ s' hk (by
      have e0 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r0) (by decide)
      have e1 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r1) (by decide)
      have e2 := view_gpr' s (mulRd f g) (mulWr h scr) (r := .r2) (by decide)
      rw [a.r0] at e0; rw [a.r1] at e1; rw [a.r2] at e2
      simpa only [kMul, mkK, Mul.H, Mul.fp, Mul.gp, Mul.F, Mul.G, Mul.ph, Mul.pf, Mul.pg, e0, e1, e2,
        State.withRegions_mem, State.callEntry_mem] using hp)

theorem regsEq_view {rs : List Reg} (hl : ∀ r ∈ rs, r ∉ linkRegs) {a b : State} (hab : ∀ r ∈ rs, a.gpr r = b.gpr r)
    (rd wr : List Region) : regsEq rs (view a rd wr) (view b rd wr) := fun r hr => by
  rw [view_gpr' _ _ _ (hl r hr), view_gpr' _ _ _ (hl r hr), hab r hr]

theorem mul_ct {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∃ h f g scr, MulArgs a h f g scr ∧ MulArgs b h f g scr) :
    RelCT isa P (.call "vg_mlkem_multiply_ntts" Impl.MlKem.Arm.multiplyNTTs) fun _ _ => True :=
  call_ct (k := kMul) kMul_ok kMul_ct (fun (x : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) s =>
      MulArgs s x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x => mulRd x.2.1 x.2.2.1) (fun x => mulWr x.1 x.2.2.2)
    (fun _ _ h => mul_pre h) (fun _ _ h => ⟨covers_append h.cr (covers_wr h.cw), h.cw⟩)
    (fun _ _ _ ha hb => regsEq_view (by decide) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [ha.r0, hb.r0]
      · rw [ha.r1, hb.r1]
      · rw [ha.r2, hb.r2]
      · rw [ha.r3, hb.r3]) _ _)
    fun a b hab => let ⟨h, f, g, scr, h₁, h₂⟩ := hP a b hab; ⟨(h, f, g, scr), h₁, h₂⟩

end VG.Proof.MlKem.Arm
