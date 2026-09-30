import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Lay
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# ML-DSA signing on x86-64: calls of verified code

Untrusted: everything here is checked by Lean. A primitive the function
calls is any code verified against its shared contract (`Spec/MlDsa/Poly.lean`)
for some stack of `S` bytes that leaves 8 bytes for the return address in
the `D` bytes the function gives its calls, and that never writes `rsp`
(`Callee`). A call, with the moves of its arguments before it
(`glueCall_ok`), leaves the permissions and the callee-saved registers as
they were, and changes memory only within the buffers it writes and the `D`
bytes of stack below `rsp`. Two runs of it leak the same when the callee's
public data agree (`glueCall_tr`), and a callee whose result is public in
its own runs (`RetPub`) returns the same in both (`glueCallRet_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ argRegs := by decide

theorem bases_cs : ∀ r ∈ bases, r ∈ calleeSaved := by decide

/-- Code verified against the contract `k S` for a stack of `S` bytes, with
8 bytes to spare in `D`, which never writes `rsp` and whose calls nest
within `D` bytes. -/
structure Callee (k : Nat → Contract isa) (D : Nat) (c : Prog isa) where
  /-- The stack its contract gives it. -/
  S : Nat
  hS : S + 8 ≤ D
  ver : Verified X86_64.target c (k S)
  nosp : NoSp c
  depth : 8 * (c.depth + 1) ≤ D

/-- The result of `c` (the low 32 bits of `rax`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32

/-! ## Blocks without memory accesses -/

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(execBlock_nomem h e₁).trans (execBlock_nomem h e₂).symm, trivial⟩

theorem nomem_append {a b : List Instr} (ha : ∀ i ∈ a, ∀ s, isa.addrs i s = [])
    (hb : ∀ i ∈ b, ∀ s, isa.addrs i s = []) : ∀ i ∈ a ++ b, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h s, hb i h s]

theorem lea_nomem (d : Reg) (p : Ptr) : ∀ i ∈ lea d p, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem movi_nomem (d : Reg) (v : Nat) : ∀ i ∈ movi d v, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [movi, List.mem_singleton] at hi
  subst hi; rfl

/-! ## The stack of a call -/

theorem ce_ret {sp : Addr} {D : Nat} {R : Region} (h : (below sp D).Disjoint R) (hD : 8 ≤ D) (hDs : D < 2 ^ 32) :
    Region.Disjoint ⟨sp - 8, 8⟩ R :=
  h.sub_left fun x hx => by
    simp only [Region.Contains] at hx ⊢
    rw [show x - (sp - BitVec.ofNat 64 D) = (x - (sp - 8)) + BitVec.ofNat 64 (D - 8) by
      rw [show BitVec.ofNat 64 (D - 8) = BitVec.ofNat 64 D - 8 by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (8 : BitVec 64).toNat = 8 := rfl
        rw [this]; omega]
      bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := D - 8) (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem ce_below {sp : Addr} {D S : Nat} {R : Region} (h : (below sp D).Disjoint R) (hS : S + 8 ≤ D)
    (hDs : D < 2 ^ 32) : (below (sp - 8) S).Disjoint R :=
  (h.sub_left (below_sub hS (by omega))).sub_left (below_callee sp S)

theorem ce_stackBelow {sp : Addr} {D S : Nat} {R : Region} (h : (below sp D).Disjoint R) (hS : S + 8 ≤ D)
    (hDs : D < 2 ^ 32) : ∀ r ∈ stackBelow (sp - 8) S, r.Disjoint R := by
  intro r hr
  cases S with
  | zero => simp [stackBelow] at hr
  | succ S =>
    simp only [stackBelow, List.mem_singleton] at hr
    subst hr
    exact ce_below h hS hDs

theorem ce_wf {sp : Addr} {D S : Nat} (hS : S + 8 ≤ D) (hsp : D ≤ sp.toNat) :
    S ≤ (sp - 8).toNat := by
  rw [BitVec.toNat_sub]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  have := sp.isLt
  omega

theorem abi_wf_of {ws : List Nat} (hws : ws.length ≤ 6) {S : Nat} {s : State} (h : S ≤ (s.gpr .rsp).toNat) :
    X86_64.abi.wf ws S s := by
  simp only [X86_64.abi, VG.X86_64.argRegs, List.length_cons, List.length_nil, Nat.reduceAdd, hws, ite_true]
  cases S <;> simp_all

/-- The facts about the stack a callee's contract needs, on entry: its
stack pointer leaves `S` bytes below it. -/
theorem ce_wfS {ws : List Nat} (hws : ws.length ≤ 6) {D S : Nat} (hS : S + 8 ≤ D) {s : State}
    (hsp : D ≤ (s.gpr .rsp).toNat) (rd wr : List Region) : X86_64.abi.wf ws S (s.callEntry.withRegions rd wr) :=
  abi_wf_of hws (by simp only [State.withRegions_gpr, State.callEntry_rsp]; exact ce_wf hS hsp)

/-- The regions of the stack a callee's contract gives it, apart from each buffer. -/
theorem conj_stk {sp : Addr} {S : Nat} (bs : List Region) (h : ∀ B ∈ bs, (below sp S).Disjoint B) :
    Sig.conj ((List.map (fun r => bs.map fun B => r.Disjoint B) (stackBelow sp S)).flatten) := by
  cases S with
  | zero => exact trivial
  | succ S =>
    simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Sig.conj_map]
    exact h

/-! ## Memory on entry to a callee -/

theorem ce_byte (s : State) {D : Nat} {R : Region} (h : (below (s.gpr .rsp) D).Disjoint R) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [⟨s.gpr .rsp - 8, 8⟩])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (by simpa using (ce_ret h hD hDs).symm) hR hi

theorem ce_polyAt (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : polyAt s.callEntry.mem p = polyAt s.mem p :=
  polyAt_congr fun _ hi => ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi

theorem ce_natPolyAt (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : natPolyAt s.callEntry.mem p = natPolyAt s.mem p :=
  natPolyAt_congr fun _ hi => ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi

theorem ce_reduced (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : Reduced s.callEntry.mem p ↔ Reduced s.mem p :=
  ⟨reduced_congr fun _ hi => (ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi).symm,
    reduced_congr fun _ hi => ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi⟩

theorem ce_bytesAt (s : State) {D : Nat} {p : Addr} {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : (below (s.gpr .rsp) D).Disjoint ⟨p, n⟩) (hD : 8 ≤ D) (hDs : D < 2 ^ 32) :
    bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  VG.Proof.MlKem.bytesAt_congr fun _ hi => ce_byte s (R := ⟨p, n⟩) h hD hDs hn hi

/-! ## A call, with the moves of its arguments -/

/-- The moves of the arguments, then a call of verified code. -/
theorem glueCall_ok {D : Nat} {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => PostB D s s' wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono hg fun s1 ⟨⟨hV, hm⟩, k1⟩ => ?_)
  refine WP.call hv hsp (by omega) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r (bases_cs r hr), k1.gpr (argRegs_cs r (bases_cs r hr))],
      by rw [hcs .rsp (by decide), k1.gpr (by decide)], ?_⟩,
      fun r hr => by rw [hcs r hr, k1.gpr (argRegs_cs r hr)], s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf hd (by omega)

/-- The trace of the moves then a call, from two runs where the moves are
the same and the callee's public data agree. -/
theorem glueCall_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} {V : State → State → Prop}
    (hgt : RelCT isa P (.block glue) fun _ _ => True)
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c)) fun _ _ => True :=
  RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ V x x1 ∧ V y y1) hgt hg
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx hv hct fun x1 y1 ⟨x, y, hp, h1, h2⟩ => hP x y x1 y1 hp h1 h2)

/-- A call of verified code whose result is public in its own runs, narrowed
in each run to regions of its own: the same trace, and the same result. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      -- Each run is the widening of the narrowed run.
      have narrow : ∀ {s : State} {rd wr : List Region} {t : List Leak} {s' : State},
          k.pre (s.callEntry.withRegions rd wr) → Covers (rd ++ wr) (s.rd ++ s.wr) → Covers wr s.wr →
          Exec isa c s.callEntry t s' → ∃ s'', Exec isa c (s.callEntry.withRegions rd wr) t s'' ∧
            s''.gpr = s'.gpr := by
        intro s rd wr t s' hpre hc hw he
        obtain ⟨t', s'', he', -⟩ := hv _ hpre
        have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
        simp only [State.withRegions_withRegions] at hw'
        rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at hw'
        obtain ⟨rfl, rfl⟩ := Exec.det he hw'
        exact ⟨_, he', rfl⟩
      obtain ⟨n₁, x₁, g₁⟩ := narrow p₁ c₁ w₁ b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow p₂ c₂ w₂ b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      have q₁ := VG.X86_64.ret_rsp r₁
      have q₂ := VG.X86_64.ret_rsp r₂
      simp only [State.callEntry_rsp] at q₁ q₂
      refine ⟨?_, ?_⟩
      · simp only [q₁, q₂, hsp, ht]
      · simp only [isa, ret] at r₁ r₂
        split at r₁ <;> [skip; cases r₁]
        split at r₂ <;> [skip; cases r₂]
        cases r₁; cases r₂
        simp only [State.setReg]
        rw [← g₁, ← g₂]; exact hrax

/-- The moves of the arguments then a call whose result is public: the same
trace, and the same result, in both runs. -/
theorem glueCallRet_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} {V : State → State → Prop}
    (hgt : RelCT isa P (.block glue) fun _ _ => True)
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c))
      fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 :=
  RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ V x x1 ∧ V y y1) hgt hg
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callRet hv hr fun x1 y1 ⟨x, y, hp, h1, h2⟩ => hP x y x1 y1 hp h1 h2)

end VG.Proof.MlDsa.X86_64.Sign
