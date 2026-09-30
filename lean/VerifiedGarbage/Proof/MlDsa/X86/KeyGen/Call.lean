import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call

/-!
# ML-DSA on x86 (32-bit): calls of the primitives from the top-level functions

Untrusted: everything here is checked by Lean. The top-level functions are
proven as ML-KEM's (`Proof/MlKem/X86/Top.lean`: `Lay`, `Buf`, `Ctx`,
`Piece`), for any verified implementations of the primitives (`Callee`).

A call (`callP`, `callPR`) sets its arguments (`setArgs_ok`: each register
holds its argument's value, `Arg.val`), pushes them and calls. The callee's
entry state (`Ent`) has those arguments on its stack, the memory of the
buffers as the caller left it, and the stack of the call below `E1` (`esp`
in the body): the arguments, the return address, and the callee's own
stack. `callP_piece` makes the call a `Piece` from the callee's precondition
and public data on such an entry state, and gives its postcondition, with
the memory changed only in the buffers it writes and the 80 bytes of stack
below `E1`: at most 5 arguments, the return address and the callee's 56 bytes.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen (Arg argRegs setArgs argRs callP callPR)

/-! ## The primitives -/

/-- Code verified against `k (K + 1)`, for some stack `K + 1 ≤ 56` (every
function uses some stack, if only for its return address), using at most 56
bytes of stack, and that never writes `esp` but by frames and calls. -/
structure Callee (c : Prog isa) (k : Nat → Contract isa) : Prop where
  verified : ∃ K, K + 1 ≤ 56 ∧ Verified X86.target c (k (K + 1))
  stack : stackUse c ≤ 56
  nosp : NoSp c


variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-! ## Arguments -/

/-- An argument within the layout: a buffer of it, or an immediate of 32 bits. -/
def _root_.VG.Impl.MlDsa.X86.KeyGen.Arg.ok (Y : Lay) : Arg → Bool
  | .buf b => Y.ok b
  | .imm v => decide (v < 2 ^ 32)

/-- The value of an argument. -/
def _root_.VG.Impl.MlDsa.X86.KeyGen.Arg.val (s₀ : State) : Arg → BitVec 32
  | .buf b => b.ptr s₀
  | .imm v => BitVec.ofNat 32 v

theorem _root_.VG.Impl.MlDsa.X86.KeyGen.Arg.val_eq {s₀ s₀' : State} (hq : TPub Y lk s₀ s₀') {a : Arg} (ha : a.ok Y = true) :
    a.val s₀ = a.val s₀' := by
  cases a with
  | buf b => exact hq.ptr ha
  | imm v => rfl

/-- Setting the arguments `as` in the registers `rs`. -/
theorem setArgs_ok {s₀ : State} (hp : TPre Y s₀) {Q : State → Prop} {is : List Instr} :
    ∀ (rs : List Reg) (as : List Arg) (s : State), Ctx Y s₀ s → (∀ r ∈ rs, r ≠ .esp ∧ r ≠ .esi) →
      rs.Nodup → as.all (Arg.ok Y) = true →
      (∀ s', Only rs s s' → Ctx Y s₀ s' →
        (∀ i (h₁ : i < rs.length) (h₂ : i < as.length), s'.gpr rs[i] = as[i].val s₀) → WP isa (.block is) s' Q) →
      WP isa (.block (setArgs Y.sc rs as ++ is)) s Q
  | [], _, s, h, _, _, _, k => k s (Only.refl _ _) h fun _ h₁ => absurd h₁ (Nat.not_lt_zero _)
  | _ :: _, [], s, h, _, _, _, k => k s (Only.refl _ _) h fun _ _ h₂ => absurd h₂ (Nat.not_lt_zero _)
  | r :: rs, a :: as, s, h, hr, hnd, hok, k => by
    have hr0 := hr r (List.mem_cons_self ..)
    rw [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨hnr, hnd'⟩ := List.nodup_cons.mp hnd
    have step : ∀ s₁, Only [r] s s₁ → s₁.gpr r = a.val s₀ →
        WP isa (.block (setArgs Y.sc rs as ++ is)) s₁ Q := by
      intro s₁ o₁ v₁
      have c₁ := h.only o₁ (by simpa using hr0.1.symm) (by simpa using hr0.2.symm)
      refine setArgs_ok hp rs as s₁ c₁ (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) hnd' hok.2
        fun s' o' c' v' => k s' ((o₁.trans o').mono fun x hx => by simpa using hx) c' fun i h₁ h₂ => ?_
      cases i with
      | zero => simp only [List.getElem_cons_zero]; rw [o'.gpr r hnr, v₁]
      | succ i => simpa using v' i (by simpa using h₁) (by simpa using h₂)
    show WP isa (.block ((Arg.set Y.sc r a ++ setArgs Y.sc rs as) ++ is)) s Q
    rw [List.append_assoc]
    cases a with
    | buf b => exact ptrTo_ok hp h hok.1 step
    | imm v => exact wp_movi fun s₁ o₁ v₁ => step s₁ o₁ v₁

/-! ## The callee's entry -/

/-- `e` is the entry state of a call with the arguments `as`, set from `s`. -/
structure Ent (Y : Lay) (s₀ s : State) (as : List Arg) (e : State) : Prop where
  esp : e.gpr .esp = E1 s₀ - BitVec.ofNat 32 (4 * as.length + 4)
  arg : ∀ i (h : i < as.length), arg e i = as[i].val s₀
  argAddr0 : argAddr e 0 = (E1 s₀ - BitVec.ofNat 32 (4 * as.length)).setWidth 64
  mem : ∀ b, Y.ok b = true → ∀ i < b.len, e.mem (b.addr s₀ + BitVec.ofNat 64 i) = s.mem (b.addr s₀ + BitVec.ofNat 64 i)

theorem argRs_len {n : Nat} (hn : n ≤ 6) : (argRs n).length = n := by
  simp only [argRs, List.length_reverse, List.length_take, argRegs, List.length_cons, List.length_nil]; omega

theorem argRs_ne {n : Nat} (hn : n ≠ 0) (hn' : n ≤ 6) : argRs n ≠ [] := fun h => by
  have := argRs_len hn'; rw [h] at this; exact hn this.symm

theorem esp_argRs (n : Nat) : Reg.esp ∉ argRs n := by
  simp only [argRs, List.mem_reverse]
  intro h
  have := List.mem_of_mem_take h
  simp [argRegs] at this

theorem argRs_getD : ∀ n ≤ 6, ∀ i < n, (argRs n).getD ((argRs n).length - 1 - i) .esp = argRegs.getD i .esp := by
  decide

theorem ctx_E' {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) (hN : 96 ≤ Y.stk) :
    80 ≤ (s.gpr .esp).toNat := ctx_E hp h (N := 80) (by omega)

theorem ent_of {s₀ s s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : Ctx Y s₀ s₁) (m₁ : s₁.mem = s.mem)
    {as : List Arg} (hn : as.length ≤ 5)
    (v : ∀ i (h₁ : i < argRegs.length) (h₂ : i < as.length), s₁.gpr argRegs[i] = as[i].val s₀) :
    Ent Y s₀ s as (pushed (argRs as.length) s₁).callEntry := by
  have hE := ctx_E' hp h₁ hN
  have hl := argRs_len (n := as.length) (by omega)
  have fit : 4 * (argRs as.length).length + 4 ≤ (s₁.gpr .esp).toNat := by rw [hl]; omega
  refine ⟨?_, fun i hi => ?_, ?_, fun b hb i hi => ?_⟩
  · rw [callEntry_esp', h₁.esp, hl]
  · rw [callEntry_arg fit (esp_argRs _) (by rw [hl]; exact hi), List.getElem_eq_getD .esp,
      argRs_getD as.length (by omega) i hi]
    rw [← List.getElem_eq_getD (h := by simp [argRegs]; omega) Reg.esp]
    exact v i (by simp [argRegs]; omega) hi
  · rw [callEntry_argAddr0, h₁.esp, hl]
  · rw [← m₁]
    exact ent_keep hp h₁ (esp_argRs _) (by rw [hl]; omega) hb i hi

/-- The regions of the callee's entry, apart from a buffer. -/
theorem Ent.rgn {s₀ s e : State} {as : List Arg} (he : Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) {b : Buf} (hb : Y.ok b = true) {K : Nat} (hK : K ≤ 56) :
    (b.rgn s₀).Disjoint (below (E1 s₀) (4 * as.length)) ∧
      (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (b.rgn s₀) ∧
      (⟨(e.gpr .esp).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (b.rgn s₀) := by
  have hE : 4 * as.length + 4 + K ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
  rw [he.esp]
  exact entry_regions hE (Buf.stkD hp hb (N := 4 * as.length + 4 + K) (by omega))

/-- The callee's own regions, apart from each other. -/
theorem Ent.self {s₀ s e : State} {as : List Arg} (he : Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) {K : Nat} (hK : K ≤ 56) :
    (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (E1 s₀) (4 * as.length)) ∧
      (⟨(e.gpr .esp).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (below (E1 s₀) (4 * as.length)) := by
  have hE : 4 * as.length + 4 + K ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
  rw [he.esp]
  exact entry_self hE

/-- The callee's stack pointer, as a number. -/
theorem Ent.espNat {s₀ s e : State} {as : List Arg} (he : Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) : (e.gpr .esp).toNat = (E1 s₀).toNat - (4 * as.length + 4) ∧ 80 ≤ (E1 s₀).toNat := by
  have hE : 80 ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
  rw [he.esp, sub_toNat (by omega)]
  exact ⟨rfl, hE⟩

/-! ## A call -/

/-- The regions of a call: the buffers it reads, and those it writes and its arguments. -/
abbrev rdR (s₀ : State) (rB : List Buf) : List Region := rB.map (Buf.rgn s₀)
abbrev wrR (s₀ : State) (wB : List Buf) (n : Nat) : List Region := wB.map (Buf.rgn s₀) ++ [below (E1 s₀) (4 * n)]

section
variable {k : Contract isa} {nm : String} {c : Prog isa} (as : List Arg) (rB wB : List Buf)

/-- The setting of the arguments of a call. -/
theorem setup_call (hok : as.all (Arg.ok Y) = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s) :
    Piece (TPre Y) (TPub Y lk) A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx Y s₀ s₁ ∧ s₁.mem = s.mem ∧
      ∀ i (h₁ : i < argRegs.length) (h₂ : i < as.length), s₁.gpr argRegs[i] = as[i].val s₀)
      (.block (setArgs Y.sc argRegs as)) :=
  setup_piece _ (fun s₀ s hp h => by
    rw [← List.append_nil (setArgs Y.sc argRegs as)]
    exact setArgs_ok hp argRegs as s h (by decide) (by decide) hok fun s' o c v =>
      WP.block_nil_iff.mpr ⟨c, o.mem, v⟩) hA tt

theorem call_hd {s₀ s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : Ctx Y s₀ s₁) (hst : stackUse c ≤ 56)
    (hn : as.length ≤ 5) : 4 * (argRs as.length).length + stackUse c + 4 ≤ (s₁.gpr .esp).toNat := by
  rw [argRs_len (by omega)]; have := ctx_E' hp h₁ hN; omega

theorem call_cov {s₀ s₁ : State} (hp : TPre Y s₀) (h₁ : Ctx Y s₀ s₁) (hn : as.length ≤ 5)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true) :
    Covers (rdR s₀ rB ++ wrR s₀ wB as.length)
        (s₁.rd ++ below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) ∧
      Covers (wrR s₀ wB as.length) (below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) := by
  rw [argRs_len (by omega)]
  refine covers_of (fun r h => ?_) fun r h => ?_
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
    exact Buf.within hp (List.all_eq_true.mp hr b hb) h₁.rd h₁.wr
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      obtain ⟨o, w⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)
      exact .inr (Buf.withinW hp o w h₁.wr)
    · rw [List.mem_singleton] at h; subst h
      exact .inl (by rw [h₁.esp])

theorem call_fr {s₀ s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : Ctx Y s₀ s₁) (hst : stackUse c ≤ 56)
    (hn : as.length ≤ 5) {m m' : Mem}
    (fr : Frame (wrR s₀ wB as.length ++ [below (s₁.gpr .esp) (4 * (argRs as.length).length + stackUse c + 4)]) m m') :
    Frame (FR s₀ wB 80) m m' := by
  rw [h₁.esp, argRs_len (by omega)] at fr
  refine fr.sub fun r hr => ?_
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | rfl) | rfl
  · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp (by omega) (by omega)⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp (by omega) (by omega)⟩

theorem call_W {s₀ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (hw : wB.all Y.okW = true) :
    ∀ r ∈ FR s₀ wB 80, ∃ r' ∈ W Y s₀, Region.Sub r r' := wr_sub hp hw (by omega)

theorem call_pubs {s₀ s₀' s s' e e' : State} (hq : TPub Y lk s₀ s₀') (hok : as.all (Arg.ok Y) = true)
    (he : Ent Y s₀ s as e) (he' : Ent Y s₀' s' as e') :
    e.gpr .esp = e'.gpr .esp ∧ ∀ i < as.length, arg e i = arg e' i := by
  refine ⟨by rw [he.esp, he'.esp, hq.E1], fun i hi => ?_⟩
  rw [he.arg i hi, he'.arg i hi]
  exact Arg.val_eq hq (List.all_eq_true.mp hok _ (List.getElem_mem hi))

/-- A call of a primitive: see the module documentation. -/
theorem callP_piece (hv : Verified X86.target c k) (hsp : NoSp c) (hst : stackUse c ≤ 56)
    (hn₀ : as.length ≠ 0) (hn : as.length ≤ 5) (hok : as.all (Arg.ok Y) = true) (hN : 96 ≤ Y.stk)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hpre : ∀ s₀ s e, TPre Y s₀ → A s₀ s → Ent Y s₀ s as e →
      k.pre (e.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)))
    (hpub : ∀ s₀ s₀' s s' e e', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Ent Y s₀ s as e → Ent Y s₀' s' as e' →
      k.pub (e.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)) (e'.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ wB 80) s.mem s'.mem →
      (∃ e s₂, Ent Y s₀ s as e ∧ s₂.mem = s'.mem ∧ k.post (e.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)) s₂) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callP Y.sc nm c as) := by
  refine Piece.seq (setup_call as hok tt hA) ?_
  refine Piece.callWith hv.1 hv.2.1 hsp (argRs_ne hn₀ (by omega)) (esp_argRs _)
    (fun s₀ => rdR s₀ rB) (fun s₀ => wrR s₀ wB as.length)
    (fun s₀ s₁ hp ⟨_, _, h₁, _⟩ => call_hd as hp hN h₁ hst hn)
    (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, v⟩ => ⟨hpre s₀ s _ hp ha (ent_of hp hN h₁ m₁ hn v),
      (call_cov as rB wB hp h₁ hn hr hw).1, (call_cov as rB wB hp h₁ hn hr hw).2⟩)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h₁, m₁, v⟩ ⟨s', ha', h₁', m₁', v'⟩ => ?_)
    (fun s₀ s₁ s' hp ⟨s, ha, h₁, m₁, v⟩ e₁ e₂ e₃ fr ⟨s₂, m₂, post⟩ => ?_)
  · have er : rdR s₀ rB = rdR s₀' rB := List.map_congr_left fun b hb => by
      simp only [Buf.rgn, hq.ptr (List.all_eq_true.mp hr b hb)]
    have ew : wrR s₀ wB as.length = wrR s₀' wB as.length := by
      simp only [wrR, hq.E1]
      exact congrArg (· ++ _) (List.map_congr_left fun b hb => by
        simp only [Buf.rgn, hq.ptr (Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)).1])
    refine ⟨er, ew, by rw [h₁.esp, h₁'.esp, hq.E1], ?_⟩
    have := hpub s₀ s₀' s s' _ _ hp hp' hq ha ha' (ent_of hp hN h₁ m₁ hn v) (ent_of hp' hN h₁' m₁' hn v')
    exact this
  · have fr' := call_fr as wB hp hN h₁ hst hn fr
    have h' : Ctx Y s₀ s' := h₁.call e₁ e₂ e₃ fr' (call_W wB hp hN hw)
    rw [m₁] at fr'
    exact hQ s₀ s s' hp ha h' fr' ⟨_, s₂, ent_of hp hN h₁ m₁ hn v, m₂, post⟩

/-- `callP_piece`, for a call that returns a value in `eax` (`callPR`). -/
theorem callPR_piece (hv : Verified X86.target c k) (hsp : NoSp c) (hst : stackUse c ≤ 56)
    (hn₀ : as.length ≠ 0) (hn : as.length ≤ 5) (hok : as.all (Arg.ok Y) = true) (hN : 96 ≤ Y.stk)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hpre : ∀ s₀ s e, TPre Y s₀ → A s₀ s → Ent Y s₀ s as e →
      k.pre (e.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)))
    (hpub : ∀ s₀ s₀' s s' e e', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Ent Y s₀ s as e → Ent Y s₀' s' as e' →
      k.pub (e.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)) (e'.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ wB 80) s.mem s'.mem →
      (∃ e s₂, Ent Y s₀ s as e ∧ s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post (e.withRegions (rdR s₀ rB) (wrR s₀ wB as.length)) s₂) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callPR Y.sc nm c as) := by
  refine Piece.seq (setup_call as hok tt hA) ?_
  refine Piece.callRet hv.1 hv.2.1 hsp (argRs_ne hn₀ (by omega)) (esp_argRs _)
    (fun s₀ => rdR s₀ rB) (fun s₀ => wrR s₀ wB as.length)
    (fun s₀ s₁ hp ⟨_, _, h₁, _⟩ => call_hd as hp hN h₁ hst hn)
    (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, v⟩ => ⟨hpre s₀ s _ hp ha (ent_of hp hN h₁ m₁ hn v),
      (call_cov as rB wB hp h₁ hn hr hw).1, (call_cov as rB wB hp h₁ hn hr hw).2⟩)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h₁, m₁, v⟩ ⟨s', ha', h₁', m₁', v'⟩ => ?_)
    (fun s₀ s₁ s' hp ⟨s, ha, h₁, m₁, v⟩ e₁ e₂ e₃ fr ⟨s₂, m₂, g₂, post⟩ => ?_)
  · have er : rdR s₀ rB = rdR s₀' rB := List.map_congr_left fun b hb => by
      simp only [Buf.rgn, hq.ptr (List.all_eq_true.mp hr b hb)]
    have ew : wrR s₀ wB as.length = wrR s₀' wB as.length := by
      simp only [wrR, hq.E1]
      exact congrArg (· ++ _) (List.map_congr_left fun b hb => by
        simp only [Buf.rgn, hq.ptr (Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)).1])
    refine ⟨er, ew, by rw [h₁.esp, h₁'.esp, hq.E1], ?_⟩
    have := hpub s₀ s₀' s s' _ _ hp hp' hq ha ha' (ent_of hp hN h₁ m₁ hn v) (ent_of hp' hN h₁' m₁' hn v')
    exact this
  · have fr' := call_fr as wB hp hN h₁ hst hn fr
    have h' : Ctx Y s₀ s' := h₁.call e₁ e₂ e₃ fr' (call_W wB hp hN hw)
    rw [m₁] at fr'
    exact hQ s₀ s s' hp ha h' fr' ⟨_, s₂, ent_of hp hN h₁ m₁ hn v, m₂, g₂, post⟩

end

/-! ## Calls of functions that may not write their arguments -/

/-- The regions of such a call: the buffers it reads and its arguments, and those it writes. -/
abbrev rdRO (s₀ : State) (rB : List Buf) (n : Nat) : List Region := rB.map (Buf.rgn s₀) ++ [below (E1 s₀) (4 * n)]
abbrev wrRO (s₀ : State) (wB : List Buf) : List Region := wB.map (Buf.rgn s₀)

section
variable {k : Contract isa} {nm : String} {c : Prog isa} (as : List Arg) (rB wB : List Buf)

theorem call_covRO {s₀ s₁ : State} (hp : TPre Y s₀) (h₁ : Ctx Y s₀ s₁) (hn : as.length ≤ 5)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true) :
    Covers (rdRO s₀ rB as.length ++ wrRO s₀ wB)
        (s₁.rd ++ below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) ∧
      Covers (wrRO s₀ wB) (below (s₁.gpr .esp) (4 * (argRs as.length).length) :: s₁.wr) := by
  rw [argRs_len (by omega)]
  refine ⟨Covers.of_sub fun r hr' => ?_, Covers.of_sub fun r hr' => ?_⟩
  · rcases List.mem_append.mp hr' with hr' | hr'
    · rcases List.mem_append.mp hr' with hr' | hr'
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
        obtain ⟨r', h', o, e, l⟩ := Buf.within hp (List.all_eq_true.mp hr b hb) h₁.rd h₁.wr
        refine ⟨r', ?_, o, e, l⟩
        rcases List.mem_append.mp h' with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
      · rw [List.mem_singleton] at hr'; subst hr'
        exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), 0, by rw [h₁.esp]; simp, by simp⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
      obtain ⟨o, w⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)
      obtain ⟨r', h', o', e, l⟩ := Buf.withinW hp o w h₁.wr
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h'), o', e, l⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨o, w⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)
    obtain ⟨r', h', o', e, l⟩ := Buf.withinW hp o w h₁.wr
    exact ⟨r', List.mem_cons_of_mem _ h', o', e, l⟩

theorem call_frRO {s₀ s₁ : State} (hp : TPre Y s₀) (hN : 96 ≤ Y.stk) (h₁ : Ctx Y s₀ s₁) (hst : stackUse c ≤ 56)
    (hn : as.length ≤ 5) {m m' : Mem}
    (fr : Frame (wrRO s₀ wB ++ [below (s₁.gpr .esp) (4 * (argRs as.length).length + stackUse c + 4)]) m m') :
    Frame (FR s₀ wB 80) m m' := by
  rw [h₁.esp, argRs_len (by omega)] at fr
  refine fr.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp (by omega) (by omega)⟩

/-- `callPR_piece`, for a function that may not write its arguments. -/
theorem callPR_pieceRO (hv : Verified X86.target c k) (hsp : NoSp c) (hst : stackUse c ≤ 56)
    (hn₀ : as.length ≠ 0) (hn : as.length ≤ 5) (hok : as.all (Arg.ok Y) = true) (hN : 96 ≤ Y.stk)
    (hr : rB.all Y.ok = true) (hw : wB.all Y.okW = true)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs Y.sc argRegs as)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hpre : ∀ s₀ s e, TPre Y s₀ → A s₀ s → Ent Y s₀ s as e →
      k.pre (e.withRegions (rdRO s₀ rB as.length) (wrRO s₀ wB)))
    (hpub : ∀ s₀ s₀' s s' e e', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Ent Y s₀ s as e → Ent Y s₀' s' as e' →
      k.pub (e.withRegions (rdRO s₀ rB as.length) (wrRO s₀ wB))
        (e'.withRegions (rdRO s₀ rB as.length) (wrRO s₀ wB)))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → Frame (FR s₀ wB 80) s.mem s'.mem →
      (∃ e s₂, Ent Y s₀ s as e ∧ s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post (e.withRegions (rdRO s₀ rB as.length) (wrRO s₀ wB)) s₂) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callPR Y.sc nm c as) := by
  refine Piece.seq (setup_call as hok tt hA) ?_
  refine Piece.callRet hv.1 hv.2.1 hsp (argRs_ne hn₀ (by omega)) (esp_argRs _)
    (fun s₀ => rdRO s₀ rB as.length) (fun s₀ => wrRO s₀ wB)
    (fun s₀ s₁ hp ⟨_, _, h₁, _⟩ => call_hd as hp hN h₁ hst hn)
    (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, v⟩ => ⟨hpre s₀ s _ hp ha (ent_of hp hN h₁ m₁ hn v),
      (call_covRO as rB wB hp h₁ hn hr hw).1, (call_covRO as rB wB hp h₁ hn hr hw).2⟩)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h₁, m₁, v⟩ ⟨s', ha', h₁', m₁', v'⟩ => ?_)
    (fun s₀ s₁ s' hp ⟨s, ha, h₁, m₁, v⟩ e₁ e₂ e₃ fr ⟨s₂, m₂, g₂, post⟩ => ?_)
  · have er : rdRO s₀ rB as.length = rdRO s₀' rB as.length := by
      simp only [rdRO, hq.E1]
      exact congrArg (· ++ _) (List.map_congr_left fun b hb => by
        simp only [Buf.rgn, hq.ptr (List.all_eq_true.mp hr b hb)])
    have ew : wrRO s₀ wB = wrRO s₀' wB := List.map_congr_left fun b hb => by
      simp only [Buf.rgn, hq.ptr (Lay.okW_iff.mp (List.all_eq_true.mp hw b hb)).1]
    refine ⟨er, ew, by rw [h₁.esp, h₁'.esp, hq.E1], ?_⟩
    exact hpub s₀ s₀' s s' _ _ hp hp' hq ha ha' (ent_of hp hN h₁ m₁ hn v) (ent_of hp' hN h₁' m₁' hn v')
  · have fr' := call_frRO as wB hp hN h₁ hst hn fr
    have h' : Ctx Y s₀ s' := h₁.call e₁ e₂ e₃ fr' (call_W wB hp hN hw)
    rw [m₁] at fr'
    exact hQ s₀ s s' hp ha h' fr' ⟨_, s₂, ent_of hp hN h₁ m₁ hn v, m₂, g₂, post⟩

end

end VG.Proof.MlDsa.X86.KeyGen

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen (Arg)

variable {Y : Lay}

/-- What a callee's precondition needs of a buffer it is passed. -/
theorem Ent.buf {s₀ s e : State} {as : List Arg} (he : Ent Y s₀ s as e) (hp : TPre Y s₀) (hN : 96 ≤ Y.stk)
    (hn : as.length ≤ 5) {b : Buf} (hb : Y.ok b = true) {K : Nat} (hK : K ≤ 56) :
    (b.rgn s₀).Disjoint (below (E1 s₀) (4 * as.length)) ∧
      (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (b.rgn s₀) ∧
      (⟨(e.gpr .esp).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (b.rgn s₀) ∧
      (b.ptr s₀).toNat + b.len ≤ 2 ^ 32 :=
  ⟨(he.rgn hp hN hn hb hK).1, (he.rgn hp hN hn hb hK).2.1, (he.rgn hp hN hn hb hK).2.2, Buf.fit hp hb⟩

end VG.Proof.MlDsa.X86.KeyGen
