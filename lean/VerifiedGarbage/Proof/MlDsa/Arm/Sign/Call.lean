import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Lay
import VerifiedGarbage.Proof.MlKem.Arm.Keccak
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on ARMv7: calls of verified code

Untrusted: everything here is checked by Lean. `setArgs as` moves each
argument (a pointer or an immediate) into its register (`r0`–`r3`, `r12`,
`lr`): afterwards each holds the argument's value in the state before the
moves, and nothing else changed but those registers (`setArgs_ok`). A
primitive the function calls is any code verified against its shared
contract (`Spec/MlDsa/Poly.lean`) for some stack of `S` bytes that, with
the `F` bytes of the frame the call pushes, fits in the `D` bytes the
function gives its calls, and whose own frames use at most `S` bytes
(`Callee`). A call with at most four arguments (`callR_ok`), or with its
fifth and sixth pushed in a frame (`callS_ok`), leaves the permissions and
the callee-saved registers as they were, and changes memory only within the
buffers it writes and the `D` bytes of stack below the stack pointer. Two
runs of it leak the same when the callee's public data agree
(`callR_tr`, `callS_tr`), and a callee whose result is public in its own
runs (`RetPub`) returns the same in both (`callRRet_tr`, `callSRet_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (push2_frame addr_sub view_gpr)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa

/-! ## Registers a block writes -/

/-- `s'` differs from `s` only in the registers `rs` (and the flags). -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) : Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

theorem argRegs_cs : ∀ r ∈ preserved, r ≠ .lr → r ∉ argRegs := by decide

theorem Keep.cs {s s' : State} (h : Keep argRegs s s') : CS s s' := fun r hr hl => h.gpr r (argRegs_cs r hr hl)

/-! ## Moves -/

theorem movi_val (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  have e1 : BitVec.ofNat 16 (v / 65536) = (BitVec.ofNat 32 v).extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have e2 : BitVec.ofNat 16 v = (BitVec.ofNat 32 v).extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [e1, e2]; exact movw_movt _

theorem movi_ok (d : Reg) (v : Nat) (s : State) :
    WP isa (.block (movi d v)) s fun s1 => s1.gpr d = BitVec.ofNat 32 v ∧ Keep [d] s s1 := by
  run_block [movi]
  refine ⟨by simp [movi_val], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp [hr]

theorem lea_ok (d : Reg) (p : Ptr) (hd : p.1 ≠ d) (s : State) :
    WP isa (.block (lea d p)) s fun s1 => s1.gpr d = s.gpr p.1 + BitVec.ofNat 32 p.2 ∧ Keep [d] s s1 := by
  run_block [lea, movi, hd]
  refine ⟨by simp [movi_val, BitVec.add_comm], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp [hr]

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.Arm.Sign.Arg.val (s : State) : Arg → BitVec 32
  | .ptr p => s.gpr p.1 + BitVec.ofNat 32 p.2
  | .imm v => BitVec.ofNat 32 v

/-- A pointer in a register of `bases`, or an immediate. -/
def _root_.VG.Impl.MlDsa.Arm.Sign.Arg.ok : Arg → Bool
  | .ptr p => decide (p.1 ∈ bases)
  | .imm _ => true

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs) (s : State) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ Keep [d] s s1 := by
  cases a with
  | ptr p =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact lea_ok d p (fun e => by revert ha hd; rw [e]; cases d <;> decide) s
  | imm v => exact movi_ok d v s

theorem setArgsTo_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs) →
    as.all Arg.ok = true → ∀ s : State,
    WP isa (.block (setArgsTo ds as)) s fun s1 => (∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ Keep ds s s1
  | [], _, _, _, _, s => WP.block_nil ⟨fun _ h => by simp at h, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s => WP.block_nil ⟨fun _ h => by simp at h, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [setArgsTo, List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha.1 (hd d (List.mem_cons_self ..)) s) fun s1 ⟨h1, k1⟩ => ?_
    refine WP.mono (setArgsTo_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1)
      fun s2 ⟨h2, k2⟩ => ⟨fun da hda => ?_, (k1.mono fun r hr => by simp_all).trans (k2.mono fun r hr => by simp [hr])⟩
    -- The values in `s1` are those in `s`: the moves keep the bases.
    have hval : ∀ b : Arg, b.ok = true → b.val s1 = b.val s := fun b hb => by
      cases b with
      | ptr p =>
        simp only [Arg.ok, decide_eq_true_eq] at hb
        simp only [Arg.val]
        have hdb : d ∈ argRegs := hd d (List.mem_cons_self ..)
        rw [k1.gpr p.1 (by simp only [List.mem_singleton]; intro e; revert hb hdb; rw [e]; cases d <;> decide)]
      | imm v => rfl
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr _ hn.1, h1]
    · have := List.of_mem_zip hda
      rw [h2 da hda, hval da.2 (List.all_eq_true.mp ha.2 _ this.2)]

theorem argRegs6_nodup : argRegs6.Nodup := by decide

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧
      Keep argRegs s s1 :=
  setArgsTo_ok argRegs6 as argRegs6_nodup (fun _ h => h) ha s

theorem setArgsTo_nomem (ds : List Reg) (as : List Arg) : ∀ i ∈ setArgsTo ds as, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [setArgsTo, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, _, hi⟩ := hi
  cases a with
  | ptr p =>
    simp only [Arg.mov, lea, movi, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  | imm v =>
    simp only [Arg.mov, movi, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

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

/-- A relation of the final states from facts each run proves of its own. -/
theorem postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-! ## Callees -/

/-- Code verified against the contract `k S` for a stack of `S` bytes, that
with the `F` bytes of the frame its calls push fits in `D`, and whose frames
use at most `S` bytes. -/
structure Callee (k : Nat → Contract isa) (F D : Nat) (c : Prog isa) where
  /-- The stack its contract gives it. -/
  S : Nat
  hS : S + F ≤ D
  ver : Verified Arm.target c (k S)
  su : stackUse c ≤ S

/-- The result of `c` (`r0`) is the same in two runs from states that
satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn2 {a b : Arg} {s s1 : State} (h : ArgsIn [a, b] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6])⟩

theorem argsIn3 {a b c : Arg} {s s1 : State} (h : ArgsIn [a, b, c] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6])⟩

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s ∧
      s1.gpr .r12 = e.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6]), h (.r12, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s ∧
      s1.gpr .r12 = e.val s ∧ s1.gpr .lr = f.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6]), h (.r12, e) (by simp [argRegs6]), h (.lr, f) (by simp [argRegs6])⟩

/-! ## The stack -/

theorem belowA_mono {sp : BitVec 32} {a b : Nat} (hab : a ≤ b) {W : List Region} {m m' : Mem}
    (h : Frame (W ++ [belowA sp a]) m m') : Frame (W ++ [belowA sp b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub hab⟩

/-- The argument on the stack of a call with a frame: the word at the
stack pointer of the callee. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 4⟩

/-! ## Calls with their arguments in registers -/

/-- The moves of the arguments, then a call of verified code. -/
theorem callR_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : stackUse c ≤ D) {as : List Arg} (ha : as.all Arg.ok = true) {s : State} (hsp : D ≤ s.sp.toNat)
    {rd wr : List Region}
    (hpre : ∀ s1, ArgsIn as s s1 → Keep argRegs s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callR n c as) s fun s' => PostB D s s' wr ∧ CS s s' ∧
      ∃ s1, ArgsIn as s s1 ∧ Keep argRegs s s1 ∧ k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (setArgs_ok as ha s) fun s1 ⟨hA, k1⟩ => ?_)
  refine WP.callF hv (hpre s1 hA k1) (by rw [k1.rd, k1.wr]; exact hc) (by rw [k1.wr]; exact hw)
    (by rw [k1.sp]; omega) fun s' hrd hwr hsp' hf hcs hpost => ?_
  have hcs' : CS s s' := CS.trans k1.cs hcs
  rw [k1.mem, k1.sp] at hf
  exact ⟨⟨hrd.trans k1.rd, hwr.trans k1.wr, fun r hr => hcs' r (bases_cs r hr).1 (bases_cs r hr).2,
    hsp'.trans k1.sp, belowA_mono hsu hf⟩, hcs', s1, hA, k1, hpost⟩

/-! ## Calls with arguments on the stack -/

theorem frame8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩ : Region) =
      belowA s.sp 8 := by
  simp only [belowA, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  rw [addr_sub hsp]

theorem ne12_pres : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r12 := by decide

theorem argR_contains {s : State} {x : Addr} {m : Nat} (h : (argR s).Contains x m) :
    (belowA s.sp 8).Contains x m := by
  simp only [Region.Contains, belowA] at h ⊢; omega

theorem sp_sub8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : (sp - BitVec.ofNat 32 8).toNat = sp.toNat - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem argR_sub (s : State) : Region.Sub (argR s) (belowA s.sp 8) := fun x hx => by
  simp only [Region.Contains, belowA] at hx ⊢; omega

/-- The moves of the arguments, then a call of verified code in a frame that
pushes its fifth and sixth arguments (`r12`, `lr`). -/
theorem callS_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : 8 + stackUse c ≤ D) {as : List Arg} (ha : as.all Arg.ok = true) {s : State} (hsp : D ≤ s.sp.toNat)
    {rd wr : List Region}
    (hpre : ∀ s1, ArgsIn as s s1 → Keep argRegs s s1 →
      k.pre ((pushed [.r12, .lr] s1).callEntry.withRegions (rd ++ [argR s]) wr))
    (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callS n c as) s fun s' => PostB D s s' wr ∧ CS s s' ∧
      ∃ s1, ArgsIn as s s1 ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .r12 → s₂.gpr r = s'.gpr r) ∧
        k.post ((pushed [.r12, .lr] s1).callEntry.withRegions (rd ++ [argR s]) wr)
          (s₂.withRegions (rd ++ [argR s]) wr) := by
  have h8 : 8 ≤ s.sp.toNat := by omega
  refine WP.seq (WP.mono (setArgs_ok as ha s) fun s1 ⟨hA, k1⟩ => ?_)
  have h8' : 8 ≤ s1.sp.toNat := by rw [k1.sp]; exact h8
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8') (by decide) ?_
  have hwp : (pushed [.r12, .lr] s1).wr = belowA s.sp 8 :: s.wr := by
    rw [VG.Arm.pushed_wr, frame8 h8', k1.wr, k1.sp]
  refine WP.callF hv (hpre s1 hA k1) (fun x m hx => ?_) (fun x m hx => ?_) ?_ fun s₂ hrd hwr hsp₂ hf hcs hpost => ?_
  · rw [VG.Arm.pushed_rd, hwp, k1.rd]
    rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), argR_contains hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · rw [hwp]
    obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [VG.Arm.pushed_sp, k1.sp, show BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 from rfl,
      sp_sub8 h8]; omega
  · have hcs₂ : CS s s₂ := fun r hr hl => by rw [hcs r hr hl, VG.Arm.pushed_gpr]; exact k1.cs r hr hl
    have hsp₂' : s₂.sp = s.sp - BitVec.ofNat 32 8 := by rw [hsp₂, VG.Arm.pushed_sp, k1.sp]; rfl
    have f₁ := push2_frame h8'
    rw [k1.mem] at f₁
    have hsu' : 8 + stackUse c ≤ s.sp.toNat := by omega
    refine ⟨⟨by simp only [popped_rd, hrd, VG.Arm.pushed_rd, k1.rd], by simp only [popped_wr, hwr, hwp, List.tail_cons],
      fun r hr => (popped_gpr (ne12_pres r (bases_cs r hr).1 (bases_cs r hr).2) _ _).trans
        (hcs₂ r (bases_cs r hr).1 (bases_cs r hr).2), by rw [popped_sp, hsp₂']; exact BitVec.sub_add_cancel _ _, ?_⟩,
      fun r hr hl => by rw [popped_gpr (ne12_pres r hr hl)]; exact hcs₂ r hr hl,
      s1, hA, k1, s₂, rfl, fun r hr => (popped_gpr hr _ _).symm, hpost⟩
    rw [popped_mem]
    rw [VG.Arm.pushed_sp, k1.sp] at hf
    refine (f₁.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      show ∃ r', r' ∈ wr ++ [belowA s.sp D] ∧ (belowA s1.sp 8).Sub r'
      rw [k1.sp]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun x h => belowA_sub (show 8 + stackUse c ≤ D by omega) x (belowA_push hsu' x h)⟩

/-! ## Two runs of a call -/

/-- A call of verified code leaks the same in two runs whose narrowed entry
states satisfy its precondition and agree on its public data; and its
result is the same if it is public in its own runs (`RetPub`). -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 ∨ True)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁⟩ := trace_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂⟩ := trace_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ n₁ n₂
      exact ⟨by simp only [ht], trivial⟩

/-- The run of a call narrowed to the regions its contract gives it: the
same trace, and the same registers. -/
theorem narrow_run {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} {t : List Leak} {s' : State}
    (hpre : k.pre (s.withRegions rd wr)) (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨n₁, x₁, g₁⟩ := narrow_run hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow_run hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      rw [ret_eq r₁, ret_eq r₂]
      exact ⟨by simp only [ht], show _ = _ by rw [← g₁, ← g₂]; exact hrax⟩

/-- Constant time, as `RelCT.callEx` needs it. -/
theorem ct_or {k : Contract isa} {c : Prog isa} (hct : ConstantTime isa k.pre k.pub c) :
    RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 ∨ True :=
  fun _ _ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ⟨hct _ _ _ _ _ _ h₁ h₂ hp e₁ e₂, .inr trivial⟩

/-- The moves of the arguments, from two related states. -/
theorem setArgs_rel {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop} :
    RelCT isa P (.block (setArgs as)) fun x1 y1 => ∃ x y, P x y ∧ (ArgsIn as x x1 ∧ Keep argRegs x x1) ∧
      (ArgsIn as y y1 ∧ Keep argRegs y y1) :=
  RelCT.mono (RelCT.wpDep (block_nomem_tr (setArgsTo_nomem _ _))
    (fun x y _ => ⟨setArgs_ok as ha x, setArgs_ok as ha y⟩)) (fun _ _ h => h)
    fun _ _ ⟨_, x, y, hp, h1, h2⟩ => ⟨x, y, hp, h1, h2⟩

/-- Region lists for the two runs of a call. -/
abbrev Regs2 (k : Contract isa) (x1 y1 : State) : Prop := ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
  k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
  k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
  Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧ Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr

theorem callR_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k x1 y1) :
    RelCT isa P (callR n c as) fun _ _ => True :=
  RelCT.seq (setArgs_rel ha) (RelCT.callEx hv (ct_or hct) fun _ _ ⟨x, y, hp, h1, h2⟩ => hP x y _ _ hp h1 h2)

theorem callRRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k x1 y1) :
    RelCT isa P (callR n c as) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 :=
  RelCT.seq (setArgs_rel ha) (RelCT.callRet hv hr fun _ _ ⟨x, y, hp, h1, h2⟩ => hP x y _ _ hp h1 h2)

/-- A frame of the stack arguments around a call whose runs relate by `Q`
(on `r0`, which the pop does not change). -/
theorem RelCT.frame12 {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed [.r12, .lr] s₁ ∧ b = pushed [.r12, .lr] s₂) body
      fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0) :
    RelCT isa P (.frame (.push [.r12, .lr]) body (.pop .r12 8)) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain ⟨rfl, -⟩ := VG.Arm.push_pushed' p₁
      obtain ⟨rfl, -⟩ := VG.Arm.push_pushed' p₂
      obtain ⟨ht, h0⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      have hq₁ := pop_eq q₁
      have hq₂ := pop_eq q₂
      have e := hsp _ _ hp
      refine ⟨?_, ?_⟩
      · rw [ht]
        simp only [addrs, hq₁.2.2.2.2.1, hq₂.2.2.2.2.1, VG.Arm.pushed_sp, e]
      · show _ = _
        rw [hq₁.2.2.2.1 .r0 (by decide), hq₂.2.2.2.1 .r0 (by decide)]; exact h0

theorem callS_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k (pushed [.r12, .lr] x1) (pushed [.r12, .lr] y1)) :
    RelCT isa P (callS n c as) fun _ _ => True :=
  RelCT.seq (setArgs_rel ha) (VG.Arm.RelCT.frame
    (fun _ _ ⟨x, y, hp, h1, h2⟩ => by rw [h1.2.sp, h2.2.sp]; exact hsp x y hp)
    (RelCT.callEx hv (ct_or hct) fun _ _ ⟨x1, y1, ⟨x, y, hp, h1, h2⟩, ea, eb⟩ => by
      rw [(VG.Arm.push_pushed' ea).1, (VG.Arm.push_pushed' eb).1]; exact hP x y x1 y1 hp h1 h2))

theorem callSRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k (pushed [.r12, .lr] x1) (pushed [.r12, .lr] y1)) :
    RelCT isa P (callS n c as) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 :=
  RelCT.seq (setArgs_rel ha) (RelCT.frame12
    (fun _ _ ⟨x, y, hp, h1, h2⟩ => by rw [h1.2.sp, h2.2.sp]; exact hsp x y hp)
    (RelCT.callRet hv hr fun _ _ ⟨x1, y1, ⟨x, y, hp, h1, h2⟩, ea, eb⟩ => ea ▸ eb ▸ hP x y x1 y1 hp h1 h2))

end VG.Proof.MlDsa.Arm.Sign
