import VerifiedGarbage.Impl.MlDsa.X86.Sign.Sign
import VerifiedGarbage.Proof.MlKem.X86.TopKeep
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.MlDsa.Sign.Vals
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA signing on x86 (32-bit): the setting of the proof

The function is proven as ML-KEM's top-level functions on x86 are
(`Proof/MlKem/X86/Top*.lean`), piece by piece (`Piece`), from the layout of
its arguments (`Y`: `sk`, `mu`, `rnd`, `sig`, `scratch`, and 96 bytes of
stack), with `Ctx` holding between the pieces. Two runs are related (`SPub`)
by the pointers and what signing may leak (`signLeakT`, which is `signLeak`);
a piece of ML-KEM's, whose runs are related by the pointers alone, is one of
these (`lift`).

Blocks whose addresses depend only on `esp` and `esi`, which they do not
write (`esOk`), leak the same in runs that agree on both (`blk_piece`): the
moves of a call's arguments (`setArgs`, `setup_piece`) and the stores to
`scratch`. A loop runs a number of iterations that depends on the initial
state, the same in related runs (`loopN`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The layout and the related runs -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- The stack signing uses below its return address. -/
abbrev STK : Nat := 96

/-- `sk`, `mu`, `rnd` (read), `sig` and `scratch` (written); 96 bytes of stack. -/
def Y (p : Params) : Lay := ⟨[(p.skLen, false), (64, false), (32, false), (p.sigLen, true), (scrLen p, true)], SC, STK⟩

/-- Nothing, as the leakage of ML-KEM's pieces. -/
abbrev lk0 : State → List Byte := fun _ => []

section
variable (p : Params) (s₀ : State)
/-- `sk`, `μ` and `rnd`, on entry. -/
abbrev skOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ (bSk 0 p.skLen)) p.skLen
abbrev muOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ bMu) 64
abbrev rndOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ bRnd) 32
end

/-- Two runs with the same pointers and the same leakage. -/
def SPub (p : Params) (s₀ s₀' : State) : Prop :=
  TPub (Y p) lk0 s₀ s₀' ∧ signLeakT p (skOf p s₀) (muOf s₀) (rndOf s₀) = signLeakT p (skOf p s₀') (muOf s₀') (rndOf s₀')

/-- The pieces of the proof. -/
abbrev SP (p : Params) (A B : State → State → Prop) (c : Prog isa) : Prop := Piece (TPre (Y p)) (SPub p) A B c

theorem lift {p : Params} {A B : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (Y p)) (TPub (Y p) lk0) A B c) : SP p A B c :=
  h.pre_mono (fun _ h => h) fun _ _ _ _ h => h.1

theorem SPub.t {p : Params} {s₀ s₀' : State} (h : SPub p s₀ s₀') : TPub (Y p) lk0 s₀ s₀' := h.1

theorem Y_sc (p : Params) : (Y p).sc = SC := rfl

/-! ## Blocks that address through `esp` and `esi` -/

/-- A base register `esp` or `esi`. -/
def esBase (m : MemOp) : Bool := m.base == .esp || m.base == .esi

/-- The addresses of `i` depend only on `esp` and `esi`. -/
def esAddr : Instr → Bool
  | .mov _ (.mem m) | .alu _ _ (.mem m) => esBase m
  | .mov .. | .alu .. => true
  | .store m _ | .store8 m _ | .movzx8 _ m => esBase m
  | .shift .. | .bswap _ | .mul _ => true
  | .push _ | .pop .. | .movdquLoad .. | .movdquStore .. | .xop .. => false

/-- `i` writes neither `esp` nor `esi`, and addresses through them. -/
def esOk (i : Instr) : Bool := !Taint.clobbers i .esp && !Taint.clobbers i .esi && esAddr i

theorem esBase_ea {m : MemOp} (h : esBase m = true) {s s' : State} (h₁ : s.gpr .esp = s'.gpr .esp)
    (h₂ : s.gpr .esi = s'.gpr .esi) : s.ea m = s'.ea m := by
  simp only [esBase, Bool.or_eq_true, beq_iff_eq] at h
  simp only [State.ea]
  rcases h with e | e <;> rw [e] <;> simp only [h₁, h₂]

theorem esAddr_addrs {i : Instr} (h : esAddr i = true) {s s' : State} (h₁ : s.gpr .esp = s'.gpr .esp)
    (h₂ : s.gpr .esi = s'.gpr .esi) : addrs i s = addrs i s' := by
  cases i with
  | mov d src =>
    cases src with
    | mem m => simp only [esAddr] at h; simp only [addrs, srcAddrs, esBase_ea h h₁ h₂]
    | _ => rfl
  | alu op d src =>
    cases src with
    | mem m => simp only [esAddr] at h; simp only [addrs, srcAddrs, esBase_ea h h₁ h₂]
    | _ => rfl
  | store m r => simp only [esAddr] at h; simp only [addrs, esBase_ea h h₁ h₂]
  | store8 m r => simp only [esAddr] at h; simp only [addrs, esBase_ea h h₁ h₂]
  | movzx8 d m => simp only [esAddr] at h; simp only [addrs, esBase_ea h h₁ h₂]
  | shift | bswap | mul => rfl
  | push | pop | movdquLoad | movdquStore | xop => simp [esAddr] at h

theorem esOk_block : ∀ {is : List Instr}, is.all esOk = true →
    RelCT isa (fun s s' => s.gpr .esp = s'.gpr .esp ∧ s.gpr .esi = s'.gpr .esi) (.block is) fun _ _ => True := by
  intro is h s₁ s₂ t₁ t₂ s₁' s₂' ⟨e₁, e₂⟩ x₁ x₂
  rw [Exec.block_iff] at x₁ x₂
  refine ⟨?_, trivial⟩
  induction is generalizing s₁ s₂ t₁ t₂ with
  | nil => simp [execBlock] at x₁ x₂; rw [x₁.2, x₂.2]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases hu₁ : exec i s₁ with
    | none => simp only [execBlock, hu₁] at x₁; cases x₁
    | some u₁ =>
    cases hu₂ : exec i s₂ with
    | none => simp only [execBlock, hu₂] at x₂; cases x₂
    | some u₂ =>
    simp only [execBlock, hu₁, hu₂] at x₁ x₂
    obtain ⟨⟨v₁, w₁⟩, y₁, z₁⟩ := Option.map_eq_some_iff.mp x₁
    obtain ⟨⟨v₂, w₂⟩, y₂, z₂⟩ := Option.map_eq_some_iff.mp x₂
    simp only [Prod.mk.injEq] at z₁ z₂
    rw [← z₁.2, ← z₂.2]
    have hi := h.1
    simp only [esOk, Bool.and_eq_true, Bool.not_eq_true'] at hi
    have g₁ := exec_gpr hi.1.1 hu₁
    have g₂ := exec_gpr hi.1.1 hu₂
    have g₃ := exec_gpr hi.1.2 hu₁
    have g₄ := exec_gpr hi.1.2 hu₂
    rw [esAddr_addrs hi.2 e₁ e₂,
      ih h.2 u₁ u₂ w₁ w₂ (by rw [g₁, g₂, e₁]) (by rw [g₃, g₄, e₂]) (z₁.1 ▸ y₁) (z₂.1 ▸ y₂)]

/-- A block that addresses through `esp` and `esi`, from `Ctx`. -/
theorem blk_piece {p : Params} {A B : State → State → Prop} {is : List Instr}
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hw : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → WP isa (.block is) s (B s₀)) (h : is.all esOk = true) :
    SP p A B (.block is) where
  wp := hw
  ct s₀ s₀' hp hp' hq := (esOk_block h).mono (fun s s' ⟨a, a'⟩ => by
    have c := hA _ _ hp a
    have c' := hA _ _ hp' a'
    exact ⟨by rw [c.esp, c'.esp, hq.t.E1], by rw [c.esi, c'.esi, hq.t.sc hp]⟩) fun _ _ h => h

/-! ## The moves of a call's arguments -/

/-- The value of an argument. -/
def argV (s₀ : State) : Arg → BitVec 32
  | .buf b => b.ptr s₀
  | .imm v => BitVec.ofNat 32 v

/-- An argument whose buffer lies in its argument. -/
def argOk (Y : Lay) : Arg → Bool
  | .buf b => Y.ok b
  | .imm _ => true

theorem Arg.mov_esOk {d : Reg} (hd : d ≠ .esp) (hd' : d ≠ .esi) (a : Arg) : (a.mov d).all esOk = true := by
  cases a with
  | buf b =>
    simp only [Arg.mov, ptrTo]
    split <;> cases d <;> simp_all [esOk, esAddr, esBase, Taint.clobbers, Taint.dst, at_]
  | imm v => cases d <;> simp_all [Arg.mov, esOk, esAddr, Taint.clobbers, Taint.dst]

theorem setArgs_esOk : ∀ {as : List (Reg × Arg)}, (∀ x ∈ as, x.1 ≠ .esp ∧ x.1 ≠ .esi) →
    (setArgs as).all esOk = true
  | [], _ => rfl
  | (d, a) :: as, h => by
    simp only [setArgs, List.all_append, Bool.and_eq_true]
    exact ⟨Arg.mov_esOk (h _ (List.mem_cons_self ..)).1 (h _ (List.mem_cons_self ..)).2 a,
      setArgs_esOk fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem argMov_ok {p : Params} {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {d : Reg} {a : Arg}
    (ha : argOk (Y p) a = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = argV s₀ a → WP isa (.block is) s' Q) :
    WP isa (.block (a.mov d ++ is)) s Q := by
  cases a with
  | buf b => exact ptrTo_ok hp h ha k
  | imm v => exact wp_movi k

/-- The values of the arguments in their registers. -/
def ArgsAre (s₀ s : State) (as : List Arg) : Prop :=
  ∀ i < as.length, s.gpr (argRegs.getD i .eax) = argV s₀ (as.getD i (.imm 0))

theorem setArgs_ok {p : Params} {s₀ : State} (hp : TPre (Y p) s₀) :
    ∀ (as : List (Reg × Arg)) {s : State}, Ctx (Y p) s₀ s → (as.map Prod.fst).Nodup →
      (∀ x ∈ as, x.1 ≠ .esp ∧ x.1 ≠ .esi ∧ argOk (Y p) x.2 = true) → ∀ {Q : State → Prop},
      (∀ s', Ctx (Y p) s₀ s' → s'.mem = s.mem → (∀ r, r ∉ as.map Prod.fst → s'.gpr r = s.gpr r) →
        (∀ x ∈ as, s'.gpr x.1 = argV s₀ x.2) → Q s') →
      WP isa (.block (setArgs as)) s Q
  | [], s, h, _, _, Q, k => WP.block_nil_iff.mpr (k s h rfl (fun _ _ => rfl) fun _ hx => absurd hx List.not_mem_nil)
  | (d, a) :: as, s, h, hnd, hok, Q, k => by
    have h0 := hok _ (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold setArgs
    refine argMov_ok hp h h0.2.2 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by simp [h0.1.symm]) (by simp [h0.2.1.symm])
    refine setArgs_ok hp as c₁ hnd.2 (fun x hx => hok x (List.mem_cons_of_mem _ hx)) fun s' c' m' g' v' => ?_
    refine k s' c' (m'.trans o₁.mem) (fun r hr => ?_) fun x hx => ?_
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [g' r hr.2, o₁.gpr r (by simp [hr.1])]
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [g' _ hnd.1, v₁]
      · exact v' x hx

theorem zip_mem {as : List Arg} (hn : as.length ≤ 5) {i : Nat} (hi : i < as.length) :
    (argRegs.getD i .eax, as.getD i (.imm 0)) ∈ argRegs.zip as := by
  have h1 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp only [List.length_zip]; omega, ?_⟩
  simp [List.getElem_zip, List.getD_eq_getElem?_getD, hi, List.getElem?_eq_getElem h1]

theorem argRegs_ne : ∀ r ∈ argRegs, r ≠ .esp ∧ r ≠ .esi := by decide

/-- The moves of the arguments `as`. -/
theorem setup_piece' {p : Params} {A : State → State → Prop} (as : List Arg) (hn : as.length ≤ 5)
    (hok : ∀ a ∈ as, argOk (Y p) a = true) (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s) :
    SP p A (fun s₀ s₁ => ∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ ArgsAre s₀ s₁ as)
      (.block (setArgs (argRegs.zip as))) := by
  have hne : ∀ x ∈ argRegs.zip as, x.1 ≠ .esp ∧ x.1 ≠ .esi := fun x hx => argRegs_ne _ (List.of_mem_zip hx).1
  refine blk_piece hA (fun s₀ s hp ha => ?_) (setArgs_esOk hne)
  refine setArgs_ok hp _ (hA _ _ hp ha) ?_ (fun x hx => ⟨(hne x hx).1, (hne x hx).2, hok _ (List.of_mem_zip hx).2⟩)
    fun s' c' m' _ v' => ⟨s, ha, c', m', fun i hi => v' _ (zip_mem hn hi)⟩
  match as, hn with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _ => simp [argRegs]

theorem argPush_len {n : Nat} (hn : n ≤ 5) : (argPush n).length = n := by
  simp only [argPush, List.length_reverse, List.length_take, argRegs, List.length_cons, List.length_nil]; omega

theorem esp_nmem_argPush (n : Nat) : Reg.esp ∉ argPush n := fun h => by
  simp only [argPush, List.mem_reverse] at h
  exact (argRegs_ne _ (List.mem_of_mem_take h)).1 rfl

theorem argPush_ne {n : Nat} (hn : 0 < n) : argPush n ≠ [] := by
  cases n with
  | zero => omega
  | succ n => simp [argPush, argRegs]

/-- The callee's argument `i` is the `i`-th argument register. -/
theorem argPush_arg {n : Nat} (hn : n ≤ 5) {s : State} (hfit : 4 * n + 4 ≤ (s.gpr .esp).toNat) {i : Nat}
    (hi : i < n) : arg (pushed (argPush n) s).callEntry i = s.gpr (argRegs.getD i .eax) := by
  have hl := argPush_len hn
  rw [callEntry_arg (by rw [hl]; exact hfit) (esp_nmem_argPush n) (by rw [hl]; exact hi)]
  congr 1
  have h1 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega
  simp only [argPush, List.getElem_reverse, List.getElem_take, hl]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
  congr 1
  simp only [List.length_take, argRegs, List.length_cons, List.length_nil]
  omega

/-! ## Loops of a number of iterations that depends on the initial state -/

theorem loopN {Pre : State → Prop} {Pub : State → State → Prop} {body : Prog isa} {cnd : Cond}
    (N : State → Nat) (Inv : Nat → State → State → Prop) (hN : ∀ s₀, Pre s₀ → 0 < N s₀)
    (hNp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → N s₀ = N s₀')
    (hb : ∀ k, Piece Pre Pub (fun s₀ s => Inv k s₀ s ∧ k < N s₀)
      (fun s₀ s => Inv (k + 1) s₀ s ∧ isa.eval cnd s = some (decide (k + 1 < N s₀))) body) :
    Piece Pre Pub (Inv 0) (fun s₀ s => Inv (N s₀) s₀ s) (.loop body cnd) where
  wp s₀ s h₀ ha := by
    refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ Inv k s₀ s)
      (fun n s hi => ?_) (N s₀) s ⟨0, (Nat.sub_zero _).symm, hN s₀ h₀, ha⟩
    obtain ⟨k, hn, hk, hi⟩ := hi
    refine ((hb k).wp _ _ h₀ ⟨hi, hk⟩).mono fun s' ⟨hi', hc⟩ => ?_
    by_cases h : k + 1 < N s₀
    · exact .inr ⟨by rw [hc, decide_eq_true h], N s₀ - (k + 1), by omega, k + 1, rfl, h, hi'⟩
    · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N s₀ = k + 1 by omega]; exact hi'⟩
  ct s₀ s₀' h₀ h₀' hp := by
    have eN := hNp _ _ h₀ h₀' hp
    have := RelCT.loop (M := isa) (body := body) (c := cnd) (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ Inv k s₀ s ∧ Inv k s₀' s')
      (fun n => by
        refine RelCT.exists_ fun k => ?_
        by_cases hk : n = N s₀ - k ∧ k < N s₀
        · refine ((hb k).ct' h₀ h₀' hp).mono (fun s s' ⟨_, _, a, a'⟩ => ⟨⟨a, hk.2⟩, a', eN ▸ hk.2⟩) ?_
          rintro s s' ⟨⟨i₁, c₁⟩, i₂, c₂⟩
          refine ⟨by rw [c₁, c₂, eN], fun _ => trivial, fun h => ?_⟩
          rw [c₁, Option.some.injEq, decide_eq_true_iff] at h
          exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, h, i₁, i₂⟩
        · exact RelCT.of_false fun s s' ⟨h1, h2, _⟩ => hk ⟨h1, h2⟩) (N s₀)
    exact this.mono (fun s s' ⟨a, a'⟩ => ⟨0, (Nat.sub_zero _).symm, hN s₀ h₀, a, a'⟩) fun _ _ h => h

end VG.Proof.MlDsa.X86.Sign
