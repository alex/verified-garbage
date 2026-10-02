import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Sha3.Compl
import VerifiedGarbage.Impl.Sha3.X86_64

/-!
# Keccak-f[1600] on x86-64: a round, by evaluation

A round (`round s d k`) is checked by evaluating its code over the ANF
domain (`Bitslice.Anf`, with `Straight.eval`): the lanes of the state at
`s`, as stored (complemented, `Compl.cmpl`), are atoms `0–24`, and row 4 of
it is in `rowReg` on entry. The one instruction the evaluator does not
model, ι's load of the round constant (`[rsi + r15 + …]`, a third memory
area), splits the round in two: it XORs atom 25 into `r9`. `check` then
compares what the round stores at `d`, and leaves in `rowReg`, with the
round computed from the specification (`Compl.specP`), and `round_ok`
turns that into a statement about the machine. The two rounds of an
iteration (`check₀`, `check₁`) are each checked once.

The prologue and the epilogue complement the lanes `complLanes` in place
(`complement`), which is checked the same way (`slots_ok`).
-/

namespace VG.Proof.Sha3.X86_64.Round

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice.Anf VG.Impl.Sha3.X86_64
open VG.Proof.Sha3.Compl (specP)

/-- The registers of row 4 between rounds. -/
def rowReg (x : Nat) : Reg := [Reg.rax, .rbx, .rcx, .rdx, .rbp].getD x .rax

/-- The output state at `d` (slots), the input state at `s` (external words). -/
def cfg (s d : Reg) : Cfg := { base := d, slots := 25, ext := s, exts := 25 }

def ext (k : Nat) : Option Poly := some (atom k)

/-- On entry, row 4 of the input in `rowReg`. -/
def env₀ : Straight.Env Poly :=
  { reg := fun r => if r = .rax then some (atom 20) else if r = .rbx then some (atom 21)
      else if r = .rcx then some (atom 22) else if r = .rdx then some (atom 23)
      else if r = .rbp then some (atom 24) else none
    slot := fun _ => none }

/-- The output, and row 4 of it in `rowReg`. -/
def post (e : Straight.Env Poly) : Bool :=
  (List.range 25).all (fun j => e.slot j == some (specP j)) &&
    (List.range 5).all fun x => e.reg (rowReg x) == some (specP (20 + x))

/-- The round from `s` to `d`, with ι (the round constant, atom 25, XORed
into `r9`) between `roundA` and `roundB`. -/
def check (s d : Reg) : Bool :=
  match Straight.eval anf (cfg s d) ext (roundA s) env₀ with
  | none => false
  | some e₁ => match e₁.reg .r9 with
    | none => false
    | some a => Straight.check anf (cfg s d) ext (roundB s d) (e₁.setReg .r9 (pxor a (atom 25))) post

theorem of_check {s d : Reg} (h : check s d = true) :
    ∃ e₁ a, Straight.eval anf (cfg s d) ext (roundA s) env₀ = some e₁ ∧ e₁.reg .r9 = some a ∧
      Straight.check anf (cfg s d) ext (roundB s d) (e₁.setReg .r9 (pxor a (atom 25))) post = true := by
  unfold check at h
  split at h
  · cases h
  · rename_i e₁ he₁
    split at h
    · cases h
    · rename_i a ha
      exact ⟨e₁, a, he₁, ha, h⟩

/-- The registers a round keeps. -/
def kept : List Reg := [.rdi, .rsi, .r15, .rsp]

/-- The round's instructions write none of `kept`. -/
def keeps (s d : Reg) : Bool :=
  (roundA s ++ roundB s d).all fun i => kept.all fun r => i.dst != some r

theorem env₀_reg {r : Reg} {a : Poly} (h : env₀.reg r = some a) :
    ∃ x < 5, r = rowReg x ∧ a = atom (20 + x) := by
  simp only [env₀] at h
  cases r <;> simp at h <;> subst h
  · exact ⟨0, by decide, rfl, rfl⟩
  · exact ⟨2, by decide, rfl, rfl⟩
  · exact ⟨3, by decide, rfl, rfl⟩
  · exact ⟨1, by decide, rfl, rfl⟩
  · exact ⟨4, by decide, rfl, rfl⟩

open VG.Proof.Sha3 (Lanes laneAddr outState)
open VG.Proof.Sha3.Compl (cmpl msk maskP eval_specP)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

theorem cmpl_get (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] = A[i] ^^^ msk i := by
  simp [cmpl]

/-- A round from the state at `s` to the state at `d`: on lanes kept
complemented (`cmpl`), with row 4 in `rowReg` before and after. -/
theorem round_ok {sR dR : Reg} (hc : check sR dR = true) (hk : keeps sR dR = true)
    (hsk : sR ∈ kept) (hdk : dR ∈ kept) (k : Nat)
    {s : State} {A : KState} {rc : Lane} {src dst : Addr}
    (hs : s.gpr sR = src) (hd : s.gpr dR = dst)
    (he : Proof.Sha3.Env s.rd s.wr src dst (s.ea (rcOp k)))
    (hA : Lanes s.mem src (cmpl A))
    (hrow : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl A)[20 + x])
    (hrc : s.mem.readW (s.ea (rcOp k)) 64 = rc) :
    WP isa (.block (round sR dR k)) s fun s' =>
      Lanes s'.mem dst (cmpl (outState A rc)) ∧
      (∀ x (hx : x < 5), s'.gpr (rowReg x) = (cmpl (outState A rc))[20 + x]) ∧
      Frame [⟨dst, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r ∈ kept, s'.gpr r = s.gpr r := by
  obtain ⟨e₁, a, he₁, ha, hchk⟩ := of_check hc
  obtain ⟨e₃, he₃, hpost⟩ := Straight.of_check _ _ _ hchk
  let V : Nat → Lane := fun i => if i = 25 then rc else s.mem.readW (wordAddr src i) 64
  have hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i := fun i hi => by
    simp only [V, show i ≠ 25 by omega, ite_false]
    rw [← cmpl_get A hi]; exact hA i hi
  have hV25 : V 25 = rc := by simp [V]
  have hok : Ok (cfg sR dR) s :=
    { slotIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hd]; exact he.dst_out j hj
      extIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hs]; exact he.src_in j hj
      slots := by simp only [cfg]; decide
      sep := fun j hj i hi => by
        simp only [cfg] at hj hi ⊢; rw [hd, hs]
        exact Region.Disjoint.sep he.dst_src (Proof.Sha3.lane_contains dst hj)
          (Proof.Sha3.lane_contains src hi) }
  have hrel : Rel (AnfRel V) (cfg sR dR) ext env₀ s :=
    { reg := fun r a h => by
        obtain ⟨x, hx, rfl, rfl⟩ := env₀_reg h
        simp only [AnfRel, eval_atom, V, show 20 + x ≠ 25 by omega, ite_false]
        rw [hrow x hx]; exact hA _ (by omega)
      slot := fun _ _ _ h => by cases h
      ext := fun j a hj h => by
        simp only [ext, Option.some.injEq] at h; subst h
        simp only [cfg] at hj ⊢
        simp only [AnfRel, eval_atom, V, show j ≠ 25 by omega, ite_false, hs] }
  obtain ⟨s₁, hs₁, p₁⟩ := Straight.run (anf_sound V) hok hrel he₁
  have hk' : ∀ r ∈ kept, (roundA sR).all (fun i => i.dst != some r) = true ∧
      (roundB sR dR).all (fun i => i.dst != some r) = true := fun r hr => by
    simp only [keeps, List.all_append, Bool.and_eq_true, List.all_eq_true] at hk
    exact ⟨List.all_eq_true.mpr fun i hi => hk.1 i hi r hr, List.all_eq_true.mpr fun i hi => hk.2 i hi r hr⟩
  have k₁ : ∀ r ∈ kept, s₁.gpr r = s.gpr r := fun r hr =>
    p₁.other r (by rw [(hk' r hr).1]; decide)
  -- ι
  have hea : s₁.ea (rcOp k) = s.ea (rcOp k) := by
    simp only [State.ea, rcOp, k₁ .rsi (by decide), k₁ .r15 (by decide)]
  have hrc₁ : s₁.mem.readW (s.ea (rcOp k)) 64 = rc := by
    rw [p₁.frame.readW (Region.contains_self _ _) ?_ (by decide), hrc]
    simp only [slotRegion, cfg, List.mem_singleton, forall_eq, hd]
    exact he.dst_rc.symm
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s.ea (rcOp k)) 8 := by rw [p₁.rd, p₁.wr]; exact he.rc_in
  let v := s₁.gpr .r9 ^^^ rc
  have hexec : exec (iota k) s₁ =
      some ((arithFlags s₁ v false false).setReg .r9 v) := by
    simp [iota, exec, execAlu, readSrc, State.load64, hea, hin₁, hrc₁, v]
  have hr9 : AnfRel V (pxor a (atom 25)) v := by
    simp only [AnfRel, eval_pxor, eval_atom, hV25, v]; rw [p₁.rel.reg _ _ ha]
  have hb₁ : Reg.r9 ≠ (cfg sR dR).base := fun h => by
    simp only [cfg] at h; subst h; simp [kept] at hdk
  have hx₁ : Reg.r9 ≠ (cfg sR dR).ext := fun h => by
    simp only [cfg] at h; subst h; simp [kept] at hsk
  have p₂ := post_setReg p₁.ok p₁.rel hr9 hb₁ hx₁ (arithFlags s₁ v false false) ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, hs₃, p₃⟩ := Straight.run (anf_sound V) p₂.ok p₂.rel he₃
  have hbase : s₃.gpr dR = dst := by
    have := p₃.base.trans (p₂.base.trans p₁.base)
    simp only [cfg] at this; rw [this, hd]
  unfold round
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, WP.block_cons_iff.mpr ⟨_, hexec, WP.of_runBlock ⟨s₃, hs₃, ?_⟩⟩⟩
  simp only [post, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨fun i hi => ?_, fun x hx => ?_, ?_, p₃.rd.trans (p₂.rd.trans p₁.rd),
    p₃.wr.trans (p₂.wr.trans p₁.wr), fun r hr => ?_⟩
  · have h := p₃.rel.slot i _ (by simp only [cfg]; exact hi) (hpost.1 i hi)
    simp only [AnfRel, eval_specP hV hV25 hi, cfg, hbase] at h
    exact h.symm
  · have h := p₃.rel.reg _ _ (hpost.2 x hx)
    simp only [AnfRel, eval_specP hV hV25 (show 20 + x < 25 by omega)] at h
    exact h.symm
  · have f₁ := p₁.frame
    have f₃ := p₃.frame
    have hb₂ : ((arithFlags s₁ v false false).setReg .r9 v).gpr dR = dst := by
      have := p₂.base.trans p₁.base; simp only [cfg] at this; rw [this, hd]
    simp only [slotRegion, cfg, hb₂, hd] at f₁ f₃
    exact f₁.trans f₃
  · rw [p₃.other r (by rw [(hk' r hr).2]; decide), p₂.other r (fun h => by subst h; simp [kept] at hr), k₁ r hr]

theorem check₀ : check .rdi .rsi = true := by decide +kernel
theorem check₁ : check .rsi .rdi = true := by decide +kernel
theorem keeps₀ : keeps .rdi .rsi = true := by decide +kernel
theorem keeps₁ : keeps .rsi .rdi = true := by decide +kernel

/-! ## Complementing the lanes -/

/-- The state at `rdi` (slots). -/
def sCfg : Cfg := { base := .rdi, slots := 25, ext := .rdi, exts := 0 }

/-- Lane `i` of the state is atom `i`. -/
def sEnv : Straight.Env Poly := { reg := fun _ => none, slot := fun i => some (atom i) }

/-- The lanes `complLanes` complemented. -/
def cPost (e : Straight.Env Poly) : Bool :=
  (List.range 25).all fun i => e.slot i == some (pxor (atom i) (maskP i))

/-- And row 4 of the result in `rowReg`. -/
def rPost (e : Straight.Env Poly) : Bool :=
  cPost e && (List.range 5).all fun x => e.reg (rowReg x) == some (pxor (atom (20 + x)) (maskP (20 + x)))

theorem complement_check : Straight.check anf sCfg (fun _ => none) complement sEnv cPost = true := by
  decide +kernel

theorem complementRow_check :
    Straight.check anf sCfg (fun _ => none) (complement ++ loadRow) sEnv rPost = true := by
  decide +kernel

theorem complement_writes : ∀ r ∈ kept, (complement ++ loadRow).all (fun i => i.dst != some r) = true := by
  decide +kernel

theorem complement_writes' : ∀ r ∈ kept, complement.all (fun i => i.dst != some r) = true := by
  decide +kernel

theorem eval_compl (M : KState) {i : Nat} (hi : i < 25) :
    Bitslice.Anf.eval (fun j => M[j]!) (pxor (atom i) (maskP i)) = (cmpl M)[i] := by
  rw [eval_pxor, eval_atom, Compl.eval_maskP, cmpl_get M hi, Proof.Sha3.getElem!_eq _ hi]

/-- A block that complements the lanes `complLanes` of the state at `rdi`. -/
theorem slots_ok {is : List Instr} {post : Straight.Env Poly → Bool}
    (hchk : Straight.check anf sCfg (fun _ => none) is sEnv post = true) (hpost : ∀ e, post e = true → cPost e = true)
    (hw : ∀ r ∈ kept, is.all (fun i => i.dst != some r) = true)
    {s : State} {st : Addr} {M : KState} (hdi : s.gpr .rdi = st) (hst : (⟨st, 200⟩ : Region) ∈ s.wr)
    (hM : Lanes s.mem st M) :
    ∃ s' e', runBlock isa is s = some s' ∧ post e' = true ∧
      Rel (AnfRel fun i => M[i]!) sCfg (fun _ => none) e' s' ∧
      Lanes s'.mem st (cmpl M) ∧ Frame [⟨st, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r ∈ kept, s'.gpr r = s.gpr r := by
  obtain ⟨e', he', hp⟩ := Straight.of_check _ _ _ hchk
  have hok : Ok sCfg s := Ok.of_region hst (by simp [sCfg, hdi]) (by simp [sCfg]) (by decide) rfl
  have hrel : Rel (AnfRel fun i => M[i]!) sCfg (fun _ => none) sEnv s :=
    { reg := fun _ _ h => by cases h
      slot := fun k a hk h => by
        simp only [sEnv, Option.some.injEq] at h; subst h
        simp only [sCfg] at hk ⊢
        simp only [AnfRel, eval_atom, hdi, Proof.Sha3.getElem!_eq _ hk]
        exact (hM k hk).symm
      ext := fun _ _ _ h => by cases h }
  obtain ⟨s', hs', p⟩ := Straight.run (anf_sound _) hok hrel he'
  have hc := hpost e' hp
  simp only [cPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  refine ⟨s', e', hs', hp, p.rel, fun i hi => ?_, ?_, p.rd, p.wr, fun r hr => p.other r (by rw [hw r hr]; decide)⟩
  · have hb : s'.gpr .rdi = st := p.base.trans hdi
    have h := p.rel.slot i _ (by simp only [sCfg]; exact hi) (hc i hi)
    simp only [AnfRel, eval_compl M hi, sCfg, hb] at h
    exact h.symm
  · have f := p.frame
    simp only [slotRegion, sCfg, hdi] at f
    exact f

theorem rows_of {e : Straight.Env Poly} {s : State} {M : KState}
    (hr : Rel (AnfRel fun i => M[i]!) sCfg (fun _ => none) e s) (hp : rPost e = true) :
    ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl M)[20 + x] := by
  intro x hx
  simp only [rPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have h := hr.reg _ _ (hp.2 x hx)
  simp only [AnfRel, eval_compl M (show 20 + x < 25 by omega)] at h
  exact h.symm

theorem cmpl_cmpl (A : KState) : cmpl (cmpl A) = A := by
  apply Vector.ext; intro i hi
  rw [cmpl_get _ hi, cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end VG.Proof.Sha3.X86_64.Round
