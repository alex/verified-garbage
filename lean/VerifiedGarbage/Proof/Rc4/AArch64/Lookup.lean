import VerifiedGarbage.Proof.Rc4.AArch64.Regs

/-!
# A table lookup

`lookup_run`: from the index `X` broadcast in `x`, and `X ^ 64`, `X ^ 128`,
`X ^ 192` in `a`, `b`, `c` (`quarters_run` computes them), the lookup
leaves `S[X]` (`tbyte`) broadcast in `d`, through the temporary `t`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem exec_vop' (s : State) (op : VOp) :
    exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

/-- The registers but `d` keep their values, and nothing else changes. -/
def Only (ds : List VReg) (s s' : State) : Prop :=
  s' = { s with v := s'.v } ∧ ∀ r, r ∉ ds → s'.v r = s.v r

theorem Only.refl (ds : List VReg) (s : State) : Only ds s s := ⟨rfl, fun _ _ => rfl⟩

theorem Only.trans {ds : List VReg} {a b c : State} (h₁ : Only ds a b) (h₂ : Only ds b c) :
    Only ds a c := by
  refine ⟨?_, fun r hr => (h₂.2 r hr).trans (h₁.2 r hr)⟩
  rw [h₂.1, h₁.1]

theorem Only.mono {ds ds' : List VReg} {a b : State} (h : Only ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    Only ds' a b := ⟨h.1, fun r hr => h.2 r fun h' => hr (hs r h')⟩

theorem Only.setV (s : State) {d : VReg} {ds : List VReg} (hd : d ∈ ds) (x : BitVec 128) :
    Only ds s (s.setV d x) := by
  refine ⟨rfl, fun r hr => ?_⟩
  have : r ≠ d := fun e => hr (e ▸ hd)
  exact v_setV_of_ne _ _ this

theorem Only.gpr {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.gpr = s.gpr := by
  rw [h.1]
theorem Only.mem {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.mem = s.mem := by
  rw [h.1]
theorem Only.rd {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.rd = s.rd := by
  rw [h.1]
theorem Only.wr {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.wr = s.wr := by
  rw [h.1]
theorem Only.sp {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.sp = s.sp := by
  rw [h.1]

theorem runBlock_cat (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_cat, h₁, Option.bind_some, h₂]

/-! ## The quarters -/

theorem xor64_128 (X : BitVec 8) : X ^^^ 64 ^^^ 128 = X ^^^ 192 := by
  rw [BitVec.xor_assoc]; rfl

theorem quarters_run {s : State} (hk : Consts s) {x a b c : VReg} (X : BitVec 8)
    (hx : s.v x = bc X) (hax : a ≠ x) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c)
    (ha128 : a ≠ c128) (hb128 : b ≠ c128) :
    ∃ s', runBlock isa (quarters x a b c) s = some s' ∧ s'.v a = bc (X ^^^ 64) ∧
      s'.v b = bc (X ^^^ 128) ∧ s'.v c = bc (X ^^^ 192) ∧ Only [a, b, c] s s' := by
  let s₁ := s.setV a (s.v x ^^^ s.v c64)
  let s₂ := s₁.setV b (s₁.v x ^^^ s₁.v c128)
  let s₃ := s₂.setV c (s₂.v a ^^^ s₂.v c128)
  have ha₁ : s₁.v a = bc (X ^^^ 64) := by
    simp only [s₁, v_setV_self, hx, hk.c64, bc_xor]
  have ha₂ : s₂.v a = bc (X ^^^ 64) := by simp only [s₂, v_setV_of_ne _ _ (Ne.symm hba), ha₁]
  have hb₂ : s₂.v b = bc (X ^^^ 128) := by
    simp only [s₂, v_setV_self, s₁, v_setV_of_ne _ _ hax.symm, v_setV_of_ne _ _ ha128.symm, hx,
      hk.c128, bc_xor]
  have c128₂ : s₂.v c128 = bc 128 := by
    simp only [s₂, s₁, v_setV_of_ne _ _ hb128.symm, v_setV_of_ne _ _ ha128.symm, hk.c128]
  refine ⟨s₃, ?_, ?_, ?_, ?_, ?_⟩
  · have e₁ : exec (eorV a x c64) s = some s₁ := rfl
    have e₂ : exec (eorV b x c128) s₁ = some s₂ := rfl
    have e₃ : exec (eorV c a c128) s₂ = some s₃ := rfl
    rw [quarters, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some,
      runBlock_cons, e₃, runStep_some, runBlock_nil]
  · by_cases h : a = c
    · exact absurd h hca.symm
    · simp only [s₃, v_setV_of_ne _ _ h, ha₂]
  · simp only [s₃, v_setV_of_ne _ _ hbc]
    exact hb₂
  · simp only [s₃, v_setV_self, ha₂, c128₂, bc_xor, xor64_128]
  · exact (((Only.setV s (by simp) _).trans (Only.setV _ (by simp) _)).trans (Only.setV _ (by simp) _))

/-! ## The lookup -/

/-- What a `tbl` (or `tbx`, keeping `prev`) of quarter `q`, at index `idx`,
leaves in a byte. -/
def qbyte (T : Nat → BitVec 8) (q idx : Nat) (ext : Bool) (prev : BitVec 8) : BitVec 8 :=
  if idx < 64 then T (64 * q + idx) else if ext then prev else 0

theorem vbyte_tblN (s : State) (ext : Bool) {q : Nat} (hq : q < 4) (d m : VReg) {e : Nat}
    (he : e < 16) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * 4 then
        tableByte s.v ([VReg.v16, .v20, .v24, .v28].getD q .v16) (vbyte (s.v m) i).toNat
      else if ext then vbyte (s.v d) i else 0) e =
      qbyte (tbyte s.v) q (vbyte (s.v m) e).toNat ext (vbyte (s.v d) e) := by
  rw [vbyte_ofVBytes _ he, qbyte]
  split
  · rename_i h; rw [tableByte_quarter _ hq h]
  · rfl

theorem toNat_xor_byte (X : BitVec 8) (k : Nat) (hk : k < 256) :
    (X ^^^ BitVec.ofNat 8 k).toNat = X.toNat ^^^ k := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem or_zero8 (y : BitVec 8) : y ||| 0 = y := by simp
theorem zero_or8 (y : BitVec 8) : 0 ||| y = y := by simp

/-- The four quarters' bytes, combined, are the byte at the index. -/
theorem quarters_byte (T : Nat → BitVec 8) (X : BitVec 8) (p p' : BitVec 8) :
    qbyte T 1 (X.toNat ^^^ 64) true (qbyte T 0 X.toNat false p) |||
      qbyte T 3 (X.toNat ^^^ 192) true (qbyte T 2 (X.toNat ^^^ 128) false p') = T X.toNat := by
  have hX := X.isLt
  have q := xor_quarter X.toNat hX
  obtain ⟨h1, e1⟩ := q 1 (by decide)
  obtain ⟨h2, e2⟩ := q 2 (by decide)
  obtain ⟨h3, e3⟩ := q 3 (by decide)
  simp only [Nat.mul_one, show 64 * 2 = 128 by rfl, show 64 * 3 = 192 by rfl] at h1 h2 h3 e1 e2 e3
  simp only [qbyte]
  have n1 : X.toNat / 64 ≠ 1 → ¬ (X.toNat ^^^ 64 < 64) := fun h h' => h (h1.mp h')
  have n2 : X.toNat / 64 ≠ 2 → ¬ (X.toNat ^^^ 128 < 64) := fun h h' => h (h2.mp h')
  have n3 : X.toNat / 64 ≠ 3 → ¬ (X.toNat ^^^ 192 < 64) := fun h h' => h (h3.mp h')
  rcases (by omega : X.toNat / 64 = 0 ∨ X.toNat / 64 = 1 ∨ X.toNat / 64 = 2 ∨ X.toNat / 64 = 3)
    with h | h | h | h
  · simp only [show X.toNat < 64 by omega, n1 (by omega), n2 (by omega), n3 (by omega), ite_true,
      ite_false, Bool.false_eq_true, Nat.mul_zero, Nat.zero_add, or_zero8]
  · simp only [show ¬ X.toNat < 64 by omega, h1.mpr h, n2 (by omega), n3 (by omega), ite_true,
      ite_false, Bool.false_eq_true]
    rw [e1 h, or_zero8]
    exact congrArg T (by omega)
  · simp only [show ¬ X.toNat < 64 by omega, n1 (by omega), h2.mpr h, n3 (by omega), ite_true,
      ite_false, Bool.false_eq_true]
    rw [e2 h, zero_or8]
    exact congrArg T (by omega)
  · simp only [show ¬ X.toNat < 64 by omega, n1 (by omega), n2 (by omega), h3.mpr h, ite_true,
      ite_false, Bool.false_eq_true]
    rw [e3 h, zero_or8]
    exact congrArg T (by omega)

theorem xor_toNat (X : BitVec 8) (k : BitVec 8) : (X ^^^ k).toNat = X.toNat ^^^ k.toNat :=
  BitVec.toNat_xor _ _

theorem lookup_run {s : State} {d t x a b c : VReg} (X : BitVec 8)
    (hx : s.v x = bc X) (ha : s.v a = bc (X ^^^ 64)) (hb : s.v b = bc (X ^^^ 128))
    (hc : s.v c = bc (X ^^^ 192))
    (hd : NotTable d) (ht : NotTable t) (hdt : d ≠ t) (hda : d ≠ a) (hdb : d ≠ b)
    (hdc : d ≠ c) (htc : t ≠ c) :
    ∃ s', runBlock isa (lookup d t x a b c) s = some s' ∧ s'.v d = bc (tbyte s.v X.toNat) ∧
      Only [d, t] s s' := by
  let T := tbyte s.v
  let f (q : Nat) (m : VReg) (ext : Bool) (st : State) (dd : VReg) : BitVec 128 :=
    ofVBytes fun i => if (vbyte (st.v m) i).toNat < 16 * 4 then
      tableByte st.v ([VReg.v16, .v20, .v24, .v28].getD q .v16) (vbyte (st.v m) i).toNat
    else if ext then vbyte (st.v dd) i else 0
  let s₁ := s.setV d (f 0 x false s d)
  let s₂ := s₁.setV d (f 1 a true s₁ d)
  let s₃ := s₂.setV t (f 2 b false s₂ t)
  let s₄ := s₃.setV t (f 3 c true s₃ t)
  let s₅ := s₄.setV d (s₄.v d ||| s₄.v t)
  have o₁ : Only [d, t] s s₁ := Only.setV _ (by simp) _
  have o₂ : Only [d, t] s s₂ := o₁.trans (Only.setV _ (by simp) _)
  have o₃ : Only [d, t] s s₃ := o₂.trans (Only.setV _ (by simp) _)
  have o₄ : Only [d, t] s s₄ := o₃.trans (Only.setV _ (by simp) _)
  have o₅ : Only [d, t] s s₅ := o₄.trans (Only.setV _ (by simp) _)
  have tab : ∀ st, Only [d, t] s st → tbyte st.v = T := by
    intro st h; funext k; simp only [tbyte, T]
    rw [h.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hd.ne _, ht.ne _⟩)]
  have a₁ : s₁.v a = bc (X ^^^ 64) := by rw [v_setV_of_ne _ _ (Ne.symm hda), ha]
  have b₂ : s₂.v b = bc (X ^^^ 128) := by
    rw [v_setV_of_ne _ _ (Ne.symm hdb), v_setV_of_ne _ _ (Ne.symm hdb), hb]
  have c₃ : s₃.v c = bc (X ^^^ 192) := by
    rw [v_setV_of_ne _ _ (Ne.symm htc), v_setV_of_ne _ _ (Ne.symm hdc), v_setV_of_ne _ _ (Ne.symm hdc), hc]
  have d₄ : s₄.v d = s₂.v d := by
    rw [v_setV_of_ne _ _ hdt, v_setV_of_ne _ _ hdt]
  have hf : ∀ q m ext st dd e, q < 4 → e < 16 →
      vbyte (f q m ext st dd) e = qbyte (tbyte st.v) q (vbyte (st.v m) e).toNat ext (vbyte (st.v dd) e) :=
    fun q m ext st dd e hq he => vbyte_tblN st ext hq dd m he
  have y₁ : ∀ e < 16, vbyte (s₁.v d) e = qbyte T 0 X.toNat false (vbyte (s.v d) e) := by
    intro e he
    rw [show s₁.v d = f 0 x false s d from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, hx,
      vbyte_bc _ he]
  have y₂ : ∀ e < 16, vbyte (s₂.v d) e =
      qbyte T 1 (X.toNat ^^^ 64) true (vbyte (s₁.v d) e) := by
    intro e he
    rw [show s₂.v d = f 1 a true s₁ d from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, a₁,
      vbyte_bc _ he, xor_toNat, tab s₁ o₁]
    rfl
  have y₃ : ∀ e < 16, vbyte (s₃.v t) e =
      qbyte T 2 (X.toNat ^^^ 128) false (vbyte (s₂.v t) e) := by
    intro e he
    rw [show s₃.v t = f 2 b false s₂ t from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, b₂,
      vbyte_bc _ he, xor_toNat, tab s₂ o₂]
    rfl
  have y₄ : ∀ e < 16, vbyte (s₄.v t) e =
      qbyte T 3 (X.toNat ^^^ 192) true (vbyte (s₃.v t) e) := by
    intro e he
    rw [show s₄.v t = f 3 c true s₃ t from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, c₃,
      vbyte_bc _ he, xor_toNat, tab s₃ o₃]
    rfl
  refine ⟨s₅, ?_, ?_, o₅⟩
  · have e₁ : exec (.vop (.tblN false 4 d .v16 x)) s = some s₁ := rfl
    have e₂ : exec (.vop (.tblN true 4 d .v20 a)) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.tblN false 4 t .v24 b)) s₂ = some s₃ := rfl
    have e₄ : exec (.vop (.tblN true 4 t .v28 c)) s₃ = some s₄ := rfl
    have e₅ : exec (.vop (.logic .orr d d t)) s₄ = some s₅ := rfl
    rw [lookup, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · apply vbyte_ext; intro e he
    simp only [s₅, v_setV_self, vbyte_or, d₄, y₂ e he, y₁ e he, y₄ e he, y₃ e he, vbyte_bc _ he]
    exact quarters_byte T X _ _

end VG.Proof.Rc4.AArch64
