import VerifiedGarbage.Proof.MlDsa.X86.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlKem.X86.Sample

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_rej_ntt_poly`

Untrusted: everything here is checked by Lean. The body is the SHAKE128
output of the seed at `scratch + 840` (`sponge_piece`), then the 336
iterations of the loop, iteration `t` of which starts with the coefficients
`LA B t = rnFold [] ((G(B, 1008)).take (3t))` (`Proof/MlDsa/Sample/RejNtt.lean`)
stored at `a`, `edi` after them and `ecx` counting them (`Loop`); the end
returns whether there are 256. An iteration computes the value of its 3
bytes in `eax` (`load_piece`) and, while there are fewer than 256
coefficients, stores it if it is less than `q` (`try_piece`); its branches
depend on the XOF output, a function of the seed, and so agree in two runs
from the same seed (`Pub`), which the contract lets the function leak.
-/

namespace VG.Proof.MlDsa.X86.Sample.RejNtt

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp rnLoad rnTry rnBody rnInit retJ qImm)
open VG.Spec.MlDsa (Zq q G n)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)

/-- The layout: `rejNTT(seed, a, scratch)`, 34 bytes of seed, 1008 bytes of
SHAKE128. -/
def L : Lay := { nA := 3, iA := 1, iS := 2, rate := 168, outlen := 1008, mlen := some 34 }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by cases hk; decide,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The pointers, `esp` and the seed agree. -/
def Pub (s₀ s₀' : State) : Prop := PubP L s₀ s₀' ∧ L.Msg s₀ = L.Msg s₀'

/-! ## The XOF output and the coefficients it gives -/

/-- The XOF output of the seed `B`. -/
abbrev X (B : List Byte) : List Byte := G B 1008

/-- Byte `k` of it. -/
abbrev xb (B : List Byte) (k : Nat) : Byte := (X B).getD k 0

/-- The coefficients sampled after `t` iterations. -/
abbrev LA (B : List Byte) (t : Nat) : List Zq := rnFold [] ((X B).take (3 * t))

/-- The value of the 3 bytes of iteration `t`. -/
abbrev z (B : List Byte) (t : Nat) : Nat := rnZ (xb B (3 * t)) (xb B (3 * t + 1)) (xb B (3 * t + 2))

theorem out_eq (s₀ : State) : L.out s₀ = X (L.Msg s₀) := (G_eq _ _).symm

theorem X_length (B : List Byte) : (X B).length = 1008 := G_length _ _

theorem take_add_three (M : List Byte) {i : Nat} (h : i + 3 ≤ M.length) :
    M.take (i + 3) = M.take i ++ [M.getD i 0, M.getD (i + 1) 0, M.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < M.length by omega), List.getElem?_eq_getElem (show i + 1 < M.length by omega),
    List.getElem?_eq_getElem (show i + 2 < M.length by omega), Option.getD_some]

theorem LA_succ (B : List Byte) {t : Nat} (ht : t < 336) :
    LA B (t + 1) = rnStep (LA B t) (xb B (3 * t)) (xb B (3 * t + 1)) (xb B (3 * t + 2)) := by
  simp only [LA]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega, take_add_three _ (by rw [X_length]; omega),
    rnFold_snoc _ (by rw [List.length_take, X_length]; omega)]

theorem LA_zero (B : List Byte) : LA B 0 = [] := by simp [LA, rnFold]

theorem LA_length_le (B : List Byte) (t : Nat) : (LA B t).length ≤ 256 := rnFold_length_le (by simp) _

theorem z_lt (B : List Byte) (t : Nat) : z B t < 2 ^ 23 := by
  have := (xb B (3 * t)).isLt
  have := (xb B (3 * t + 1)).isLt
  have := Nat.mod_lt (xb B (3 * t + 2)).toNat (show 128 > 0 by decide)
  simp only [z, rnZ]; omega

/-! ## The state of the loop -/

/-- After `t` iterations, with the coefficients `La` stored. -/
structure Loop (s₀ : State) (t : Nat) (La : List Zq) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 1008, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = xb (L.Msg s₀) p
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (840 + 3 * t)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (336 - t)
  len : La.length ≤ 256
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * La.length)
  ecx : s.gpr .ecx = BitVec.ofNat 32 La.length
  stored : Stored s.mem (L.aA s₀) La

/-- Within iteration `t`, with the value of its 3 bytes in `eax`. -/
structure Mid (s₀ : State) (t : Nat) (La : List Zq) (s : State) : Prop extends Loop s₀ t La s where
  eax : s.gpr .eax = BitVec.ofNat 32 (z (L.Msg s₀) t)

theorem Loop.flags {s₀ s s' : State} {t : Nat} {La : List Zq} (h : Loop s₀ t La s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : Loop s₀ t La s' :=
  ⟨⟨by rw [hg, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm]; exact h.frame⟩,
    by rw [hm]; exact h.out, by rw [hg, h.esi], by rw [hg, h.ebp], h.len, by rw [hg, h.edi], by rw [hg, h.ecx],
    by rw [hm]; exact h.stored⟩

theorem Mid.flags {s₀ s s' : State} {t : Nat} {La : List Zq} (h : Mid s₀ t La s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : Mid s₀ t La s' :=
  ⟨h.toLoop.flags hg hm hr hw, by rw [hg, h.eax]⟩

theorem linit_piece : Piece (Pre L) Pub (Out L) (fun s₀ s => Loop s₀ 0 (LA (L.Msg s₀) 0) s) (.block rnInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) (by decide)
    have v₁ := h.args 1 (by decide)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp (config := {decide := true}) only [rnInit, argOp, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₁, i₁, v₁, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    rw [LA_zero]
    refine ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, fun p hp' => ?_, by simp [h.esi], rfl,
      by simp, by simp; rfl, by simp, stored_nil _ _⟩
    rw [h.out p hp', out_eq]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

/-! ## The value of the 3 bytes -/

theorem load_ok {s₀ : State} (hp : Pre L s₀) {t : Nat} (ht : t < 336) {s : State}
    (h : Loop s₀ t (LA (L.Msg s₀) t) s) :
    WP isa (.block rnLoad) s fun s' => Mid s₀ t (LA (L.Msg s₀) t) s' ∧
      eval .b s' = some (decide ((LA (L.Msg s₀) t).length < 256)) := by
  have hs := hp.s_fit
  have eb : ∀ o < 3, (L.sP s₀ + BitVec.ofNat 32 (840 + 3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (840 + (3 * t + o)) := fun o ho => by
    rw [ea_add (by simp only [L] at hs ⊢; omega), Nat.add_assoc]
  have e0 := eb 0 (by omega)
  have e1 := eb 1 (by omega)
  have e2 := eb 2 (by omega)
  have i0 := hp.inS' h.wr (o := 840 + (3 * t + 0)) (n := 1) (by omega)
  have i1 := hp.inS' h.wr (o := 840 + (3 * t + 1)) (n := 1) (by omega)
  have i2 := hp.inS' h.wr (o := 840 + (3 * t + 2)) (n := 1) (by omega)
  have v0 := h.out (3 * t + 0) (by omega)
  have v1 := h.out (3 * t + 1) (by omega)
  have v2 := h.out (3 * t + 2) (by omega)
  simp only [Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [rnLoad, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, e1, e2, i0, i1, i2, v0, v1, v2, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  have hz : (BitVec.setWidth 32 (xb (L.Msg s₀) (3 * t)) +
      (BitVec.setWidth 32 (xb (L.Msg s₀) (3 * t + 1))).rotateRight 24 +
      (BitVec.setWidth 32 (xb (L.Msg s₀) (3 * t + 2)) &&& 127).rotateRight 16).toNat = z (L.Msg s₀) t := by
    have l0 := (xb (L.Msg s₀) (3 * t)).isLt
    have l1 := (xb (L.Msg s₀) (3 * t + 1)).isLt
    have l2 := (xb (L.Msg s₀) (3 * t + 2)).isLt
    have hm : (BitVec.setWidth 32 (xb (L.Msg s₀) (3 * t + 2)) &&& 127).toNat =
        (xb (L.Msg s₀) (3 * t + 2)).toNat % 128 := by
      rw [show (127 : BitVec 32) = BitVec.ofNat 32 (2 ^ 7 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    have hm' : (xb (L.Msg s₀) (3 * t + 2)).toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    rw [BitVec.toNat_add, BitVec.toNat_add,
      rotr_small (BitVec.setWidth 32 (xb (L.Msg s₀) (3 * t + 2)) &&& 127) (by decide) (by decide)
        (by rw [hm]; omega), hm,
      rotr_small (BitVec.setWidth 32 (xb (L.Msg s₀) (3 * t + 1))) (by decide) (by decide)
        (by rw [toNat_byte32]; omega), toNat_byte32, toNat_byte32]
    simp only [z, rnZ]
    omega
  have hl := h.len
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ebp], h.len,
    by simp [h.edi], by simp [h.ecx], h.stored⟩, eq_ofNat_of_toNat hz⟩, ?_⟩
  simp only [eval, h.ecx, toNat_ofNat32 (show (LA (L.Msg s₀) t).length < 2 ^ 32 by omega)]
  rfl

theorem load_piece (t : Nat) (ht : t < 336) :
    Piece (Pre L) Pub (fun s₀ s => Loop s₀ t (LA (L.Msg s₀) t) s) (fun s₀ s => Mid s₀ t (LA (L.Msg s₀) t) s ∧
      eval .b s = some (decide ((LA (L.Msg s₀) t).length < 256))) (.block rnLoad) :=
  Piece.taint [.esi] (fun s₀ s hp h => load_ok hp ht h)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.1.sP hL]) (by taint_decide)

/-! ## Storing the value -/

theorem zw_ofNat {v : Nat} (hv : v < q) : zw (Fin.ofNat q v) = BitVec.ofNat 32 v := by
  simp only [zw, Fin.val_ofNat, Nat.mod_eq_of_lt hv]

theorem store_ok {s₀ : State} (hp : Pre L s₀) {t : Nat} {La : List Zq} {v : Nat} (hv : v < q)
    (hl : La.length < 256) {s : State} (h : Mid s₀ t La s) (hrv : s.gpr .eax = BitVec.ofNat 32 v) :
    WP isa (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) s
      fun s' => Loop s₀ t (La ++ [Fin.ofNat q v]) s' := by
  have ha := hp.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * La.length) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (L.aA s₀) La.length := by
    rw [ea_add (by simp only [L] at ha ⊢; omega)]; rfl
  have hin : InRegions s.wr (coeffAddr (L.aA s₀) La.length) 4 := hp.inA h.wr hl
  have fa : Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) La.length) (BitVec.ofNat 32 v)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hl)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, ea, hin,
    hrv, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := L.aR s₀) (by simp) _
    (coeff_contains _ hl)⟩, fun p hp' => ?_, by simp [h.esi], by simp [h.ebp],
    (by simp only [List.length_append, List.length_singleton]; omega), ?_, ?_, ?_⟩
  · refine (fa _ fun r hr hc => ?_).trans (h.out p hp')
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.a_s _ hc ((hp.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
  · simp only [ite_true, List.length_append, List.length_singleton]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx, List.length_append, List.length_singleton]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
  · have := stored_snoc h.stored hl (Fin.ofNat q v)
    rwa [zw_ofNat hv] at this

theorem LA_then {B : List Byte} {t : Nat} (ht : t < 336) (hl : (LA B t).length < 256) (hz : z B t < q) :
    LA B t ++ [Fin.ofNat q (z B t)] = LA B (t + 1) := by
  rw [LA_succ B ht, rnStep, ifT (by simp only [n]; omega), ifT hz]

theorem LA_else {B : List Byte} {t : Nat} (ht : t < 336) (hz : ¬ (z B t < q)) : LA B t = LA B (t + 1) := by
  rw [LA_succ B ht, rnStep]
  split <;> rfl

theorem LA_full {B : List Byte} {t : Nat} (ht : t < 336) (hl : ¬ (LA B t).length < 256) :
    LA B t = LA B (t + 1) := by
  rw [LA_succ B ht, rnStep, ifF (by simp only [n]; omega)]

theorem nil_piece {Pre' : State → Prop} {Pub' : State → State → Prop} {A B : State → State → Prop}
    (h : ∀ s₀ s, Pre' s₀ → A s₀ s → B s₀ s) : Piece Pre' Pub' A B (.block []) :=
  Piece.taint [] (fun s₀ s hp ha => WP.block_nil_iff.mpr (h s₀ s hp ha))
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

theorem try_piece (t : Nat) (ht : t < 336) :
    Piece (Pre L) Pub (fun s₀ s => Mid s₀ t (LA (L.Msg s₀) t) s ∧ (LA (L.Msg s₀) t).length < 256)
      (fun s₀ s => Loop s₀ t (LA (L.Msg s₀) (t + 1)) s) rnTry := by
  refine Piece.seq (B := fun s₀ s => (Mid s₀ t (LA (L.Msg s₀) t) s ∧ (LA (L.Msg s₀) t).length < 256) ∧
      eval .b s = some (decide (z (L.Msg s₀) t < q))) ?_
    (Piece.ite (fun s₀ => decide (z (L.Msg s₀) t < q)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.2]) ?_ ?_)
  · refine Piece.taint [] (fun s₀ s hp ha => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)
    obtain ⟨h, hl⟩ := ha
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨h.flags rfl rfl rfl rfl, hl⟩, ?_⟩
    have := z_lt (L.Msg s₀) t
    simp only [eval, h.eax, toNat_ofNat32 (show z (L.Msg s₀) t < 2 ^ 32 by omega)]
    rfl
  · refine Piece.taint [.edi] (fun s₀ s hp ⟨⟨⟨h, hl⟩, _⟩, hb⟩ => ?_)
      (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨h, _⟩, _⟩, _⟩ ⟨⟨⟨h', _⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
    · have hq : z (L.Msg s₀) t < q := of_decide_eq_true hb
      exact (store_ok hp hq hl h h.eax).mono fun s' h' => LA_then ht hl hq ▸ h'
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP hL, hq.2]
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => LA_else ht (of_decide_eq_false hb) ▸ h.toLoop

theorem end_ok {s₀ : State} {t : Nat} (ht : t < 336) {La : List Zq} {s : State} (h : Loop s₀ t La s) :
    WP isa (.block [.alu .add .esi (.imm 3), .alu .sub .ebp (.imm 1)]) s
      fun s' => Loop s₀ (t + 1) La s' ∧ eval .ne s' = some (decide (t + 1 < 336)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, h.len, by simp [h.edi], by simp [h.ecx],
    h.stored⟩, ?_⟩
  · simp only [ite_true, h.esi]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    exact cnt_next ht
  · simp only [eval, h.ebp]
    exact cnt_ne ht (by omega)

/-! ## An iteration, and the loop -/

theorem body_piece (t : Nat) (ht : t < 336) :
    Piece (Pre L) Pub (fun s₀ s => Loop s₀ t (LA (L.Msg s₀) t) s)
      (fun s₀ s => Loop s₀ (t + 1) (LA (L.Msg s₀) (t + 1)) s ∧ eval .ne s = some (decide (t + 1 < 336)))
      rnBody := by
  refine Piece.seq (load_piece t ht) (Piece.seq (B := fun s₀ s => Loop s₀ t (LA (L.Msg s₀) (t + 1)) s) ?_
    (Piece.taint [] (fun s₀ s _ h => end_ok ht h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)))
  refine Piece.ite (fun s₀ => decide ((LA (L.Msg s₀) t).length < 256)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.2]) ?_ ?_
  · exact (try_piece t ht).mono (fun _ _ _ ⟨⟨h, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h
  · exact nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => LA_full ht (of_decide_eq_false hb) ▸ h.toLoop

theorem loop_piece : Piece (Pre L) Pub (fun s₀ s => Loop s₀ 0 (LA (L.Msg s₀) 0) s)
    (fun s₀ s => Loop s₀ 336 (LA (L.Msg s₀) 336) s) (.loop rnBody .ne) :=
  Piece.loop (fun t s₀ s => Loop s₀ t (LA (L.Msg s₀) t) s) (by decide) fun t ht => body_piece t ht

/-- The end: 1 in `eax` if there are 256 coefficients, 0 if fewer. -/
structure Fin (s₀ s : State) : Prop extends Loop s₀ 336 (LA (L.Msg s₀) 336) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((LA (L.Msg s₀) 336).length / 256)

theorem fin_piece : Piece (Pre L) Pub (fun s₀ s => Loop s₀ 336 (LA (L.Msg s₀) 336) s) Fin
    (.block (retJ .ecx)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ebp], h.len, by rw [g _ (by decide), h.edi], by rw [g _ (by decide), h.ecx],
    by rw [o.mem]; exact h.stored⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.ecx]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (LA (L.Msg s₀) 336).length < 2 ^ 32 by omega)])

end VG.Proof.MlDsa.X86.Sample.RejNtt

namespace VG.Proof.MlDsa.X86.Sample.RejNtt

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (rnBody rnInit retJ sponge)
open VG.Spec.MlDsa (Zq q G n)
open VG.Spec.Sha3 (bytesAt)

/-! ## The whole function -/

theorem main_piece : Piece (Pre L) Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (sponge 2 168 (.imm 34) 1008) (.seq (.block rnInit) (.seq (.loop rnBody .ne) (.block (retJ .ecx))))) :=
  Piece.seq ((sponge_piece hL).pre_mono (fun _ h => h) fun _ _ _ _ h => h.1) <|
    Piece.seq linit_piece <| Piece.seq loop_piece fin_piece

theorem piece : Piece (Pre L) Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.rejNTT :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨by have := hp.sp; omega, by have := hp.sp'; omega⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem Pre.of {s₀ : State} (h : (Spec.MlDsa.rejNTTContract X86.abi 56).pre s₀) : Pre L s₀ := by
  sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, show (34 : Nat) < 168 by decide⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂ :=
  VG.Proof.MlKem.X86.Sample.map_toNat_inj

/-- The coefficients at `a`, when there are 256. -/
theorem poly_eq {s₀ s : State} (h : Loop s₀ 336 (LA (L.Msg s₀) 336) s) (hl : (LA (L.Msg s₀) 336).length = 256) :
    Spec.MlDsa.PolyIs s.mem (L.aA s₀) (toPoly (rnFold [] (G (L.Msg s₀) 1008))) := by
  have e : LA (L.Msg s₀) 336 = rnFold [] (G (L.Msg s₀) 1008) := by
    simp only [LA]; rw [List.take_of_length_le (by rw [X_length])]
  rw [← e]
  exact stored_polyIs h.stored hl

/-- Memory with the arguments `0`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Sample.rejNTT (Spec.MlDsa.rejNTTContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h
    refine ⟨⟨e₁, fun i hi => ?_⟩, map_toNat_inj e₂⟩
    match i, hi with
    | 0, _ => exact e₃
    | 1, _ => exact e₄
    | 2, _ => exact e₅
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl := hfin.len
    by_cases e : (LA (L.Msg s₀) 336).length = 256
    · have hp := poly_eq hfin.toLoop e
      have hf : (rnFold [] (G (L.Msg s₀) 1008)).length = 256 := by
        simp only [LA] at e; rwa [List.take_of_length_le (by rw [X_length])] at e
      rw [e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, ?_⟩⟩
      show Spec.MlDsa.rejNTTPoly 1008 (L.Msg s₀) = some (Spec.MlDsa.polyAt s.mem (L.aA s₀))
      rw [rejNTT_some hf, hp.2]
    · rw [Nat.div_eq_of_lt (by omega)]
      have hf : (rnFold [] (G (L.Msg s₀) 1008)).length ≠ 256 := by
        simp only [LA] at e; rwa [List.take_of_length_le (by rw [X_length])] at e
      exact ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide),
        .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · let st := satState satMem [⟨0, 34⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 12⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.RejNtt
