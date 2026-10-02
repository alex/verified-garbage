import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem.X86_64.Prfs

/-!
# ML-KEM-768 on x86-64: K-PKE.Encrypt, the ciphertext

When every entry of `Â` was sampled: `ŷ` (`y_ok`), `u` to the ciphertext
(`u_ok`), `t̂` (`t_ok`) and `v` to the ciphertext (`v_ok`). Between the steps,
`ER ny nu nt`: the first `ny` of `ŷ`, `nu` of `u` and `nt` of `t̂` are done.
Each with its constant time, for a given `ρ`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr}

/-- The steps done after the matrix. -/
structure ER (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (ny nu nt : Nat) (s : State) : Prop where
  ok : allOk (rhoE ek) 9
  i : EIn C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ i < 3, ∀ j < 3, PolyIs s.mem (pa s (aS i j)) (aHat (rhoE ek) i j)
  prf : ∀ N < 7, bytesAt s.mem (pa s (prfO N)) 128 = prf 2 r (BitVec.ofNat 8 N)
  y : ∀ k < ny, PolyIs s.mem (pa s (pS k)) (encY r k)
  u : ∀ i < nu, bytesAt s.mem (pa s (sc (oCT + 320 * i))) 320 = compressEncode 10 (encU (aHat (rhoE ek)) r i)
  t : ∀ i < nt, PolyIs s.mem (pa s (pS (3 + i))) (ekT ek i)

/-- A piece that writes `ws` keeps `ER ny nu nt`. -/
def erChk (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ny nu nt : Nat) (ws : List (Ptr × Nat)) : Bool :=
  inKeep bs chk E ws && (List.range 9).all (fun e => keepB bs ws (aS (e / 3) (e % 3)) 1024) &&
    (List.range 7).all (fun N => keepB bs ws (prfO N) 128) && (List.range ny).all (fun k => keepB bs ws (pS k) 1024) &&
    (List.range nu).all (fun i => keepB bs ws (sc (oCT + 320 * i)) 320) &&
    (List.range nt).all (fun i => keepB bs ws (pS (3 + i)) 1024)

theorem ER.keep {C : Ctx rbs wbs} {ek m r : List Byte} {ny nu nt : Nat} {s s' : State} (h : ER C E ek m r ny nu nt s)
    {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : erChk (rbs ++ wbs) C.chk E ny nu nt ws = true) :
    ER C E ek m r ny nu nt s' := by
  simp only [erChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hin, kA⟩, kR⟩, kY⟩, kU⟩, kT⟩ := hc
  have L := C.lay h.i.out
  refine ⟨h.ok, h.i.keep hP.b hin, by rw [hP.cs .r15 (by decide)]; exact h.r15, fun i hi j hj => ?_,
    fun N hN => by rw [L.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L.keepPoly hP.b (kY k hk) (h.y k hk), fun i hi => by rw [L.keepBytes hP.b (kU i hi)]; exact h.u i hi,
    fun i hi => L.keepPoly hP.b (kT i hi) (h.t i hi)⟩
  have := kA (3 * i + j) (by omega)
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
  exact L.keepPoly hP.b this (h.mat i hi j hj)

theorem EB.flag {C : Ctx rbs wbs} {ek m r : List Byte} {s s' : State} (h : EB C E ek m r 9 s) (hP : PPost s s' [])
    (hc : inKeep (rbs ++ wbs) C.chk E [] = true) (hk : ∀ e < 9, keepB (rbs ++ wbs) [] (aS (e / 3) (e % 3)) 1024 = true)
    (hsb : keepB (rbs ++ wbs) [] (sc oSB) 32 = true) : EB C E ek m r 9 s' := by
  have L := C.lay h.i.out
  exact ⟨h.i.keep hP.b hc, by rw [L.keepBytes hP.b hsb]; exact h.sb, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he f hf => L.keepPoly hP.b (hk e he) (h.mat e he f hf)⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure ER0 (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  ok : allOk (rhoE ek) 9
  i : EIn C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ i < 3, ∀ j < 3, PolyIs s.mem (pa s (aS i j)) (aHat (rhoE ek) i j)

theorem ER0.start {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : EB C E ek m r 9 s)
    (ho : allOk (rhoE ek) 9) : ER0 C E ek m r s := by
  refine ⟨ho, h.i, by rw [h.r15, ifp ho], fun i hi j hj => ?_⟩
  have := h.mat (3 * i + j) (by omega) (aHat (rhoE ek) i j)
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
  exact this (aHat_eq ho hi hj)

/-- The steps, for the `ρ` of `ek`. -/
abbrev ERρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (ny nu nt : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE ek = ρ ∧ ER C E ek m r ny nu nt s

/-! ## The outputs of `PRF₂` -/

def prfsEChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  prfsChk bs wbs 7 oPR lPW && inKeep bs chk E (prfsW 7 oPR lPW) &&
    (List.range 9).all (fun e => keepB bs (prfsW 7 oPR lPW) (aS (e / 3) (e % 3)) 1024)

theorem prfsE_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hc : prfsEChk (rbs ++ wbs) wbs C.chk E = true)
    {ek m r : List Byte} {s : State} (h : ER0 C E ek m r s) :
    WP isa (v.callee.prfs 0 7 oPR lPW) s fun s' => PPost s s' (prfsW 7 oPR lPW) ∧ ER C E ek m r 0 0 0 s' := by
  simp only [prfsEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hpc, hin⟩, kA⟩ := hc
  have L := C.lay h.i.out
  refine WP.mono (v.prfs_ok L C.bs (by decide) hpc) fun s' ⟨hP, hb⟩ => ⟨hP, h.ok, h.i.keep hP.b hin,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun i hi j hj => ?_, fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · have := kA (3 * i + j) (by omega)
    rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
    exact L.keepPoly hP.b this (h.mat i hi j hj)
  · rw [prfO, hP.pa rbx_cs, hb N hN, h.i.r, Nat.zero_add]

/-- After the matrix, for the `ρ` of `ek`. -/
abbrev ER0ρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE ek = ρ ∧ ER0 C E ek m r s

theorem prfsE_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hc : prfsEChk (rbs ++ wbs) wbs C.chk E = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ C E ρ x ∧ ER0ρ C E ρ y) (v.callee.prfs 0 7 oPR lPW)
      (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ 0 0 0 x ∧ ERρ C E ρ 0 0 0 y) := by
  have hc' := hc
  simp only [prfsEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (v.prfs_tr C.bs (by decide) hc'.1.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (prfsE_ok v hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `ŷ` -/

def yChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (N : Nat) : Bool :=
  twoChk bs wbs (prfO N) 128 (pS N) 1024 && ipChk bs wbs (pS N) && erChk bs chk E N 0 0 (KeyGen.seW N)

theorem y_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < 3) (hc : yChk (rbs ++ wbs) wbs C.chk E N = true) {ek m r : List Byte}
    {s : State} (h : ER C E ek m r N 0 0 s) :
    WP isa (y A N) s fun s' => PPost s s' (KeyGen.seW N) ∧ ER C E ek m r (N + 1) 0 0 s' := by
  simp only [yChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, hrc⟩ := hc
  have L := C.lay h.i.out
  unfold y
  refine WP.seq (WP.mono (cbd2At_okL L rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L.post hP₁.b C.bs
  rw [h.prf N (by omega), ← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hP := PPost.app hP₁ hP₂ (by simp [calleeSaved])
  have hk := h.keep hP hrc
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.y k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂; exact hp₂

theorem y_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < 3) (hc : yChk (rbs ++ wbs) wbs C.chk E N = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ N 0 0 x ∧ ERρ C E ρ N 0 0 y) (y A N)
      (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ (N + 1) 0 0 x ∧ ERρ C E ρ (N + 1) 0 0 y) := by
  have hc' := hc
  simp only [yChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨htw, hic⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (y_ok hA hN hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold y
  exact RelCT.mono (RelCT.seqL (I := fun _ => True) (J := fun x => Reduced x.mem (pa x (pS N))) C.bs
    (RelCT.mono (cbd2At_trL rbx_na htw) (fun _ _ h => h.1) fun _ _ h => h)
    (fun x Lx _ => WP.mono (cbd2At_okL Lx rbx_na htw) fun x' ⟨hP, hq⟩ =>
      ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hA hic)) (fun _ _ h => ⟨h.1, trivial, trivial⟩)
    fun _ _ h => h

/-! ## `u` -/

/-- What `SamplePolyCBD₂(PRF₂(r, N))` to polynomial 16 writes. -/
abbrev prfW16 : List (Ptr × Nat) := [(pS 16, 1024)]

abbrev uW (i : Nat) : List (Ptr × Nat) :=
  KeyGen.dotW ++ [(pS 15, 1024), (sc oSS, 1024)] ++ prfW16 ++ [(pS 15, 1024)] ++ [(sc (oCT + 320 * i), 320)]

def uChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  dotChk bs wbs (fun j => aS j i) pS && ipChk bs wbs (pS 15) && twoChk bs wbs (prfO (3 + i)) 128 (pS 16) 1024 &&
    keepB bs prfW16 (pS 15) 1024 && accChk bs wbs (pS 15) (pS 16) &&
    twoChk bs wbs (pS 15) 1024 (sc (oCT + 320 * i)) 320 && inKeep bs chk E KeyGen.dotW &&
    inKeep bs chk E [(pS 15, 1024), (sc oSS, 1024)] && erChk bs chk E 3 i 0 (uW i) &&
    keepB bs KeyGen.dotW (prfO (3 + i)) 128 && keepB bs [(pS 15, 1024), (sc oSS, 1024)] (prfO (3 + i)) 128

theorem u_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {i : Nat} (hi : i < 3) (hc : uChk (rbs ++ wbs) wbs C.chk E i = true)
    {ek m r : List Byte} {s : State} (h : ER C E ek m r 3 i 0 s) :
    WP isa (u A i) s fun s' => PPost s s' (uW i) ∧ ER C E ek m r 3 (i + 1) 0 s' := by
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, htw⟩, hi₁⟩, hi₂⟩, hrc⟩, kp₁⟩, kp₂⟩ := hc
  have L := C.lay h.i.out
  unfold u
  refine WP.seq (WP.mono (dotAt_ok hA L C.bs hdc (a := fun j => aHat (rhoE ek) j i) (b := encY r)
    (fun k hk => h.mat k hk i hi) (fun k hk => h.y k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e₁ := h.i.keep hP₁.b hi₁
  have L₁ := C.lay e₁.out
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have e₂ := e₁.keep hP₂.b hi₂
  have L₂ := C.lay e₂.out
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (cbd2At_okL L₂ rbx_na hpc) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b C.bs
  rw [L₁.keepBytes hP₂.b kp₂, L.keepBytes hP₁.b kp₁, h.prf (3 + i) (by omega), ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (addAt_ok L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b C.bs
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceAt_okL L₄ rbx_na htw (by decide) hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅
    (by simp [calleeSaved])
  have hk := h.keep hP hrc
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.u i' hi'
  · rw [hP₅.pa rbx_cs, hb₅, hp₄.2]; rfl

theorem u_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {i : Nat} (hi : i < 3) (hc : uChk (rbs ++ wbs) wbs C.chk E i = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ 3 i 0 x ∧ ERρ C E ρ 3 i 0 y) (u A i)
      (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ 3 (i + 1) 0 x ∧ ERρ C E ρ 3 (i + 1) 0 y) := by
  have hc' := hc
  simp only [uChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, htw⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (u_ok hA hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold u
  refine RelCT.mono (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs
    (RelCT.mono (dotAt_tr hA C.bs hdc) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotAt_ok hA Lx C.bs hdc (a := fun k => polyAt x.mem (pa x (aS k i)))
      (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (nttInvAt_tr hA hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok hA Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) C.bs
      (RelCT.mono (cbd2At_trL rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk15 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceAt_trL rbx_na htw (by decide)))))) (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
        ⟨hl, fun k hk => ⟨(h₁.mat k hk i hi).1, (h₁.y k hk).1⟩, fun k hk => ⟨(h₂.mat k hk i hi).1, (h₂.y k hk).1⟩⟩)
    fun _ _ h => h

/-! ## `t̂` -/

def tChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (E.1, E.2 + 384 * i) 384 (pS (3 + i)) 1024 && erChk bs chk E 3 3 i [(pS (3 + i), 1024)]

theorem t_ok {C : Ctx rbs wbs} {i : Nat} (hi : i < 3) (hc : tChk (rbs ++ wbs) wbs C.chk E i = true)
    {ek m r : List Byte} {s : State} (h : ER C E ek m r 3 3 i s) :
    WP isa (t E i) s fun s' => PPost s s' [(pS (3 + i), 1024)] ∧ ER C E ek m r 3 3 (i + 1) s' := by
  simp only [tChk, Bool.and_eq_true] at hc
  have L := C.lay h.i.out
  refine WP.mono (dec12At_okL L rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, hk.u, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.t i' hi'
  · rw [hP.pa rbx_cs]
    have e : bytesAt s.mem (pa s (E.1, E.2 + 384 * i')) 384 = (ek.drop (384 * i')).take 384 := by
      rw [← h.i.ek]
      show _ = ((bytesAt s.mem (pa s E) 1184).drop (384 * i')).take 384
      rw [bytesAt_slice _ _ (show 384 * i' + 384 ≤ 1184 by omega), pa, pa, off_add]
    rw [e] at hp
    exact hp

theorem t_tr {C : Ctx rbs wbs} {i : Nat} (hi : i < 3) (hc : tChk (rbs ++ wbs) wbs C.chk E i = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ 3 3 i x ∧ ERρ C E ρ 3 3 i y) (t E i)
      (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ 3 3 (i + 1) x ∧ ERρ C E ρ 3 3 (i + 1) y) := by
  have hc' := hc
  simp only [tChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (dec12At_trL rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (t_ok hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `v` -/

abbrev vW : List (Ptr × Nat) := KeyGen.dotW ++ [(pS 15, 1024), (sc oSS, 1024)] ++ prfW16 ++ [(pS 15, 1024)] ++
  [(pS 16, 1024)] ++ [(pS 15, 1024)] ++ [(sc (oCT + 960), 128)]

def vChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  dotChk bs wbs (fun j => pS (3 + j)) pS && ipChk bs wbs (pS 15) && twoChk bs wbs (prfO 6) 128 (pS 16) 1024 &&
    keepB bs prfW16 (pS 15) 1024 && accChk bs wbs (pS 15) (pS 16) && twoChk bs wbs (sc oM) 32 (pS 16) 1024 &&
    keepB bs [(pS 16, 1024)] (pS 15) 1024 && twoChk bs wbs (pS 15) 1024 (sc (oCT + 960)) 128 &&
    inKeep bs chk E KeyGen.dotW && inKeep bs chk E [(pS 15, 1024), (sc oSS, 1024)] && inKeep bs chk E prfW16 &&
    inKeep bs chk E [(pS 15, 1024)] && inKeep bs chk E [(pS 16, 1024)] && inKeep bs chk E [(sc (oCT + 960), 128)] &&
    (List.range 3).all (fun i => keepB bs vW (sc (oCT + 320 * i)) 320) &&
    keepB bs KeyGen.dotW (prfO 6) 128 && keepB bs [(pS 15, 1024), (sc oSS, 1024)] (prfO 6) 128

theorem v_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} (hc : vChk (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State}
    (h : ER C E ek m r 3 3 3 s) :
    WP isa (v A) s fun s' => PPost s s' vW ∧ C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' (sc oCT)) 1088 = ct768 (aHat (rhoE ek)) ek m r := by
  simp only [vChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, hdd⟩, hk16⟩, htw⟩, i₁⟩, i₂⟩, i₃⟩, i₄⟩, i₅⟩, i₇⟩, hu⟩, kp₁⟩,
    kp₂⟩ := hc
  have L := C.lay h.i.out
  unfold v
  refine WP.seq (WP.mono (dotAt_ok hA L C.bs hdc (a := ekT ek) (b := encY r) (fun k hk => h.t k hk)
    (fun k hk => h.y k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e₁ := h.i.keep hP₁.b i₁
  have L₁ := C.lay e₁.out
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have e₂ := e₁.keep hP₂.b i₂
  have L₂ := C.lay e₂.out
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (cbd2At_okL L₂ rbx_na hpc) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have e₃ := e₂.keep hP₃.b i₃
  have L₃ := C.lay e₃.out
  rw [L₁.keepBytes hP₂.b kp₂, L.keepBytes hP₁.b kp₁, h.prf 6 (by decide), ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (addAt_ok L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have e₄ := e₃.keep hP₄.b i₄
  have L₄ := C.lay e₄.out
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.seq (WP.mono (ddAt_okL L₄ (d := 1) rbx_na hdd (by decide)) fun s₅ ⟨hP₅, hp₅⟩ => ?_)
  have e₅ := e₄.keep hP₅.b i₅
  have L₅ := C.lay e₅.out
  rw [e₄.m, ← hP₅.pa rbx_cs] at hp₅
  have hq₅ := L₄.keepPoly hP₅.b hk16 hp₄
  refine WP.seq (WP.mono (addAt_ok L₅ rbx_na hac hq₅.1 hp₅.1) fun s₆ ⟨hP₆, hp₆⟩ => ?_)
  have e₆ := e₅.keep hP₆.b i₄
  have L₆ := C.lay e₆.out
  rw [hq₅.2, hp₅.2, ← hP₆.pa rbx_cs] at hp₆
  refine WP.mono (ceAt_okL L₆ (d := 4) rbx_na htw (by decide) hp₆.1) fun s₇ ⟨hP₇, hb₇⟩ => ?_
  have e₇ := e₆.keep hP₇.b i₇
  have hP := PPost.app (PPost.app (PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide))
    hP₄ (by decide)) hP₅ (by decide)) hP₆ (by decide)) hP₇ (by decide)
  refine ⟨hP, e₇.out, by
    rw [hP₇.cs .r15 (by decide), hP₆.cs .r15 (by decide), hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide),
      hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15], ?_⟩
  rw [show (1088 : Nat) = 320 + (320 + (320 + 128)) from rfl, KeyGen.bytesAt_split, KeyGen.bytesAt_split, KeyGen.bytesAt_split,
    show oCT + 320 = oCT + 320 * 1 from rfl, show oCT + 320 * 1 + 320 = oCT + 320 * 2 from rfl,
    show oCT + 320 * 2 + 320 = oCT + 960 from rfl, show oCT = oCT + 320 * 0 from rfl]
  rw [L.keepBytes hP.b (hu 0 (by decide)), L.keepBytes hP.b (hu 1 (by decide)), L.keepBytes hP.b (hu 2 (by decide)),
    h.u 0 (by decide), h.u 1 (by decide), h.u 2 (by decide), hP₇.pa rbx_cs, hb₇, hp₆.2]
  simp only [ct768_eq, List.append_assoc]
  rfl

/-! ## The end of K-PKE.Encrypt -/

/-- The end: `r15` as `allOk`, and the ciphertext if it is 1. -/
structure EOut (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  r15 : s.gpr .r15 = if allOk (rhoE ek) 9 then 1 else 0
  ct : allOk (rhoE ek) 9 → bytesAt s.mem (pa s (sc oCT)) 1088 = ct768 (aHat (rhoE ek)) ek m r

/-- The end, for the `ρ` of `ek`. -/
abbrev EOρ (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop := ∃ ek m r, rhoE ek = ρ ∧ EOut C E ek m r s

theorem v_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} (hc : vChk (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ C E ρ 3 3 3 x ∧ ERρ C E ρ 3 3 3 y) (v A)
      (fun x y => LRel rbs wbs x y ∧ EOρ C E ρ x ∧ EOρ C E ρ y) := by
  have hc' := hc
  simp only [vChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, hdd⟩, hk16⟩, htw⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (v_ok hA hc hx) fun _ ⟨hP, ho, h15, hct⟩ =>
    ⟨⟨_, hP.b⟩, ek, m, r, eρ, ho, by rw [h15, ifp hx.ok], fun _ => hct⟩
  unfold v
  refine RelCT.mono (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs
    (RelCT.mono (dotAt_tr hA C.bs hdc) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotAt_ok hA Lx C.bs hdc (a := fun k => polyAt x.mem (pa x (pS (3 + k))))
      (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (nttInvAt_tr hA hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok hA Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) C.bs
      (RelCT.mono (cbd2At_trL rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk15 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) C.bs
      (RelCT.mono (ddAt_trL (d := 1) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddAt_okL Lx (d := 1) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk16 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceAt_trL (d := 4) rbx_na htw (by decide)))))))) (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
        ⟨hl, fun k hk => ⟨(h₁.t k hk).1, (h₁.y k hk).1⟩, fun k hk => ⟨(h₂.t k hk).1, (h₂.y k hk).1⟩⟩)
    fun _ _ h => h

end Enc

end VG.Proof.MlKem.X86_64
