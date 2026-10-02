import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem.X86_64.Prfs

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, the ciphertext

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

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- The steps done after the matrix. -/
structure ER (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (ny nu nt : Nat) (s : State) : Prop where
  ok : allOk L.k (rhoE L ek) (L.k * L.k)
  i : EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoE L ek) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k + 1, bytesAt s.mem (pa s (prfO L N)) 128 = prf 2 r (BitVec.ofNat 8 N)
  y : ∀ k < ny, PolyIs s.mem (pa s (pS k)) (encY r k)
  u : ∀ i < nu, bytesAt s.mem (pa s (sc (L.oCT + 32 * L.du * i))) (32 * L.du) =
    compressEncode L.du (KPke.encU L.p (aHat (rhoE L ek)) r i)
  t : ∀ i < nt, PolyIs s.mem (pa s (pS (L.k + i))) (ekT ek i)

/-- A piece that writes `ws` keeps `ER ny nu nt`. -/
def erChk (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ny nu nt : Nat)
    (ws : List (Ptr × Nat)) : Bool :=
  inKeep L bs chk E ws && (List.range (L.k * L.k)).all (fun e => keepB bs ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k + 1)).all (fun N => keepB bs ws (prfO L N) 128) &&
    (List.range ny).all (fun k => keepB bs ws (pS k) 1024) &&
    (List.range nu).all (fun i => keepB bs ws (sc (L.oCT + 32 * L.du * i)) (32 * L.du)) &&
    (List.range nt).all (fun i => keepB bs ws (pS (L.k + i)) 1024)

theorem ER.keep {C : Ctx rbs wbs} {ek m r : List Byte} {ny nu nt : Nat} {s s' : State}
    (h : ER L C E ek m r ny nu nt s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws)
    (hc : erChk L (rbs ++ wbs) C.chk E ny nu nt ws = true) : ER L C E ek m r ny nu nt s' := by
  simp only [erChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hin, kA⟩, kR⟩, kY⟩, kU⟩, kT⟩ := hc
  have L₀ := C.lay h.i.out
  exact ⟨h.ok, h.i.keep hP.b hin, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kY k hk) (h.y k hk),
    fun i hi => by rw [L₀.keepBytes hP.b (kU i hi)]; exact h.u i hi, fun i hi => L₀.keepPoly hP.b (kT i hi) (h.t i hi)⟩

/-- `Â[i, j]`, from the entries. -/
theorem ER.matIJ {C : Ctx rbs wbs} {ek m r : List Byte} {ny nu nt : Nat} {s : State}
    (h : ER L C E ek m r ny nu nt s) {i j : Nat} (hi : i < L.k) (hj : j < L.k) :
    PolyIs s.mem (pa s (L.aS i j)) (aHat (rhoE L ek) i j) := by
  have := h.mat (L.k * i + j) (ij_lt hi hj)
  rwa [(divmod_ij hj).1, (divmod_ij hj).2, ← aS_ij] at this

theorem EB.flag {C : Ctx rbs wbs} {ek m r : List Byte} {s s' : State} (h : EB L C E ek m r (L.k * L.k) s)
    (hP : PPost s s' []) (hc : inKeep L (rbs ++ wbs) C.chk E [] = true)
    (hk : ∀ e < L.k * L.k, keepB (rbs ++ wbs) [] (pS (L.pA + e)) 1024 = true)
    (hsb : keepB (rbs ++ wbs) [] (sc oSB) 32 = true) : EB L C E ek m r (L.k * L.k) s' := by
  have L₀ := C.lay h.i.out
  exact ⟨h.i.keep hP.b hc, by rw [L₀.keepBytes hP.b hsb]; exact h.sb, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e he f hf => L₀.keepPoly hP.b (hk e he) (h.m.mat e he f hf)⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure ER0 (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  ok : allOk L.k (rhoE L ek) (L.k * L.k)
  i : EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoE L ek) (e / L.k) (e % L.k))

theorem ER0.start {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : EB L C E ek m r (L.k * L.k) s)
    (ho : allOk L.k (rhoE L ek) (L.k * L.k)) : ER0 L C E ek m r s :=
  ⟨ho, h.i, by rw [h.m.r15, ifp ho], fun e he => h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

/-- The steps, for the `ρ` of `ek`. -/
abbrev ERρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (ny nu nt : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ ER L C E ek m r ny nu nt s

/-! ## The outputs of `PRF₂` -/

def prfsEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  prfsChk bs wbs (2 * L.k + 1) L.oPR L.lPW && inKeep L bs chk E (prfsW (2 * L.k + 1) L.oPR L.lPW) &&
    (List.range (L.k * L.k)).all (fun e => keepB bs (prfsW (2 * L.k + 1) L.oPR L.lPW) (pS (L.pA + e)) 1024)

theorem prfsE_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hk : L.k ≤ 4) (hc : prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ek m r : List Byte} {s : State} (h : ER0 L C E ek m r s) :
    WP isa (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW) s fun s' =>
      PPost s s' (prfsW (2 * L.k + 1) L.oPR L.lPW) ∧ ER L C E ek m r 0 0 0 s' := by
  simp only [prfsEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hpc, hin⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (v.prfs_ok L₀ C.bs (by omega) hpc) fun s' ⟨hP, hb⟩ => ⟨hP, h.ok, h.i.keep hP.b hin,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [prfO, hP.pa rbx_cs, hb N hN, h.i.r, Nat.zero_add]

/-- After the matrix, for the `ρ` of `ek`. -/
abbrev ER0ρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ ER0 L C E ek m r s

theorem prfsE_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hk : L.k ≤ 4) (hc : prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ L C E ρ x ∧ ER0ρ L C E ρ y) (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ 0 0 0 x ∧ ERρ L C E ρ 0 0 0 y) := by
  have hc' := hc
  simp only [prfsEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (v.prfs_tr C.bs (by omega) hc'.1.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (prfsE_ok v hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `ŷ` -/

def yChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (N : Nat) : Bool :=
  twoChk bs wbs (prfO L N) 128 (pS N) 1024 && ipChk bs wbs (pS N) && erChk L bs chk E N 0 0 (KeyGen.seW N)

theorem y_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : yChk L (rbs ++ wbs) wbs C.chk E N = true) {ek m r : List Byte} {s : State} (h : ER L C E ek m r N 0 0 s) :
    WP isa (y L A N) s fun s' => PPost s s' (KeyGen.seW N) ∧ ER L C E ek m r (N + 1) 0 0 s' := by
  simp only [yChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, hrc⟩ := hc
  have L₀ := C.lay h.i.out
  unfold y
  refine WP.seq (WP.mono (cbd2At_okL L₀ rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b C.bs
  rw [h.prf N (by omega), ← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hP := PPost.app hP₁ hP₂ (by simp [calleeSaved])
  have hk := h.keep hP hrc
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.y k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂; exact hp₂

theorem y_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : yChk L (rbs ++ wbs) wbs C.chk E N = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ N 0 0 x ∧ ERρ L C E ρ N 0 0 y) (y L A N)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ (N + 1) 0 0 x ∧ ERρ L C E ρ (N + 1) 0 0 y) := by
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

abbrev uW (L : Kem) (i : Nat) : List (Ptr × Nat) :=
  dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)] ++ prfW16 ++ [(pS 15, 1024)] ++
    [(sc (L.oCT + 32 * L.du * i), 32 * L.du)]

def uChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  dotChk bs wbs (fun j => L.aS j i) pS L.k && ipChk bs wbs (pS 15) &&
    twoChk bs wbs (prfO L (L.k + i)) 128 (pS 16) 1024 && keepB bs prfW16 (pS 15) 1024 && accChk bs wbs (pS 15) (pS 16) &&
    twoChk bs wbs (pS 15) 1024 (sc (L.oCT + 32 * L.du * i)) (32 * L.du) && inKeep L bs chk E (dotW L.k) &&
    inKeep L bs chk E [(pS 15, 1024), (sc oSS, 1024)] && erChk L bs chk E L.k i 0 (uW L i) &&
    keepB bs (dotW L.k) (prfO L (L.k + i)) 128 && keepB bs [(pS 15, 1024), (sc oSS, 1024)] (prfO L (L.k + i)) 128

theorem u_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) (hk0 : 0 < L.k) {C : Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : uChk L (rbs ++ wbs) wbs C.chk E i = true) {ek m r : List Byte} {s : State}
    (h : ER L C E ek m r L.k i 0 s) :
    WP isa (u L A i) s fun s' => PPost s s' (uW L i) ∧ ER L C E ek m r L.k (i + 1) 0 s' := by
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, htw⟩, hi₁⟩, hi₂⟩, hrc⟩, kp₁⟩, kp₂⟩ := hc
  have L₀ := C.lay h.i.out
  unfold u
  refine WP.seq (WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) L₀ (a := fun j => aHat (rhoE L ek) j i) (b := encY r)
    (fun k hk => h.matIJ hk hi) (fun k hk => h.y k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e₁ := h.i.keep hP₁.b hi₁
  have L₁ := C.lay e₁.out
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have e₂ := e₁.keep hP₂.b hi₂
  have L₂ := C.lay e₂.out
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (cbd2At_okL L₂ rbx_na hpc) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b C.bs
  rw [L₁.keepBytes hP₂.b kp₂, L₀.keepBytes hP₁.b kp₁, h.prf (L.k + i) (by omega), ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (addAt_ok L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b C.bs
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceCall_okL K.ce L₄ rbx_na htw K.du.1 hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅
    (by simp [calleeSaved])
  have hk := h.keep hP hrc
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.u i' hi'
  · rw [hP₅.pa rbx_cs, hb₅, hp₄.2]; rfl

theorem u_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) (hk0 : 0 < L.k) {C : Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : uChk L (rbs ++ wbs) wbs C.chk E i = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k i 0 x ∧ ERρ L C E ρ L.k i 0 y) (u L A i)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k (i + 1) 0 x ∧ ERρ L C E ρ L.k (i + 1) 0 y) := by
  have hc' := hc
  simp only [uChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, htw⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (u_ok hA K hk0 hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold u
  refine RelCT.mono (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs
    (RelCT.mono (dotN_tr hA C.bs hk0 (dotChk_spec hdc)) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) Lx (a := fun k => polyAt x.mem (pa x (L.aS k i)))
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
      (ceCall_trL K.ce rbx_na htw K.du.1))))) (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
        ⟨hl, fun k hk => ⟨(h₁.matIJ hk hi).1, (h₁.y k hk).1⟩, fun k hk => ⟨(h₂.matIJ hk hi).1, (h₂.y k hk).1⟩⟩)
    fun _ _ h => h

/-! ## `t̂` -/

def tChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (E.1, E.2 + 384 * i) 384 (pS (L.k + i)) 1024 && erChk L bs chk E L.k L.k i [(pS (L.k + i), 1024)]

theorem t_ok {C : Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k i s) :
    WP isa (t L E i) s fun s' => PPost s s' [(pS (L.k + i), 1024)] ∧ ER L C E ek m r L.k L.k (i + 1) s' := by
  simp only [tChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (dec12At_okL L₀ rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, hk.u, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.t i' hi'
  · rw [hP.pa rbx_cs]
    have e : bytesAt s.mem (pa s (E.1, E.2 + 384 * i')) 384 = (ek.drop (384 * i')).take 384 := by
      rw [← h.i.ek]
      show _ = ((bytesAt s.mem (pa s E) (384 * L.k + 32)).drop (384 * i')).take 384
      rw [bytesAt_slice _ _ (show 384 * i' + 384 ≤ 384 * L.k + 32 by omega), pa, pa, off_add]
    rw [e] at hp
    exact hp

theorem t_tr {C : Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k L.k i x ∧ ERρ L C E ρ L.k L.k i y) (t L E i)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k L.k (i + 1) x ∧ ERρ L C E ρ L.k L.k (i + 1) y) := by
  have hc' := hc
  simp only [tChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (dec12At_trL rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (t_ok hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `v` -/

abbrev vW (L : Kem) : List (Ptr × Nat) := dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)] ++ prfW16 ++ [(pS 15, 1024)] ++
  [(pS 16, 1024)] ++ [(pS 15, 1024)] ++ [(sc (L.oCT + 32 * L.du * L.k), 32 * L.dv)]

def vChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  dotChk bs wbs (fun j => pS (L.k + j)) pS L.k && ipChk bs wbs (pS 15) &&
    twoChk bs wbs (prfO L (2 * L.k)) 128 (pS 16) 1024 && keepB bs prfW16 (pS 15) 1024 && accChk bs wbs (pS 15) (pS 16) &&
    twoChk bs wbs (sc oM) 32 (pS 16) 1024 && keepB bs [(pS 16, 1024)] (pS 15) 1024 &&
    twoChk bs wbs (pS 15) 1024 (sc (L.oCT + 32 * L.du * L.k)) (32 * L.dv) && inKeep L bs chk E (dotW L.k) &&
    inKeep L bs chk E [(pS 15, 1024), (sc oSS, 1024)] && inKeep L bs chk E prfW16 && inKeep L bs chk E [(pS 15, 1024)] &&
    inKeep L bs chk E [(pS 16, 1024)] && inKeep L bs chk E [(sc (L.oCT + 32 * L.du * L.k), 32 * L.dv)] &&
    (List.range L.k).all (fun i => keepB bs (vW L) (sc (L.oCT + 32 * L.du * i)) (32 * L.du)) &&
    keepB bs (dotW L.k) (prfO L (2 * L.k)) 128 && keepB bs [(pS 15, 1024), (sc oSS, 1024)] (prfO L (2 * L.k)) 128

theorem v_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) (hk0 : 0 < L.k) {C : Ctx rbs wbs}
    (hc : vChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k L.k s) :
    WP isa (v L A) s fun s' => PPost s s' (vW L) ∧ C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' (sc L.oCT)) L.ctLen = KPke.ct L.p (aHat (rhoE L ek)) ek m r := by
  simp only [vChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, hdd⟩, hk16⟩, htw⟩, i₁⟩, i₂⟩, i₃⟩, i₄⟩, i₅⟩, i₇⟩, hu⟩, kp₁⟩,
    kp₂⟩ := hc
  have L₀ := C.lay h.i.out
  unfold v
  refine WP.seq (WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) L₀ (a := ekT ek) (b := encY r) (fun k hk => h.t k hk)
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
  rw [L₁.keepBytes hP₂.b kp₂, L₀.keepBytes hP₁.b kp₁, h.prf (2 * L.k) (by omega), ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (addAt_ok L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have e₄ := e₃.keep hP₄.b i₄
  have L₄ := C.lay e₄.out
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.seq (WP.mono (ddCall_okL ddImpl L₄ (d := 1) rbx_na hdd (by decide)) fun s₅ ⟨hP₅, hp₅⟩ => ?_)
  have e₅ := e₄.keep hP₅.b i₅
  have L₅ := C.lay e₅.out
  rw [e₄.m, ← hP₅.pa rbx_cs] at hp₅
  have hq₅ := L₄.keepPoly hP₅.b hk16 hp₄
  refine WP.seq (WP.mono (addAt_ok L₅ rbx_na hac hq₅.1 hp₅.1) fun s₆ ⟨hP₆, hp₆⟩ => ?_)
  have e₆ := e₅.keep hP₆.b i₄
  have L₆ := C.lay e₆.out
  rw [hq₅.2, hp₅.2, ← hP₆.pa rbx_cs] at hp₆
  refine WP.mono (ceCall_okL K.ce L₆ (d := L.dv) rbx_na htw K.dv.1 hp₆.1) fun s₇ ⟨hP₇, hb₇⟩ => ?_
  have e₇ := e₆.keep hP₇.b i₇
  have hP₆' := PPost.app (PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide))
    hP₄ (by decide)) hP₅ (by decide)) hP₆ (by decide)
  have hP := PPost.app hP₆' hP₇ (by simp [calleeSaved])
  rw [hP₆'.pa rbx_cs] at hb₇
  refine ⟨hP, e₇.out, by
    rw [hP₇.cs .r15 (by decide), hP₆.cs .r15 (by decide), hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide),
      hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15], ?_⟩
  rw [Kem.ctLen, Params.ctLen, show 32 * (L.p.du * L.p.k + L.p.dv) = 32 * L.du * L.k + 32 * L.dv by
      simp only [Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, Nat.mul_assoc], hP.pa rbx_cs, sc, bytesAt_split,
    hb₇, hp₆.2, KPke.ct]
  refine congrArg (· ++ _) (bytesAt_catK _ _ _ _ _ _ L.k fun i hi => ?_)
  rw [← hP.pa (p := sc (L.oCT + 32 * L.du * i)) rbx_cs, L₀.keepBytes hP.b (hu i hi), h.u i hi]

/-! ## The end of K-PKE.Encrypt -/

/-- The end: `r15` as `allOk`, and the ciphertext if it is 1. -/
structure EOut (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  r15 : s.gpr .r15 = if allOk L.k (rhoE L ek) (L.k * L.k) then 1 else 0
  ct : allOk L.k (rhoE L ek) (L.k * L.k) →
    bytesAt s.mem (pa s (sc L.oCT)) L.ctLen = KPke.ct L.p (aHat (rhoE L ek)) ek m r

/-- The end, for the `ρ` of `ek`. -/
abbrev EOρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EOut L C E ek m r s

theorem v_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) (hk0 : 0 < L.k) {C : Ctx rbs wbs}
    (hc : vChk L (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k L.k L.k x ∧ ERρ L C E ρ L.k L.k L.k y) (v L A)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  have hc' := hc
  simp only [vChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, hdd⟩, hk16⟩, htw⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (v_ok hA K hk0 hc hx) fun _ ⟨hP, ho, h15, hct⟩ =>
    ⟨⟨_, hP.b⟩, ek, m, r, eρ, ho, by rw [h15, ifp hx.ok], fun _ => hct⟩
  unfold v
  refine RelCT.mono (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs
    (RelCT.mono (dotN_tr hA C.bs hk0 (dotChk_spec hdc)) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) Lx
      (a := fun k => polyAt x.mem (pa x (pS (L.k + k)))) (b := fun k => polyAt x.mem (pa x (pS k)))
      (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
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
      (RelCT.mono (ddCall_trL ddImpl (d := 1) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL ddImpl Lx (d := 1) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk16 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL K.ce (d := L.dv) rbx_na htw K.dv.1))))))) (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
        ⟨hl, fun k hk => ⟨(h₁.t k hk).1, (h₁.y k hk).1⟩, fun k hk => ⟨(h₂.t k hk).1, (h₂.y k hk).1⟩⟩)
    fun _ _ h => h

end Enc

end VG.Proof.MlKem.X86_64
