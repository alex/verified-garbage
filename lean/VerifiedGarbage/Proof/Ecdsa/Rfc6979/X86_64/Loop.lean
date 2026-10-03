import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search

/-!
# Deterministic ECDSA on x86-64: the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`); the loop's invariant before
candidate `i` (`LoopInv`): `K` and `V` are those before it, the count is
`8 - i`, and every earlier candidate was unsuitable. One iteration either
moves to candidate `i + 1`, branching back, or leaves the loop with the
signature of candidate `i`, which is suitable or the last (`tryOne_ok`,
`loop_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Ecdsa.Rfc6979 (kvAt candAt step)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (L : Lay) (m₀ : Mem) : Nat := Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d 32)
abbrev hBOf (L : Lay) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg 32
abbrev eOf (L : Lay) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt Spec.P256.curve (hBOf L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (L : Lay) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init Spec.P256.curve Spec.Hmac.sha256 32 (xOf L m₀) (hBOf L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `V`, and its signature. -/
abbrev kvI (L : Lay) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAt Spec.Hmac.sha256 (kv0 L m₀).1 (kv0 L m₀).2 i
abbrev candI (L : Lay) (m₀ : Mem) (i : Nat) : List Byte := candAt Spec.Hmac.sha256 (kv0 L m₀).1 (kv0 L m₀).2 i
abbrev sigI (L : Lay) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith Spec.P256.curve (xOf L m₀) (eOf L m₀) (Spec.Weierstrass.ofBytes (candI L m₀ i))

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (L : Lay) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .rax).setWidth 32 = 1 ∧ Spec.Sha256.bytesAt t.mem L.out 64 = Spec.Ecdsa.encode Spec.P256.curve rs
  | none => (t.gpr .rax).setWidth 32 = 0 ∧ Spec.Sha256.bytesAt t.mem L.out 64 = List.replicate 64 0

/-- Before candidate `i`. -/
structure LoopInv (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < 8
  k : kOf L t.mem = (kvI L m₀ i).1
  v : vOf L t.mem = (kvI L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 64 (8 - i)
  fails : ∀ j < i, sigI L m₀ j = none

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < 8
  fails : ∀ j < i, sigI L m₀ j = none
  last : sigI L m₀ i ≠ none ∨ i = 7
  res : ResultIs L (sigI L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Spec.Sha256.bytesAt t.mem L.d 32 = Spec.Sha256.bytesAt m₀ L.d 32 := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (List.mem_range.mp hi)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    Spec.Sha256.bytesAt t.mem L.dg 32 = Spec.Sha256.bytesAt m₀ L.dg 32 := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (List.mem_range.mp hi)

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 120, 8⟩ r) : cnt L m' = cnt L m :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem kvw_cnt (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 120, 8⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- What `core` changes: `out`, `scratch` and its return address. -/
abbrev CoreW (L : Lay) : List Region := [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 16, 8⟩]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₁ : 24 ≤ d) (h₂ : d + n ≤ 160) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem cnt_sub {i : Nat} (hi : i < 8) : BitVec.ofNat 64 (8 - i) - 1 = BitVec.ofNat 64 (8 - (i + 1)) := by
  have : ∀ i < 8, BitVec.ofNat 64 (8 - i) - 1 = BitVec.ofNat 64 (8 - (i + 1)) := by decide
  exact this i hi

theorem cnt_ne {i : Nat} (hi : i < 8) : BitVec.ofNat 64 (8 - (i + 1)) ≠ 0 ↔ i + 1 < 8 := by
  have : ∀ i < 8, (BitVec.ofNat 64 (8 - (i + 1)) ≠ 0 ↔ i + 1 < 8) := by decide
  exact this i hi

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- `core`'s signature is the candidate's. -/
theorem coreSig_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hv : vOf L t.mem = candI L m₀ i) :
    coreSig L t.mem = sigI L m₀ i := by
  simp only [coreSig, Proof.Ecdsa.X86_64.sig, ecdsa_bytesAt]
  rw [hc.dBytes hL, hc.dgBytes hL]
  exact congrArg _ (congrArg _ hv)

theorem ResultIs.eax_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs L r t) :
    (t.gpr .rax).setWidth 32 = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `rax` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs L r t) (ha : t'.gpr .rax = t.gpr .rax)
    (hm : Spec.Sha256.bytesAt t'.mem L.out 64 = Spec.Sha256.bytesAt t.mem L.out 64) : ResultIs L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## One candidate -/

/-- After `V = HMAC_K(V)`: candidate `i`'s `V`. -/
structure P₁ (L : Lay) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf L u.mem = (kvI L m₀ i).1
  v : vOf L u.mem = candI L m₀ i
  cnt : cnt L u.mem = BitVec.ofNat 64 (8 - i)
  fails : ∀ j < i, sigI L m₀ j = none

/-- `core`'s arguments. -/
structure Args (L : Lay) (u : State) : Prop where
  rdi : u.gpr .rdi = L.out
  rsi : u.gpr .rsi = L.d
  rdx : u.gpr .rdx = L.dg
  rcx : u.gpr .rcx = L.B + BitVec.ofNat 64 56
  r8 : u.gpr .r8 = L.scr

/-- After `core`: its result. -/
structure P₃ (L : Lay) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf L u.mem = (kvI L m₀ i).1
  v : vOf L u.mem = candI L m₀ i
  cnt : cnt L u.mem = BitVec.ofNat 64 (8 - i)
  fails : ∀ j < i, sigI L m₀ j = none
  res : ResultIs L (sigI L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf L u.mem = (kvI L m₀ i).1
  v : vOf L u.mem = candI L m₀ i
  cnt : cnt L u.mem = BitVec.ofNat 64 (8 - (i + 1))
  fails : ∀ j < i, sigI L m₀ j = none
  res : ResultIs L (sigI L m₀ i) u
  dec : isa.eval .ne u = some (decide (sigI L m₀ i = none ∧ i + 1 < 8))

theorem try₁_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv L m₀ i t) :
    WP isa (cfgOf v).hmacV t fun u => Ctx L g m₀ u ∧ P₁ L m₀ i u :=
  WP.mono (hmacV_ok hL hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v]; rfl, (cnt_frame hf₁ (kvw_cnt hL)).trans hi.cnt, hi.fails⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ L m₀ i t) :
    WP isa (.block Cfg.coreArgs) t fun u => Ctx L g m₀ u ∧ P₁ L m₀ i u ∧ Args L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, hdi, hsi, hdx, hcx, h8⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails⟩, hdi, hsi, hdx, hcx, h8⟩

theorem try₃_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ L m₀ i t) (ha : Args L t) :
    WP isa (.call (cfgOf v).coreN (cfgOf v).coreC) t fun u => Ctx L g m₀ u ∧ P₃ L m₀ i u := by
  refine WP.mono (core_ok (v := v) hL hc ha.rdi ha.rsi ha.rdx ha.rcx ha.r8) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hc hi.v] at hr₃
  exact ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (by omega) (by omega)) (by omega)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (by omega) (by omega)) (by omega)).trans hi.v,
    (cnt_frame hf₃ (corew_disj hL (by omega) (by omega))).trans hi.cnt, hi.fails, hr₃⟩

theorem try₄_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid L m₀ i u := by
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hf₄, hn₄, ha₄, hz₄⟩ => ⟨hc₄, hi.lt, ?_, ?_, ?_, hi.fails, ?_, ?_⟩
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by omega)).trans hi.k
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by omega)).trans hi.v
  · rw [hn₄, hi.cnt, cnt_sub hi.lt]
  · exact hi.res.keep ha₄ (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_OUT (by omega)).symm) (by omega))
  · show u₄.zf.map (!·) = _
    rw [hz₄, hi.cnt, cnt_sub hi.lt]
    simp only [Option.map_some, Bool.not_not, hi.res.eax_zero, cnt_ne hi.lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid L m₀ i t) :
    WP isa (.ite .ne (.seq (cfgOf v).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv L m₀ (i + 1) t')) := by
  by_cases hgo : sigI L m₀ i = none ∧ i + 1 < 8
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, hz₆⟩ => ⟨hc₆, .inr ⟨by show u₆.zf.map _ = _; rw [hz₆]; rfl, ?_⟩⟩
    have hkv : kvI L m₀ (i + 1) = step Spec.Hmac.sha256 (kvI L m₀ i).1 (kvI L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, cnt_frame hf₅ (kvw_cnt hL), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, hz₅, ha₅⟩ => ⟨hc₅, .inl ⟨by show u₅.zf.map _ = _; rw [hz₅]; rfl,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < 8 := fun h => hgo ⟨hs, h⟩; omega)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv L m₀ i t) :
    WP isa (cfgOf v).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval .ne t' = some false ∧ Exit L m₀ i t') ∨
        (isa.eval .ne t' = some true ∧ LoopInv L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.X86_64
