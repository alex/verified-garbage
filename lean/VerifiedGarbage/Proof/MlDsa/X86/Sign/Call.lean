import VerifiedGarbage.Proof.MlDsa.X86.Sign.Base

/-!
# ML-DSA signing on x86 (32-bit): calls

Untrusted: everything here is checked by Lean. A call (`callP`, `callPR`):
the moves of its arguments (`setup_piece'`), then the call in a frame of
its arguments (`Piece.callWith`, `callRet`), as ML-KEM's `call_piece` makes
it but with the runs related by `SPub`, so that a callee may leak what
signing may (`callP_piece`, `callPR_piece`). What the callee sees on entry:
its arguments (`ent_arg`), the stack below `esp` (`ent_esp`, `ent_arg0`),
and the buffers apart from its stack (`ent_rgn`).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What signing needs of a callee's code: it never writes `esp`, and its
calls and frames use at most 56 bytes of stack. -/
structure COk (c : Prog isa) : Prop where
  nosp : NoSp c
  stk : stackUse c ≤ 56

/-- The state after the moves of the arguments `as`, from a state satisfying `A`. -/
def After (p : Params) (A : State → State → Prop) (as : List Arg) (s₀ s₁ : State) : Prop :=
  ∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem ∧ ArgsAre s₀ s₁ as

/-- The callee's entry state. -/
abbrev ent (n : Nat) (s : State) : State := (pushed (argPush n) s).callEntry

theorem ctx_fit {p : Params} {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {N : Nat} (hN : N ≤ 80) :
    N ≤ (s.gpr .esp).toNat := ctx_E hp h (N := N) (by show N + 16 ≤ 96; omega)

theorem E1_big {p : Params} {s₀ : State} (hp : TPre (Y p) s₀) : 80 ≤ (E1 s₀).toNat := by
  rw [E1_nat s₀ hp.E0_big]; have := hp.sp; simp only [Y, STK] at this; omega

theorem ent_arg {p : Params} {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {as : List Arg}
    (hn : as.length ≤ 5) (ha : ArgsAre s₀ s as) {i : Nat} (hi : i < as.length) :
    arg (ent as.length s) i = argV s₀ (as.getD i (.imm 0)) := by
  rw [argPush_arg hn (ctx_fit hp h (by omega)) hi]; exact ha i hi

theorem ent_esp {p : Params} {s₀ s : State} (h : Ctx (Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    (ent n s).gpr .esp = E1 s₀ - BitVec.ofNat 32 (4 * n + 4) := by
  rw [callEntry_esp', h.esp, argPush_len hn]

theorem ent_arg0 {p : Params} {s₀ s : State} (h : Ctx (Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    argAddr (ent n s) 0 = (E1 s₀ - BitVec.ofNat 32 (4 * n)).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp, argPush_len hn]

theorem ent_frame {p : Params} {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    Frame [below (E1 s₀) (4 * n + 4)] s.mem (ent n s).mem := by
  have := callEntry_frame (rs := argPush n) (s := s) (by rw [argPush_len hn]; exact ctx_fit hp h (by omega))
    (esp_nmem_argPush n)
  rw [argPush_len hn, h.esp] at this; exact this

/-- A buffer, apart from the callee's arguments, its return address and its stack. -/
theorem ent_rgn {p : Params} {s₀ : State} (hp : TPre (Y p) s₀) {b : Buf} (hb : (Y p).ok b = true) {n K : Nat}
    (hK : 4 * n + 4 + K ≤ 80) :
    (b.rgn s₀).Disjoint (below (E1 s₀) (4 * n)) ∧
      (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64, 4⟩ : Region).Disjoint (b.rgn s₀) ∧
      (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint (b.rgn s₀) :=
  entry_regions (by have := E1_big hp; omega) (Buf.stkD hp hb (N := 4 * n + 4 + K) (by show _ + 16 ≤ 96; omega))

/-- The callee's regions of the stack, apart from its arguments. -/
theorem ent_self {p : Params} {s₀ : State} (hp : TPre (Y p) s₀) {n K : Nat} (hK : 4 * n + 4 + K ≤ 80) :
    (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64, 4⟩ : Region).Disjoint (below (E1 s₀) (4 * n)) ∧
      (⟨(E1 s₀ - BitVec.ofNat 32 (4 * n + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint
        (below (E1 s₀) (4 * n)) :=
  entry_self (by have := E1_big hp; omega)

/-- The bytes of a buffer, as the callee sees them. -/
theorem ent_bytes {p : Params} {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {n : Nat} (hn : n ≤ 5)
    {b : Buf} (hb : (Y p).ok b = true) :
    ∀ i < b.len, (ent n s).mem (b.addr s₀ + BitVec.ofNat 64 i) = s.mem (b.addr s₀ + BitVec.ofNat 64 i) :=
  fun _ hi => (ent_frame hp h hn).bytes (R := b.rgn s₀)
    (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (Buf.stkD hp hb (N := 4 * n + 4) (by show _ + 16 ≤ 96; omega)).symm)
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi

/-- The callee's argument area is the frame of its arguments, below `esp`. -/
theorem ent_argArea {p : Params} {s₀ s : State} (h : Ctx (Y p) s₀ s) {n : Nat} (hn : n ≤ 5) :
    (⟨argAddr (ent n s) 0, 4 * n⟩ : Region) = below (E1 s₀) (4 * n) := by
  rw [ent_arg0 h hn]

/-- The regions a call writes, and the stack its frame and calls use, within `W`. -/
theorem stk_W {p : Params} {s₀ : State} (hp : TPre (Y p) s₀) {N : Nat} (hN : N ≤ 80) :
    ∃ r' ∈ W (Y p) s₀, Region.Sub (below (E1 s₀) N) r' :=
  ⟨cR (Y p) s₀, TPre.cW, stk_sub hp hN (by show 80 + 16 ≤ 96; omega)⟩

/-! ## Calls -/

section
variable {p : Params} {A B : State → State → Prop} {k : Contract isa} {name : String} {c : Prog isa}

/-- A call of verified code in a frame of the arguments `as`, after their moves. -/
theorem callP_piece (as : List Arg) (n : Nat) (hn' : as.length = n) (hv : Verified X86.target c k) (ok : COk c)
    (hn0 : 0 < n) (hn : n ≤ 5) (hok : ∀ a ∈ as, argOk (Y p) a = true) (rd wr : State → List Region)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hk : ∀ s₀ s₁, TPre (Y p) s₀ → After p A as s₀ s₁ → CallPre k (argPush n) (rd s₀) (wr s₀) s₁)
    (hpub : ∀ s₀ s₀' s₁ s₁', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → After p A as s₀ s₁ →
      After p A as s₀' s₁' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
        k.pub (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀))
          (((pushed (argPush n) s₁').callEntry).withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, TPre (Y p) s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ W (Y p) s₀, Region.Sub r r')
    (hQ : ∀ s₀ s₁ s', TPre (Y p) s₀ → After p A as s₀ s₁ → Ctx (Y p) s₀ s' →
      Frame (wr s₀ ++ [below (E1 s₀) (4 * n + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    SP p A B (callP name c as) := by
  subst hn'
  have hl := argPush_len hn
  refine Piece.seq (setup_piece' as hn hok hA) ?_
  refine Piece.callWith hv.1 hv.2.1 ok.nosp (argPush_ne hn0) (esp_nmem_argPush _) rd wr
    (fun s₀ s₁ hp ⟨_, _, h, _⟩ => by rw [hl]; have := ok.stk; exact ctx_fit hp h (by omega))
    (fun s₀ s₁ hp ha => hk s₀ s₁ hp ha)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s₁ s₁' hp hp' hq ha ha'
      obtain ⟨_, _, h, _⟩ := ha
      obtain ⟨_, _, h', _⟩ := ha'
      exact ⟨e₁, e₂, by rw [h.esp, h'.esp, hq.t.E1], e₃⟩)
    (fun s₀ s₁ s' hp ha e₁ e₂ e₃ fr post => ?_)
  have h := ha.choose_spec.2.1
  rw [h.esp, hl] at fr
  refine hQ s₀ s₁ s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) fr post
  rcases List.mem_append.mp hr with hr | hr
  · exact hW s₀ hp r hr
  · rw [List.mem_singleton] at hr; subst hr; have := ok.stk; exact stk_W hp (by omega)

/-- `callP_piece`, for a call that returns a value in `eax`. -/
theorem callPR_piece (as : List Arg) (n : Nat) (hn' : as.length = n) (hv : Verified X86.target c k) (ok : COk c)
    (hn0 : 0 < n) (hn : n ≤ 5) (hok : ∀ a ∈ as, argOk (Y p) a = true) (rd wr : State → List Region)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hk : ∀ s₀ s₁, TPre (Y p) s₀ → After p A as s₀ s₁ → CallPre k (argPush n) (rd s₀) (wr s₀) s₁)
    (hpub : ∀ s₀ s₀' s₁ s₁', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → After p A as s₀ s₁ →
      After p A as s₀' s₁' → rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
        k.pub (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀))
          (((pushed (argPush n) s₁').callEntry).withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, TPre (Y p) s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ W (Y p) s₀, Region.Sub r r')
    (hQ : ∀ s₀ s₁ s', TPre (Y p) s₀ → After p A as s₀ s₁ → Ctx (Y p) s₀ s' →
      Frame (wr s₀ ++ [below (E1 s₀) (4 * n + stackUse c + 4)]) s₁.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post (((pushed (argPush n) s₁).callEntry).withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    SP p A B (callPR name c as) := by
  subst hn'
  have hl := argPush_len hn
  refine Piece.seq (setup_piece' as hn hok hA) ?_
  refine Piece.callRet hv.1 hv.2.1 ok.nosp (argPush_ne hn0) (esp_nmem_argPush _) rd wr
    (fun s₀ s₁ hp ⟨_, _, h, _⟩ => by rw [hl]; have := ok.stk; exact ctx_fit hp h (by omega))
    (fun s₀ s₁ hp ha => hk s₀ s₁ hp ha)
    (fun s₀ s₀' s₁ s₁' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s₁ s₁' hp hp' hq ha ha'
      obtain ⟨_, _, h, _⟩ := ha
      obtain ⟨_, _, h', _⟩ := ha'
      exact ⟨e₁, e₂, by rw [h.esp, h'.esp, hq.t.E1], e₃⟩)
    (fun s₀ s₁ s' hp ha e₁ e₂ e₃ fr post => ?_)
  have h := ha.choose_spec.2.1
  rw [h.esp, hl] at fr
  refine hQ s₀ s₁ s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) fr post
  rcases List.mem_append.mp hr with hr | hr
  · exact hW s₀ hp r hr
  · rw [List.mem_singleton] at hr; subst hr; have := ok.stk; exact stk_W hp (by omega)

end

end VG.Proof.MlDsa.X86.Sign
