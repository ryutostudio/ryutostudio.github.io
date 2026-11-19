/-
  Proof of a World (『世界の証明』, Ryuto Sako) —
  machine check of the formal model, Rev. 5 (19 November 2026)

  What this file does
  1. It writes down the symbols, the definitions D1–D5 and the axioms
     A1, A2, A4–A8 of the formal model (Rev. 5) as a Lean structure
     `ProofOfAWorld`.
  2. It proves Lemma L1 and Theorems T1–T8 with their corollaries for EVERY
     structure that satisfies those definitions and axioms (derivability).
     The proofs follow the steps of Section IV of the formal model.
  3. It builds the model ℳ of Section VI (three beings s, t, w; one
     coordinate k) and proves that it satisfies all 19 formulas
     (consistency). It also shows that the definitions and axioms do not
     force all beings to be numerically one (non-triviality).
  4. At the end, `#print axioms` reports what each result relies on.

  How to read the result
  * No red error and no warning anywhere → every proof was accepted.
  * "does not depend on any axioms" → the result follows from the
    definitions and axioms of the formal model by logic alone; nothing
    else was assumed.
  * One result, `T6_cor_text_route` (the route of the text, which uses
    double-negation elimination), relies on classical logic; Lean then
    lists its three standard axioms `propext`, `Classical.choice`,
    `Quot.sound`. This is expected.
  * If any line lists any other axiom, that proof did not pass.

  Notes on the encoding
  * Sorts: `Ent` (beings) and `Crd` (coordinates) are two separate types.
  * The sentential operators 𝐒, F, Truth are functions `Prop → Prop`
    (`Sop`, `F`, `Truth`).
  * The schemas A1, A2, A8 and D5a are written as single statements about
    all propositions, which is slightly stronger than a schema. The proofs
    use only instances that can be written in the language ℒ
    (B(a), AbsoluteNothing(a), x = x), and the model ℳ satisfies even the
    stronger form, so both conclusions hold for the schemas as well.
  * A3 is a meta-theoretic restriction, not a formula of ℒ, so it is not
    written here.
  * `Ext` stands for Ext_原理的 (being in the fundamental exterior of
    sō-omou).
  * Defined symbols are kept as symbols together with their defining
    biconditionals, as in Section VI, where the 19 formulas are checked.

  Lean 4, core library only (no Mathlib).
  Formal model: https://ryutostudio.github.io/logic-en.html (Rev. 5)
  Book: https://doi.org/10.5281/zenodo.23607369
  This Lean file was written by Claude (Anthropic) at the author's request.
  Its correctness does not rest on trust in the writer: Lean checks it.
-/

set_option autoImplicit false

/-- The symbols of the formal language ℒ, with the definitions D1–D5 and
the axioms A1, A2, A4–A8 of Rev. 5. -/
structure ProofOfAWorld where
  -- Sorts (types)
  Ent : Type                   -- beings (entities)
  Crd : Type                   -- coordinates (locations)
  -- Constants and function
  S_ind : Ent                  -- an individual's personal sō-omou
  World : Ent                  -- the world as a whole
  c0 : Crd                     -- the single fundamental coordinate
  Loc : Ent → Crd              -- the coordinate at which a being is located
  -- Sentential operators
  Sop : Prop → Prop            -- 𝐒(φ): φ is established as sō-omou
  F : Prop → Prop              -- F(φ): φ is a convenience within sō-omou
  Truth : Prop → Prop          -- Truth(φ): φ appears as truth
  -- One-place predicates on beings
  S : Ent → Prop               -- x is sō-omou
  B : Ent → Prop               -- x exists (is real)
  PE : Ent → Prop              -- x is a fundamental being
  Concept : Ent → Prop         -- x is a concept
  M : Ent → Prop               -- x is meaning
  Ext : Ent → Prop             -- Ext_原理的: x is in the fundamental exterior
  Gen : Ent → Prop             -- unilateral generation
  Begin : Ent → Prop
  End : Ent → Prop
  AlreadyPresent : Ent → Prop
  AbsoluteNothing : Ent → Prop
  Limited : Ent → Prop
  -- Two-place predicates
  P : Ent → Ent → Prop         -- x pictures y
  CoPresent : Ent → Ent → Prop
  Same : Ent → Ent → Prop      -- fundamentally the same being
  C : Crd → Crd → Prop         -- continuity
  Before : Crd → Crd → Prop    -- chronological precedence
  -- Definitions D1–D5
  D1  : ∀ x : Ent, S x ↔ Sop (B x)
  D2a : ∀ x : Ent, Ext x ↔ ¬ Sop (B x)
  D2b : ∀ x : Ent, Gen x ↔ ∃ a : Ent, P a x ∧ ¬ P x a
  D2c : ∀ x : Ent, Begin x ↔ ∃ c : Crd, Before c (Loc x)
  D2d : ∀ x : Ent, End x ↔ ∃ c : Crd, Before (Loc x) c
  D2e : ∀ x : Ent, AbsoluteNothing x ↔ ¬ B x
  D3  : ∀ x : Ent, PE x ↔ (S x ∧ ∀ y : Ent, (P x y ↔ P y x))
  D4a : ∀ x y : Ent, CoPresent x y ↔ (Loc x = c0 ∧ Loc y = c0)
  D4b : ∀ x : Ent, AlreadyPresent x ↔ (Loc x = c0 ∧ PE x ∧ ¬ Gen x)
  D4c : ∀ x y : Ent, Same x y ↔ (PE x ∧ PE y ∧ Loc x = Loc y)
  D5a : ∀ φ : Prop, Truth φ ↔ Sop φ
  D5b : ∀ x : Ent, M x ↔ B x
  -- Axioms A1, A2, A4–A8 (A3 is a meta-theoretic restriction)
  A1 : ∀ φ : Prop, φ → Sop φ
  A2 : ∀ φ : Prop, F φ → Sop φ
  A4 : ∀ x y : Ent, P x y ↔ P y x
  A5 : (∀ c : Crd, c = c0) ∧ (∀ c c' : Crd, Before c c' → c ≠ c') ∧ C c0 c0
  A6 : (∀ y : Ent, CoPresent S_ind y) → Limited S_ind
  A7 : ∀ x : Ent, S x → B x
  A8 : ∀ (φ : Ent → Prop) (x : Ent), Sop (φ x) → S x

namespace ProofOfAWorld

variable (W : ProofOfAWorld)

/-! ## Lemma L1 and Theorems T1–T8 (Section IV) -/

/-- L1. ∀x (Loc(x) = c0). Basis: A5 (first conjunct). -/
theorem L1 : ∀ x : W.Ent, W.Loc x = W.c0 :=
  fun x => W.A5.1 (W.Loc x)

/-- T1. ¬∃x (B(x) ∧ Ext(x)). Basis: A1, D2a. -/
theorem T1 : ¬ ∃ x : W.Ent, W.B x ∧ W.Ext x :=
  fun ⟨a, hB, hExt⟩ =>
    -- Step 4: A1 with φ := B(a) gives 𝐒(B(a))
    have h4 : W.Sop (W.B a) := W.A1 (W.B a) hB
    -- Step 5: D2a gives ¬𝐒(B(a))
    have h5 : ¬ W.Sop (W.B a) := (W.D2a a).mp hExt
    -- Step 6: contradiction
    h5 h4

/-- T2. ∀x (B(x) ↔ S(x)). Basis: A1, D1, A7. -/
theorem T2 : ∀ x : W.Ent, W.B x ↔ W.S x :=
  fun x =>
    ⟨fun hB => (W.D1 x).mpr (W.A1 (W.B x) hB),  -- Steps 1–3
     fun hS => W.A7 x hS⟩                        -- Step 4

/-- T3. ∀x (B(x) ↔ PE(x)). Basis: A4, D3, T2. -/
theorem T3 : ∀ x : W.Ent, W.B x ↔ W.PE x :=
  fun x =>
    -- Step 1: A4 gives ∀y (P(x, y) ↔ P(y, x))
    have h1 : ∀ y : W.Ent, (W.P x y ↔ W.P y x) := fun y => W.A4 x y
    -- Step 2: with D3, S(x) ↔ PE(x)
    have h2 : W.S x ↔ W.PE x :=
      ⟨fun hS => (W.D3 x).mpr ⟨hS, h1⟩, fun hPE => ((W.D3 x).mp hPE).1⟩
    -- Step 3: T2 and transitivity
    (W.T2 x).trans h2

/-- Corollary of T3: Limited(S_ind). Basis: L1, D4a, A6. -/
theorem T3_cor : W.Limited W.S_ind :=
  W.A6 (fun y => (W.D4a W.S_ind y).mpr ⟨W.L1 W.S_ind, W.L1 y⟩)

/-- T4. ∀x ¬Gen(x). Basis: A4, D2b. -/
theorem T4 : ∀ x : W.Ent, ¬ W.Gen x :=
  fun x =>
    -- Steps 1–3: by A4, there is no a with P(a, x) ∧ ¬P(x, a)
    have h3 : ¬ ∃ a : W.Ent, W.P a x ∧ ¬ W.P x a :=
      fun ⟨a, hPax, hnPxa⟩ => hnPxa ((W.A4 a x).mp hPax)
    -- Step 4: contrapositive of D2b
    fun hGen => h3 ((W.D2b x).mp hGen)

/-- T5. ∀x (¬Begin(x) ∧ ¬End(x)). Basis: A5, L1, D2c, D2d. -/
theorem T5 : ∀ x : W.Ent, ¬ W.Begin x ∧ ¬ W.End x := by
  intro x
  constructor
  · intro hBegin
    -- Step 2: by D2c, Before(c1, Loc(x)) for some coordinate c1
    match (W.D2c x).mp hBegin with
    | ⟨c1, hBefore⟩ =>
      -- Step 3: c1 = c0 (A5, first conjunct) and Loc(x) = c0 (L1),
      -- so Before(c0, c0)
      rw [W.A5.1 c1, W.L1 x] at hBefore
      -- Step 4: A5 (second conjunct) gives c0 ≠ c0, against c0 = c0
      exact W.A5.2.1 W.c0 W.c0 hBefore rfl
  · intro hEnd
    -- Step 5: the same argument with D2d
    match (W.D2d x).mp hEnd with
    | ⟨c2, hBefore⟩ =>
      rw [W.A5.1 c2, W.L1 x] at hBefore
      exact W.A5.2.1 W.c0 W.c0 hBefore rfl

/-- Corollary of T5: ¬Begin(World) ∧ ¬End(World). -/
theorem T5_cor : ¬ W.Begin W.World ∧ ¬ W.End W.World :=
  W.T5 W.World

/-- T6. ¬∃x AbsoluteNothing(x). Basis: A1, A8, A7, D2e. -/
theorem T6 : ¬ ∃ x : W.Ent, W.AbsoluteNothing x :=
  fun ⟨a, hAN⟩ =>
    -- Step 2: A1 with φ := AbsoluteNothing(a)
    have h2 : W.Sop (W.AbsoluteNothing a) := W.A1 (W.AbsoluteNothing a) hAN
    -- Step 3: A8 with φ(x) := AbsoluteNothing(x)
    have h3 : W.S a := W.A8 W.AbsoluteNothing a h2
    -- Step 4: A7
    have h4 : W.B a := W.A7 a h3
    -- Steps 5–6: D2e gives ¬B(a); contradiction
    (W.D2e a).mp hAN h4

/-- Corollary of T6: ∀x B(x), by the route of the text (Step 8):
T6, the contrapositive of D2e, and double-negation elimination
(classical logic). -/
theorem T6_cor_text_route : ∀ x : W.Ent, W.B x :=
  fun x => Classical.byContradiction (fun hnB => W.T6 ⟨x, (W.D2e x).mpr hnB⟩)

/-- Corollary of T6: ∀x B(x), by the route noted under A8: x = x holds;
by A1 it holds as sō-omou; by A8 x is sō-omou; by A7 x is real.
This route needs no classical logic. It is the one used below. -/
theorem T6_cor : ∀ x : W.Ent, W.B x :=
  fun x =>
    have h1 : W.Sop (x = x) := W.A1 (x = x) rfl
    have h2 : W.S x := W.A8 (fun y => y = y) x h1
    W.A7 x h2

/-- T7. ∀x (Concept(x) → AlreadyPresent(x)).
Basis: corollary of T6, T3, L1, T4, D4b. -/
theorem T7 : ∀ x : W.Ent, W.Concept x → W.AlreadyPresent x :=
  fun x _ => (W.D4b x).mpr ⟨W.L1 x, (W.T3 x).mp (W.T6_cor x), W.T4 x⟩

/-- Corollary of T7: ∀x AlreadyPresent(x)
(Steps 2–7 do not use the assumption Concept(x)). -/
theorem T7_cor : ∀ x : W.Ent, W.AlreadyPresent x :=
  fun x => (W.D4b x).mpr ⟨W.L1 x, (W.T3 x).mp (W.T6_cor x), W.T4 x⟩

/-- T8. ∀x ((S(x) ↔ B(x)) ∧ (B(x) ↔ PE(x)) ∧ (PE(x) ↔ M(x))).
Basis: T2, T3, D5b. -/
theorem T8 : ∀ x : W.Ent, (W.S x ↔ W.B x) ∧ (W.B x ↔ W.PE x) ∧ (W.PE x ↔ W.M x) :=
  fun x => ⟨(W.T2 x).symm, W.T3 x, (W.T3 x).symm.trans (W.D5b x).symm⟩

/-- Corollary 1 of T8: ∀x (S(x) ∧ B(x) ∧ PE(x) ∧ M(x)). -/
theorem T8_cor1 : ∀ x : W.Ent, W.S x ∧ W.B x ∧ W.PE x ∧ W.M x :=
  fun x =>
    have hB : W.B x := W.T6_cor x
    ⟨(W.T2 x).mp hB, hB, (W.T3 x).mp hB, (W.D5b x).mpr hB⟩

/-- Corollary 2 of T8: ∀x∀y Same(x, y)
(fundamental identity, not numerical identity). -/
theorem T8_cor2 : ∀ x y : W.Ent, W.Same x y :=
  fun x y => (W.D4c x y).mpr ⟨(W.T8_cor1 x).2.2.1, (W.T8_cor1 y).2.2.1, (W.L1 x).trans (W.L1 y).symm⟩

end ProofOfAWorld

/-! ## The model ℳ of Section VI (consistency) -/

/-- The three beings of ℳ: s (an individual's personal sō-omou),
t (another individual), w (the world as a whole). -/
inductive Being where
  | s
  | t
  | w

/-- The model ℳ: beings {s, t, w}; one coordinate k (here `()`);
𝐒, F, Truth interpreted as the identity on truth values. -/
def modelM : ProofOfAWorld where
  Ent := Being
  Crd := Unit
  S_ind := Being.s
  World := Being.w
  c0 := ()
  Loc := fun _ => ()
  Sop := fun φ => φ
  F := fun φ => φ
  Truth := fun φ => φ
  S := fun _ => True
  B := fun _ => True
  PE := fun _ => True
  Concept := fun _ => True
  M := fun _ => True
  Ext := fun _ => False
  Gen := fun _ => False
  Begin := fun _ => False
  End := fun _ => False
  AlreadyPresent := fun _ => True
  AbsoluteNothing := fun _ => False
  Limited := fun x => x = Being.s ∨ x = Being.t
  P := fun _ _ => True
  CoPresent := fun _ _ => True
  Same := fun _ _ => True
  C := fun _ _ => True
  Before := fun _ _ => False
  -- The 19 formulas hold in ℳ:
  D1  := fun _ => Iff.rfl
  D2a := fun _ => ⟨fun h => False.elim h, fun h => False.elim (h trivial)⟩
  D2b := fun _ => ⟨fun h => False.elim h, fun ⟨_, _, h⟩ => False.elim (h trivial)⟩
  D2c := fun _ => ⟨fun h => False.elim h, fun ⟨_, h⟩ => False.elim h⟩
  D2d := fun _ => ⟨fun h => False.elim h, fun ⟨_, h⟩ => False.elim h⟩
  D2e := fun _ => ⟨fun h => False.elim h, fun h => False.elim (h trivial)⟩
  D3  := fun _ => ⟨fun _ => ⟨trivial, fun _ => Iff.rfl⟩, fun _ => trivial⟩
  D4a := fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => trivial⟩
  D4b := fun _ => ⟨fun _ => ⟨rfl, trivial, fun h => h⟩, fun _ => trivial⟩
  D4c := fun _ _ => ⟨fun _ => ⟨trivial, trivial, rfl⟩, fun _ => trivial⟩
  D5a := fun _ => Iff.rfl
  D5b := fun _ => Iff.rfl
  A1 := fun _ h => h
  A2 := fun _ h => h
  A4 := fun _ _ => Iff.rfl
  A5 := ⟨(fun c => match c with | () => rfl), (fun _ _ h => False.elim h), trivial⟩
  A6 := fun _ => Or.inl rfl
  A7 := fun _ _ => trivial
  A8 := fun _ _ _ => trivial

/-- Consistency: the definitions and axioms do not imply a contradiction,
because the model ℳ satisfies all of them. -/
theorem consistency : ¬ (ProofOfAWorld → False) :=
  fun h => h modelM

/-- In ℳ, the individual s and the world w are numerically distinct... -/
theorem modelM_distinct : modelM.S_ind ≠ modelM.World := by
  show Being.s ≠ Being.w
  intro h
  cases h

/-- ...and yet fundamentally the same being (T8, Corollary 2). -/
theorem modelM_distinct_but_same :
    modelM.S_ind ≠ modelM.World ∧ modelM.Same modelM.S_ind modelM.World :=
  ⟨modelM_distinct, modelM.T8_cor2 _ _⟩

/-- Non-triviality: the definitions and axioms do not force all beings to be
numerically one (Rev. 4, whose A5 did, is corrected in Rev. 5). Shown by ℳ,
where the individual s and the world w are distinct. -/
theorem not_all_one : ¬ (∀ W : ProofOfAWorld, ∀ x y : W.Ent, x = y) :=
  fun h => modelM_distinct (h modelM modelM.S_ind modelM.World)

/-! ## The result: what each statement relies on

Each line below should print
  'NAME' does not depend on any axioms
except `T6_cor_text_route`, which prints (the order may differ)
  'ProofOfAWorld.T6_cor_text_route' depends on axioms: [propext, Classical.choice, Quot.sound]
If any line lists any other axiom, that proof did not pass. -/

#print axioms ProofOfAWorld.L1
#print axioms ProofOfAWorld.T1
#print axioms ProofOfAWorld.T2
#print axioms ProofOfAWorld.T3
#print axioms ProofOfAWorld.T3_cor
#print axioms ProofOfAWorld.T4
#print axioms ProofOfAWorld.T5
#print axioms ProofOfAWorld.T5_cor
#print axioms ProofOfAWorld.T6
#print axioms ProofOfAWorld.T6_cor_text_route
#print axioms ProofOfAWorld.T6_cor
#print axioms ProofOfAWorld.T7
#print axioms ProofOfAWorld.T7_cor
#print axioms ProofOfAWorld.T8
#print axioms ProofOfAWorld.T8_cor1
#print axioms ProofOfAWorld.T8_cor2
#print axioms consistency
#print axioms modelM_distinct_but_same
#print axioms not_all_one
